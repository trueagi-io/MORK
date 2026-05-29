//! Cranelift JIT backend for Einstein summation, dense and CSR-sparse.
//!
//! This is the native-code counterpart to the interpreted [`crate::einsum`]
//! VM. A spec like `"ab,bc->ac"` plus concrete inputs is compiled — once —
//! into a machine-code loop nest that reads and writes the tensors' backing
//! storage directly (no per-element trait dispatch). The compiled
//! [`DenseF32Jit`] is then reused across many executions of the same spec and
//! shapes.
//!
//! # Inputs and outputs
//!
//! Inputs may be dense ([`Dense<f32>`]) or compressed-sparse-row
//! ([`Csr<u32, f32>`]), mixed freely, passed as [`JitInput`]. Outputs are
//! always [`Dense<f32>`] (CSR is immutable after construction, so it can't be
//! written into).
//!
//! # Design
//!
//! - **Direct memory.** The codegen emits native loads/stores against the raw
//!   data pointers. Dense tensors get random-access addressing with row-major
//!   strides baked in as constants ([`DenseLayout`]); CSR inputs are walked
//!   with native **sparse row iteration** — for a fixed row, the inner loop
//!   visits only that row's stored non-zeros (over `row_ptr`/`col_idx`/
//!   `values`), exactly like the VM's sparse loop, so structural zeros are
//!   skipped at native speed.
//! - **Shape-specialized.** Dimensions are baked in as constants, so a given
//!   [`DenseF32Jit`] is valid only for the exact shapes (and per-input
//!   dense/sparse kinds) it was compiled for; [`run`](DenseF32Jit::run)
//!   asserts this.
//! - **Layout seam.** [`Layout`] abstracts random-access element addressing.
//!   `DenseLayout` is the only implementor (CSR has no constant-time random
//!   address, so it participates through sparse iteration instead).
//!
//! The call boundary is type-erased to arrays of raw pointers, so the
//! Rust-side call is a single monomorphic `extern "C"` invocation regardless
//! of arity or per-input layout. A dense input contributes one pointer
//! (its `f32` data); a CSR input contributes three (`row_ptr`, `col_idx`,
//! `values`):
//!
//! ```text
//! extern "C" fn(ins: *const *const u8, outs: *const *mut u8)
//! ```
//!
//! # Coverage limits
//!
//! A CSR input is only handled when its row axis can be fixed by an outer
//! loop before its column axis is needed — true for the common cases
//! (CSR × Dense, CSR × CSR chains). Patterns where a sparse input's column
//! index is otherwise constrained (e.g. `"ab,cb->ac"` with both operands
//! sparse, or a sparse trace `"aa->"`) are rejected at compile time with
//! [`JitError::Unsupported`]; use the [`crate::einsum`] VM for those.
//!
//! # Output convention
//!
//! Outputs are **accumulated into** and must be zeroed by the caller before
//! [`run`](DenseF32Jit::run) (same convention as [`crate::einsum`]). For an
//! all-dense single output the contraction sum is held in a register and
//! stored once per free-index tuple; otherwise outputs are read-modify-write.
//!
//! # Example
//!
//! ```
//! use linalg::jit::{DenseF32Jit, JitInput};
//! use linalg::dense::Dense;
//! use linalg::tensor::NDIndex;
//!
//! let mut a = Dense::<f32>::zeros(vec![2, 3]);
//! a.fill_from(&[1., 2., 3., 4., 5., 6.]);
//! let mut b = Dense::<f32>::zeros(vec![3, 2]);
//! b.fill_from(&[7., 8., 9., 10., 11., 12.]);
//! let mut c = Dense::<f32>::zeros(vec![2, 2]);
//!
//! let jit = DenseF32Jit::compile(
//!     "ab,bc->ac",
//!     &[JitInput::Dense(&a), JitInput::Dense(&b)],
//!     &[vec![2, 2]],
//! ).unwrap();
//! jit.run(&[JitInput::Dense(&a), JitInput::Dense(&b)], &mut [&mut c]);
//!
//! assert_eq!(c.get(&[0, 0]), 58.0);
//! assert_eq!(c.get(&[1, 1]), 154.0);
//! ```

use std::fmt;
use std::mem;

use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::{types, AbiParam, Block, InstBuilder, MemFlags, Type, Value};
use cranelift_codegen::settings::{self, Configurable};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Variable};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{Linkage, Module};

use crate::csr::Csr;
use crate::dense::Dense;
use crate::einsum::{parse_spec, InvalidSpec};

// ─────────────────────────────────────────────────────────────────────────
// Errors
// ─────────────────────────────────────────────────────────────────────────

/// Failure compiling an einsum spec for the JIT backend.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum JitError {
    /// The spec itself is malformed or inconsistent with the shapes.
    Spec(InvalidSpec),
    /// The spec is valid but this backend cannot generate code for it
    /// (see the module-level "Coverage limits"). The string explains why.
    Unsupported(&'static str),
}

impl From<InvalidSpec> for JitError {
    fn from(e: InvalidSpec) -> Self {
        JitError::Spec(e)
    }
}

impl fmt::Display for JitError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            JitError::Spec(e) => write!(f, "{e}"),
            JitError::Unsupported(why) => write!(f, "unsupported by JIT backend: {why}"),
        }
    }
}

impl std::error::Error for JitError {}

// ─────────────────────────────────────────────────────────────────────────
// Public input handle
// ─────────────────────────────────────────────────────────────────────────

/// A tensor passed to the JIT, dense or CSR-sparse.
#[derive(Clone, Copy)]
pub enum JitInput<'a> {
    Dense(&'a Dense<f32>),
    Csr(&'a Csr<u32, f32>),
}

impl JitInput<'_> {
    fn is_csr(&self) -> bool {
        matches!(self, JitInput::Csr(_))
    }

    /// Logical einsum shape (CSR is an `n × n` matrix).
    fn shape(&self) -> Vec<usize> {
        match self {
            JitInput::Dense(d) => d.shape.clone(),
            JitInput::Csr(c) => vec![c.n as usize, c.n as usize],
        }
    }

    /// Append this input's backing pointers in codegen slot order.
    fn push_ptrs(&self, out: &mut Vec<*const u8>) {
        match self {
            JitInput::Dense(d) => out.push(d.data.as_ptr() as *const u8),
            JitInput::Csr(c) => {
                out.push(c.row_ptr.as_ptr() as *const u8);
                out.push(c.col_idx.as_ptr() as *const u8);
                out.push(c.values.as_ptr() as *const u8);
            }
        }
    }
}

/// What this program was compiled to expect for one input.
#[derive(Clone, PartialEq, Eq)]
struct InputSpec {
    is_csr: bool,
    shape: Vec<usize>,
}

// ─────────────────────────────────────────────────────────────────────────
// Layout seam (dense random-access addressing)
// ─────────────────────────────────────────────────────────────────────────

/// How to compute the byte address of a randomly-indexed element of a tensor
/// struct. CSR has no constant-time random address, so it does not implement
/// this — it participates through sparse row iteration instead.
trait Layout {
    fn emit_elem_addr(
        &self,
        b: &mut FunctionBuilder,
        ptr_ty: Type,
        base: Value,
        indices: &[Value],
    ) -> Value;
}

/// Row-major dense layout with strides baked in as constants.
struct DenseLayout {
    /// Element stride per axis (in elements, not bytes).
    strides: Vec<i64>,
}

impl DenseLayout {
    fn new(axis_dims: &[usize]) -> Self {
        let n = axis_dims.len();
        let mut strides = vec![1i64; n];
        for j in (0..n.saturating_sub(1)).rev() {
            strides[j] = strides[j + 1] * axis_dims[j + 1] as i64;
        }
        Self { strides }
    }
}

impl Layout for DenseLayout {
    fn emit_elem_addr(
        &self,
        b: &mut FunctionBuilder,
        ptr_ty: Type,
        base: Value,
        indices: &[Value],
    ) -> Value {
        let mut off = b.ins().iconst(ptr_ty, 0);
        for (j, &idx) in indices.iter().enumerate() {
            let contrib = b.ins().imul_imm(idx, self.strides[j]);
            off = b.ins().iadd(off, contrib);
        }
        // f32 == 4 bytes; offset (elements) << 2 == byte offset.
        let byte_off = b.ins().ishl_imm(off, 2);
        b.ins().iadd(base, byte_off)
    }
}

// ─────────────────────────────────────────────────────────────────────────
// Compiled program
// ─────────────────────────────────────────────────────────────────────────

/// A compiled, shape-specialized einsum producing [`Dense<f32>`] output(s).
///
/// Construct with [`compile`](Self::compile); execute with
/// [`run`](Self::run). Holds the owning [`JITModule`] so the generated code
/// stays mapped for the lifetime of this value.
pub struct DenseF32Jit {
    _module: JITModule,
    func: extern "C" fn(*const *const u8, *const *mut u8),
    inputs: Vec<InputSpec>,
    output_shapes: Vec<Vec<usize>>,
}

impl DenseF32Jit {
    /// Compile `spec` for the given inputs and output shapes.
    ///
    /// Only each input's shape and kind (dense vs CSR) are read here, not its
    /// data — but those are baked in, so the returned program is valid only
    /// for inputs matching exactly. Shapes are outermost-axis-first.
    pub fn compile(
        spec: &str,
        inputs: &[JitInput],
        output_shapes: &[Vec<usize>],
    ) -> Result<Self, JitError> {
        let parsed = parse_spec(spec, inputs.len())?;
        let in_shapes: Vec<Vec<usize>> = inputs.iter().map(|i| i.shape()).collect();
        let is_csr: Vec<bool> = inputs.iter().map(|i| i.is_csr()).collect();

        // Collect and validate per-slot dimensions from input shapes.
        let mut dims = [0usize; 26];
        let mut dim_set = [false; 26];
        for (pi, pattern) in parsed.inputs.iter().enumerate() {
            if in_shapes[pi].len() != pattern.len() {
                return Err(InvalidSpec::InputNdimMismatch {
                    input: pi,
                    array_ndim: in_shapes[pi].len(),
                    spec_ndim: pattern.len(),
                }
                .into());
            }
            for (pos, &s) in pattern.iter().enumerate() {
                let si = s as usize;
                let d = in_shapes[pi][pos];
                if dim_set[si] {
                    if dims[si] != d {
                        return Err(InvalidSpec::DimensionMismatch {
                            index: (s + b'a') as char,
                            expected: dims[si],
                            got: d,
                        }
                        .into());
                    }
                } else {
                    dims[si] = d;
                    dim_set[si] = true;
                }
            }
        }

        // Validate output shapes against the resolved dims.
        if output_shapes.len() != parsed.outputs.len() {
            return Err(InvalidSpec::WrongInputCount {
                expected: parsed.outputs.len(),
                got: output_shapes.len(),
            }
            .into());
        }
        for (oi, pattern) in parsed.outputs.iter().enumerate() {
            if output_shapes[oi].len() != pattern.len() {
                return Err(InvalidSpec::OutputNdimMismatch {
                    array_ndim: output_shapes[oi].len(),
                    spec_ndim: pattern.len(),
                }
                .into());
            }
            for (pos, &s) in pattern.iter().enumerate() {
                if output_shapes[oi][pos] != dims[s as usize] {
                    return Err(InvalidSpec::OutputDimMismatch {
                        axis: pos,
                        expected: dims[s as usize],
                        got: output_shapes[oi][pos],
                    }
                    .into());
                }
            }
        }

        let (module, func) = codegen(&parsed.inputs, &parsed.outputs, &is_csr, &dims)?;

        Ok(Self {
            _module: module,
            func,
            inputs: in_shapes
                .into_iter()
                .zip(is_csr)
                .map(|(shape, is_csr)| InputSpec { is_csr, shape })
                .collect(),
            output_shapes: output_shapes.to_vec(),
        })
    }

    /// Execute against concrete tensors.
    ///
    /// Panics if any input/output count, kind, or shape does not match what
    /// this program was compiled for. Outputs must be pre-zeroed.
    pub fn run(&self, inputs: &[JitInput], outputs: &mut [&mut Dense<f32>]) {
        assert_eq!(
            inputs.len(),
            self.inputs.len(),
            "input count mismatch: got {}, compiled for {}",
            inputs.len(),
            self.inputs.len()
        );
        assert_eq!(
            outputs.len(),
            self.output_shapes.len(),
            "output count mismatch: got {}, compiled for {}",
            outputs.len(),
            self.output_shapes.len()
        );
        for (i, inp) in inputs.iter().enumerate() {
            let spec = &self.inputs[i];
            assert_eq!(
                inp.is_csr(), spec.is_csr,
                "input {i} kind mismatch (dense vs CSR)"
            );
            assert_eq!(
                inp.shape(), spec.shape,
                "input {i} shape mismatch: got {:?}, compiled for {:?}",
                inp.shape(), spec.shape
            );
        }
        for (o, out) in outputs.iter().enumerate() {
            assert_eq!(
                out.shape, self.output_shapes[o],
                "output {o} shape mismatch: got {:?}, compiled for {:?}",
                out.shape, self.output_shapes[o]
            );
        }

        let mut in_ptrs: Vec<*const u8> = Vec::new();
        for inp in inputs {
            inp.push_ptrs(&mut in_ptrs);
        }
        let out_ptrs: Vec<*mut u8> =
            outputs.iter_mut().map(|d| d.data.as_mut_ptr() as *mut u8).collect();
        // SAFETY: the generated code reads exactly the pointer slots that the
        // inputs above produce (kinds asserted to match what was compiled),
        // and addresses only elements within the validated shapes.
        (self.func)(in_ptrs.as_ptr(), out_ptrs.as_ptr());
    }
}

// ─────────────────────────────────────────────────────────────────────────
// Loop scheduling
// ─────────────────────────────────────────────────────────────────────────

/// One loop in the generated nest, outermost-first.
enum LoopOp {
    /// Dense counted loop `for slot in 0..dim`.
    Dense { slot: u8 },
    /// Iterate the stored non-zeros of `inputs[input_idx]`'s row
    /// `vals[row_slot]`, binding `col_slot` to each column index.
    Sparse { input_idx: usize, row_slot: u8, col_slot: u8 },
}

/// Greedy schedule mirroring the VM: prefer a sparse row loop whose row axis
/// is already fixed; otherwise add a dense loop, favouring a sparse input's
/// row axis so it can be unlocked next.
fn schedule(
    inputs: &[Vec<u8>],
    outputs: &[Vec<u8>],
    sparse_axes: &[Option<(u8, u8)>],
) -> Vec<LoopOp> {
    let mut all_slots = Vec::new();
    let mut seen = [false; 26];
    for pat in inputs.iter().chain(outputs.iter()) {
        for &s in pat {
            if !seen[s as usize] {
                seen[s as usize] = true;
                all_slots.push(s);
            }
        }
    }

    let mut fixed = [false; 26];
    let mut n_fixed = 0;
    let mut plan = Vec::new();

    while n_fixed < all_slots.len() {
        // Try to emit a sparse row loop whose row axis is fixed.
        let mut found = false;
        'scan: for &s in &all_slots {
            if fixed[s as usize] {
                continue;
            }
            for (idx, axes) in sparse_axes.iter().enumerate() {
                if let Some((r, c)) = *axes {
                    if c == s && r != c && fixed[r as usize] {
                        plan.push(LoopOp::Sparse { input_idx: idx, row_slot: r, col_slot: c });
                        fixed[s as usize] = true;
                        n_fixed += 1;
                        found = true;
                        break 'scan;
                    }
                }
            }
        }
        if found {
            continue;
        }

        // Otherwise a dense loop; prefer a sparse input's row axis.
        let mut pick = None;
        for &s in &all_slots {
            if fixed[s as usize] {
                continue;
            }
            let is_row = sparse_axes
                .iter()
                .any(|a| matches!(a, Some((r, _)) if *r == s));
            if is_row {
                pick = Some(s);
                break;
            }
            if pick.is_none() {
                pick = Some(s);
            }
        }
        let s = pick.expect("unfixed slot exists");
        plan.push(LoopOp::Dense { slot: s });
        fixed[s as usize] = true;
        n_fixed += 1;
    }

    plan
}

// ─────────────────────────────────────────────────────────────────────────
// Code generation
// ─────────────────────────────────────────────────────────────────────────

/// Base pointer(s) for one input, as loaded at function entry.
enum InputBase {
    Dense(Value),
    Csr { row_ptr: Value, col_idx: Value, values: Value },
}

/// Open a dense counted loop `for v in 0..dim`. Returns `(header, exit)`;
/// afterwards the builder sits in the (sealed) loop body.
fn open_dense_loop(b: &mut FunctionBuilder, ptr_ty: Type, v: Variable, dim: usize) -> (Block, Block) {
    let zero = b.ins().iconst(ptr_ty, 0);
    b.def_var(v, zero);
    let header = b.create_block();
    let body = b.create_block();
    let exit = b.create_block();
    b.ins().jump(header, &[]);
    b.switch_to_block(header);
    let idx = b.use_var(v);
    let cond = b.ins().icmp_imm(IntCC::UnsignedLessThan, idx, dim as i64);
    b.ins().brif(cond, body, &[], exit, &[]);
    b.switch_to_block(body);
    b.seal_block(body);
    (header, exit)
}

/// Open a sparse row loop over `inputs[..]`'s row `row_var`. Binds `col_var`
/// to each stored column index and `val_var` to each stored value. Returns
/// `(induction_var, header, exit)`; afterwards the builder sits in the
/// (sealed) loop body with `col_var`/`val_var` already defined.
#[allow(clippy::too_many_arguments)]
fn open_sparse_loop(
    b: &mut FunctionBuilder,
    ptr_ty: Type,
    row_var: Variable,
    col_var: Variable,
    val_var: Variable,
    row_ptr_base: Value,
    col_idx_base: Value,
    values_base: Value,
) -> (Variable, Block, Block) {
    // start = row_ptr[row], end = row_ptr[row + 1]  (row_ptr is usize/i64).
    let row = b.use_var(row_var);
    let row_byte = b.ins().ishl_imm(row, 3); // * 8
    let start_addr = b.ins().iadd(row_ptr_base, row_byte);
    let start = b.ins().load(types::I64, MemFlags::trusted(), start_addr, 0);
    let end = b.ins().load(types::I64, MemFlags::trusted(), start_addr, 8);

    let ei = b.declare_var(ptr_ty);
    b.def_var(ei, start);

    let header = b.create_block();
    let body = b.create_block();
    let exit = b.create_block();
    b.ins().jump(header, &[]);
    b.switch_to_block(header);
    let ei_v = b.use_var(ei);
    let cond = b.ins().icmp(IntCC::UnsignedLessThan, ei_v, end);
    b.ins().brif(cond, body, &[], exit, &[]);
    b.switch_to_block(body);
    b.seal_block(body);

    // col = col_idx[ei] (u32 -> index), val = values[ei] (f32).
    let ei_b = b.use_var(ei);
    let off4 = b.ins().ishl_imm(ei_b, 2); // * 4
    let col_addr = b.ins().iadd(col_idx_base, off4);
    let col32 = b.ins().load(types::I32, MemFlags::trusted(), col_addr, 0);
    let col = b.ins().uextend(ptr_ty, col32);
    b.def_var(col_var, col);
    let val_addr = b.ins().iadd(values_base, off4);
    let val = b.ins().load(types::F32, MemFlags::trusted(), val_addr, 0);
    b.def_var(val_var, val);

    (ei, header, exit)
}

/// Close a loop: increment its induction variable, back-edge, seal the header,
/// then position the builder in the (sealed) exit block.
fn close_loop(b: &mut FunctionBuilder, iv: Variable, header: Block, exit: Block) {
    let idx = b.use_var(iv);
    let next = b.ins().iadd_imm(idx, 1);
    b.def_var(iv, next);
    b.ins().jump(header, &[]);
    b.seal_block(header);
    b.switch_to_block(exit);
    b.seal_block(exit);
}

/// Emit the product of all input elements at the current index values. Dense
/// inputs are loaded by computed address; sparse-covered inputs read their
/// cached per-iteration value variable.
fn emit_product(
    b: &mut FunctionBuilder,
    ptr_ty: Type,
    inputs: &[Vec<u8>],
    layouts: &[DenseLayout],
    bases: &[InputBase],
    val_vars: &[Option<Variable>],
    vars: &[Variable; 26],
) -> Value {
    let mut product: Option<Value> = None;
    for (i, pattern) in inputs.iter().enumerate() {
        let v = if let Some(vv) = val_vars[i] {
            b.use_var(vv)
        } else {
            let base = match bases[i] {
                InputBase::Dense(p) => p,
                InputBase::Csr { .. } => unreachable!("CSR input must be sparse-covered"),
            };
            let idx_vals: Vec<Value> =
                pattern.iter().map(|&s| b.use_var(vars[s as usize])).collect();
            let addr = layouts[i].emit_elem_addr(b, ptr_ty, base, &idx_vals);
            b.ins().load(types::F32, MemFlags::trusted(), addr, 0)
        };
        product = Some(match product {
            None => v,
            Some(p) => b.ins().fmul(p, v),
        });
    }
    product.expect("einsum input list is non-empty")
}

/// Build the host ISA and a fresh JIT module.
fn new_module() -> JITModule {
    let mut flags = settings::builder();
    flags.set("opt_level", "speed").unwrap();
    let isa_builder = cranelift_native::builder().expect("host machine is not supported");
    let isa = isa_builder
        .finish(settings::Flags::new(flags))
        .expect("failed to build ISA");
    let builder = JITBuilder::with_isa(isa, cranelift_module::default_libcall_names());
    JITModule::new(builder)
}

/// Generate native code for `inputs -> outputs` with the given per-slot dims.
fn codegen(
    inputs: &[Vec<u8>],
    outputs: &[Vec<u8>],
    is_csr: &[bool],
    dims: &[usize; 26],
) -> Result<(JITModule, extern "C" fn(*const *const u8, *const *mut u8)), JitError> {
    let any_sparse = is_csr.iter().any(|&c| c);

    // Sparse axes per input: Some((row_slot, col_slot)) for CSR (always 2D).
    let sparse_axes: Vec<Option<(u8, u8)>> = inputs
        .iter()
        .zip(is_csr)
        .map(|(pat, &csr)| if csr { Some((pat[0], pat[1])) } else { None })
        .collect();

    // Free (in some output) vs contracted (inputs only) slots, first-appearance.
    let mut in_output = [false; 26];
    for out in outputs {
        for &s in out {
            in_output[s as usize] = true;
        }
    }
    let mut order = Vec::new();
    let mut seen = [false; 26];
    for pat in inputs.iter().chain(outputs.iter()) {
        for &s in pat {
            if !seen[s as usize] {
                seen[s as usize] = true;
                order.push(s);
            }
        }
    }
    let free: Vec<u8> = order.iter().copied().filter(|&s| in_output[s as usize]).collect();
    let contracted: Vec<u8> =
        order.iter().copied().filter(|&s| !in_output[s as usize]).collect();

    // Sparse-aware plan (used whenever any input is sparse, or for multi-output).
    let plan = schedule(inputs, outputs, &sparse_axes);

    // Which inputs are value-sourced from a sparse loop in the plan?
    let mut sparse_covered = vec![false; inputs.len()];
    for op in &plan {
        if let LoopOp::Sparse { input_idx, .. } = op {
            sparse_covered[*input_idx] = true;
        }
    }
    // Every CSR input must be covered, else we'd need a (binary-search) random
    // access we don't generate.
    for (i, &csr) in is_csr.iter().enumerate() {
        if csr && !sparse_covered[i] {
            return Err(JitError::Unsupported(
                "a CSR input's column index could not be reached by sparse row iteration",
            ));
        }
    }

    // Dense row-major layouts (CSR inputs get an unused placeholder).
    let axis_dims = |pat: &[u8]| -> Vec<usize> { pat.iter().map(|&s| dims[s as usize]).collect() };
    let in_layouts: Vec<DenseLayout> =
        inputs.iter().map(|p| DenseLayout::new(&axis_dims(p))).collect();
    let out_layouts: Vec<DenseLayout> =
        outputs.iter().map(|p| DenseLayout::new(&axis_dims(p))).collect();

    let mut module = new_module();
    let ptr_ty = module.target_config().pointer_type();
    let ptr_bytes = ptr_ty.bytes() as i32;

    let mut ctx = module.make_context();
    let mut sig = module.make_signature();
    sig.params.push(AbiParam::new(ptr_ty)); // ins:  *const *const u8
    sig.params.push(AbiParam::new(ptr_ty)); // outs: *const *mut  u8
    ctx.func.signature = sig;

    let mut fbctx = FunctionBuilderContext::new();
    {
        let mut b = FunctionBuilder::new(&mut ctx.func, &mut fbctx);

        // One index variable per slot, an accumulator register, and a value
        // register per CSR input. Unused variables are harmless.
        let vars: [Variable; 26] = std::array::from_fn(|_| b.declare_var(ptr_ty));
        let acc = b.declare_var(types::F32);
        let val_vars: Vec<Option<Variable>> = is_csr
            .iter()
            .map(|&csr| if csr { Some(b.declare_var(types::F32)) } else { None })
            .collect();

        let entry = b.create_block();
        b.append_block_params_for_function_params(entry);
        b.switch_to_block(entry);
        b.seal_block(entry);
        let ins_ptr = b.block_params(entry)[0];
        let outs_ptr = b.block_params(entry)[1];

        // Load base pointer(s) for every input (dense: 1 slot, CSR: 3 slots).
        let mut bases: Vec<InputBase> = Vec::with_capacity(inputs.len());
        let mut slot = 0i32;
        for &csr in is_csr {
            if csr {
                let rp = b.ins().load(ptr_ty, MemFlags::trusted(), ins_ptr, slot * ptr_bytes);
                let ci =
                    b.ins().load(ptr_ty, MemFlags::trusted(), ins_ptr, (slot + 1) * ptr_bytes);
                let vv =
                    b.ins().load(ptr_ty, MemFlags::trusted(), ins_ptr, (slot + 2) * ptr_bytes);
                bases.push(InputBase::Csr { row_ptr: rp, col_idx: ci, values: vv });
                slot += 3;
            } else {
                let p = b.ins().load(ptr_ty, MemFlags::trusted(), ins_ptr, slot * ptr_bytes);
                bases.push(InputBase::Dense(p));
                slot += 1;
            }
        }
        let out_bases: Vec<Value> = (0..outputs.len())
            .map(|i| b.ins().load(ptr_ty, MemFlags::trusted(), outs_ptr, i as i32 * ptr_bytes))
            .collect();

        if !any_sparse && outputs.len() == 1 {
            // ── All-dense single output: register accumulator. ──
            // for free: { acc = 0; for contracted { acc += prod }; out = acc }
            let mut free_loops = Vec::new();
            for &s in &free {
                free_loops.push((vars[s as usize], open_dense_loop(&mut b, ptr_ty, vars[s as usize], dims[s as usize])));
            }
            let zero = b.ins().f32const(0.0);
            b.def_var(acc, zero);
            let mut c_loops = Vec::new();
            for &s in &contracted {
                c_loops.push((vars[s as usize], open_dense_loop(&mut b, ptr_ty, vars[s as usize], dims[s as usize])));
            }

            let prod = emit_product(&mut b, ptr_ty, inputs, &in_layouts, &bases, &val_vars, &vars);
            let cur = b.use_var(acc);
            let sum = b.ins().fadd(cur, prod);
            b.def_var(acc, sum);

            for (iv, (h, e)) in c_loops.into_iter().rev() {
                close_loop(&mut b, iv, h, e);
            }
            let acc_val = b.use_var(acc);
            let idx_vals: Vec<Value> =
                outputs[0].iter().map(|&s| b.use_var(vars[s as usize])).collect();
            let addr = out_layouts[0].emit_elem_addr(&mut b, ptr_ty, out_bases[0], &idx_vals);
            b.ins().store(MemFlags::trusted(), acc_val, addr, 0);
            for (iv, (h, e)) in free_loops.into_iter().rev() {
                close_loop(&mut b, iv, h, e);
            }
        } else {
            // ── General path: sparse-aware loop nest, read-modify-write. ──
            let mut opened: Vec<(Variable, Block, Block)> = Vec::with_capacity(plan.len());
            for op in &plan {
                match *op {
                    LoopOp::Dense { slot } => {
                        let (h, e) =
                            open_dense_loop(&mut b, ptr_ty, vars[slot as usize], dims[slot as usize]);
                        opened.push((vars[slot as usize], h, e));
                    }
                    LoopOp::Sparse { input_idx, row_slot, col_slot } => {
                        let (rp, ci, vv) = match bases[input_idx] {
                            InputBase::Csr { row_ptr, col_idx, values } => (row_ptr, col_idx, values),
                            InputBase::Dense(_) => unreachable!("sparse op on dense input"),
                        };
                        let (ei, h, e) = open_sparse_loop(
                            &mut b,
                            ptr_ty,
                            vars[row_slot as usize],
                            vars[col_slot as usize],
                            val_vars[input_idx].expect("CSR input has value var"),
                            rp,
                            ci,
                            vv,
                        );
                        opened.push((ei, h, e));
                    }
                }
            }

            let prod = emit_product(&mut b, ptr_ty, inputs, &in_layouts, &bases, &val_vars, &vars);
            for (oi, pattern) in outputs.iter().enumerate() {
                let idx_vals: Vec<Value> =
                    pattern.iter().map(|&s| b.use_var(vars[s as usize])).collect();
                let addr =
                    out_layouts[oi].emit_elem_addr(&mut b, ptr_ty, out_bases[oi], &idx_vals);
                let cur = b.ins().load(types::F32, MemFlags::trusted(), addr, 0);
                let sum = b.ins().fadd(cur, prod);
                b.ins().store(MemFlags::trusted(), sum, addr, 0);
            }

            for (iv, h, e) in opened.into_iter().rev() {
                close_loop(&mut b, iv, h, e);
            }
        }

        b.ins().return_(&[]);
        b.finalize();
    }

    let id = module
        .declare_function("einsum", Linkage::Export, &ctx.func.signature)
        .expect("declare_function");
    module.define_function(id, &mut ctx).expect("define_function");
    module.clear_context(&mut ctx);
    module.finalize_definitions().expect("finalize_definitions");

    let code = module.get_finalized_function(id);
    // SAFETY: `code` is a finalized function with exactly the declared
    // signature (two pointer params, no return); `module` is returned and
    // kept alive by the caller so the code stays mapped.
    let func = unsafe {
        mem::transmute::<*const u8, extern "C" fn(*const *const u8, *const *mut u8)>(code)
    };
    Ok((module, func))
}

// ─────────────────────────────────────────────────────────────────────────
// Tests
// ─────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tensor::NDIndex;

    fn dense(shape: Vec<usize>, data: &[f32]) -> Dense<f32> {
        let mut d = Dense::<f32>::zeros(shape);
        d.fill_from(data);
        d
    }

    fn d(x: &Dense<f32>) -> JitInput<'_> {
        JitInput::Dense(x)
    }

    #[test]
    fn matmul() {
        let a = dense(vec![2, 3], &[1., 2., 3., 4., 5., 6.]);
        let b = dense(vec![3, 2], &[7., 8., 9., 10., 11., 12.]);
        let jit = DenseF32Jit::compile("ab,bc->ac", &[d(&a), d(&b)], &[vec![2, 2]]).unwrap();
        let mut c = Dense::<f32>::zeros(vec![2, 2]);
        jit.run(&[d(&a), d(&b)], &mut [&mut c]);
        assert_eq!(c.data, vec![58., 64., 139., 154.]);
    }

    #[test]
    fn transpose() {
        let a = dense(vec![2, 3], &[1., 2., 3., 4., 5., 6.]);
        let jit = DenseF32Jit::compile("ab->ba", &[d(&a)], &[vec![3, 2]]).unwrap();
        let mut t = Dense::<f32>::zeros(vec![3, 2]);
        jit.run(&[d(&a)], &mut [&mut t]);
        assert_eq!(t.data, vec![1., 4., 2., 5., 3., 6.]);
    }

    #[test]
    fn dot_to_scalar() {
        let a = dense(vec![4], &[1., 2., 3., 4.]);
        let b = dense(vec![4], &[5., 6., 7., 8.]);
        let jit = DenseF32Jit::compile("i,i->", &[d(&a), d(&b)], &[vec![]]).unwrap();
        let mut s = Dense::<f32>::zeros(vec![]);
        jit.run(&[d(&a), d(&b)], &mut [&mut s]);
        assert_eq!(s.get(&[]), 70.0);
    }

    #[test]
    fn trace() {
        let m = dense(vec![3, 3], &[1., 2., 3., 4., 5., 6., 7., 8., 9.]);
        let jit = DenseF32Jit::compile("aa->", &[d(&m)], &[vec![]]).unwrap();
        let mut s = Dense::<f32>::zeros(vec![]);
        jit.run(&[d(&m)], &mut [&mut s]);
        assert_eq!(s.get(&[]), 15.0);
    }

    #[test]
    fn three_input_chain() {
        let a = dense(vec![2, 3], &[1., 2., 3., 4., 5., 6.]);
        let b = dense(vec![3, 4], &[1., 0., 0., 0., 0., 1., 0., 0., 0., 0., 1., 0.]);
        let c = dense(vec![4, 2], &[1., 2., 3., 4., 5., 6., 7., 8.]);
        let jit = DenseF32Jit::compile("ab,bc,cd->ad", &[d(&a), d(&b), d(&c)], &[vec![2, 2]])
            .unwrap();
        let mut out = Dense::<f32>::zeros(vec![2, 2]);
        jit.run(&[d(&a), d(&b), d(&c)], &mut [&mut out]);
        assert_eq!(out.data, vec![22., 28., 49., 64.]);
    }

    #[test]
    fn multi_output() {
        let a = dense(vec![2, 2], &[1., 2., 3., 4.]);
        let b = dense(vec![2, 2], &[5., 6., 7., 8.]);
        let jit = DenseF32Jit::compile(
            "ab,bc->ac,ca",
            &[d(&a), d(&b)],
            &[vec![2, 2], vec![2, 2]],
        )
        .unwrap();
        let mut ac = Dense::<f32>::zeros(vec![2, 2]);
        let mut ca = Dense::<f32>::zeros(vec![2, 2]);
        jit.run(&[d(&a), d(&b)], &mut [&mut ac, &mut ca]);
        assert_eq!(ac.data, vec![19., 22., 43., 50.]);
        assert_eq!(ca.data, vec![19., 43., 22., 50.]);
    }

    #[test]
    fn reused_across_executions() {
        let b = dense(vec![2, 2], &[1., 2., 3., 4.]);
        let a0 = dense(vec![2, 2], &[1., 0., 0., 1.]);
        let jit = DenseF32Jit::compile("ab,bc->ac", &[d(&a0), d(&b)], &[vec![2, 2]]).unwrap();
        for k in 1..4u32 {
            let f = k as f32;
            let a = dense(vec![2, 2], &[f, 0., 0., f]);
            let mut c = Dense::<f32>::zeros(vec![2, 2]);
            jit.run(&[d(&a), d(&b)], &mut [&mut c]);
            assert_eq!(c.data, vec![f, f * 2., f * 3., f * 4.]);
        }
    }

    // ── CSR-sparse inputs ──

    /// 3×3 cyclic permutation: edges (0,1),(1,2),(2,0) with value 1.
    fn cyclic_perm() -> Csr<u32, f32> {
        Csr::<u32, f32>::from_coo(3, &mut vec![(0, 1, 1.0), (1, 2, 1.0), (2, 0, 1.0)])
    }

    #[test]
    fn csr_times_dense() {
        let a = cyclic_perm();
        let x = dense(vec![3, 2], &[1., 2., 3., 4., 5., 6.]);
        let jit =
            DenseF32Jit::compile("ab,bc->ac", &[JitInput::Csr(&a), d(&x)], &[vec![3, 2]]).unwrap();
        let mut y = Dense::<f32>::zeros(vec![3, 2]);
        jit.run(&[JitInput::Csr(&a), d(&x)], &mut [&mut y]);
        // row i picks up row (i+1 mod 3) of x.
        assert_eq!(y.data, vec![3., 4., 5., 6., 1., 2.]);
    }

    #[test]
    fn csr_times_csr() {
        let a = cyclic_perm();
        let b = cyclic_perm();
        let jit = DenseF32Jit::compile(
            "ab,bc->ac",
            &[JitInput::Csr(&a), JitInput::Csr(&b)],
            &[vec![3, 3]],
        )
        .unwrap();
        let mut c = Dense::<f32>::zeros(vec![3, 3]);
        jit.run(&[JitInput::Csr(&a), JitInput::Csr(&b)], &mut [&mut c]);
        // shift twice: edges (0,2),(1,0),(2,1).
        assert_eq!(c.data, vec![0., 0., 1., 1., 0., 0., 0., 1., 0.]);
    }

    #[test]
    fn csr_dense_matches_einsum_vm() {
        use crate::einsum::einsum;

        // Random-ish but structured sparse A (5×5) and dense X (5×3).
        let a = Csr::<u32, f32>::from_coo(
            5,
            &mut vec![
                (0, 1, 2.0),
                (0, 4, -1.0),
                (1, 1, 3.0),
                (2, 0, 1.5),
                (2, 3, 0.5),
                (4, 2, -2.0),
            ],
        );
        let mut state = 0x1234_5678u64;
        let mut x = Dense::<f32>::zeros(vec![5, 3]);
        for v in x.data.iter_mut() {
            state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
            *v = ((state >> 33) as f32 / u32::MAX as f32) * 2.0 - 1.0;
        }

        let jit =
            DenseF32Jit::compile("ab,bc->ac", &[JitInput::Csr(&a), d(&x)], &[vec![5, 3]]).unwrap();
        let mut jit_out = Dense::<f32>::zeros(vec![5, 3]);
        jit.run(&[JitInput::Csr(&a), d(&x)], &mut [&mut jit_out]);

        let mut vm_out = Dense::<f32>::zeros(vec![5, 3]);
        einsum::<f32>(
            "ab,bc->ac",
            &[&a as &dyn NDIndex<f32>, &x],
            &mut [&mut vm_out as &mut dyn NDIndex<f32>],
        )
        .unwrap();

        for (j, v) in jit_out.data.iter().zip(vm_out.data.iter()) {
            assert!((j - v).abs() <= 1e-5 * (1.0 + v.abs()), "jit {j} vs vm {v}");
        }
    }

    #[test]
    fn unsupported_sparse_pattern_errs() {
        // Both operands sparse and sharing the contracted column index 'b':
        // the second's column can't be reached by row iteration.
        let a = cyclic_perm();
        let b = cyclic_perm();
        let err = DenseF32Jit::compile(
            "ab,cb->ac",
            &[JitInput::Csr(&a), JitInput::Csr(&b)],
            &[vec![3, 3]],
        )
        .err();
        assert!(matches!(err, Some(JitError::Unsupported(_))), "got {err:?}");
    }

    /// Cross-check the all-dense paths against the interpreted VM.
    #[test]
    fn matches_vm_on_random() {
        use crate::einsum::einsum_homogenous;

        let mut state = 0x2545F4914F6CDD1Du64;
        let mut next = || {
            state = state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            ((state >> 33) as f32 / u32::MAX as f32) * 2.0 - 1.0
        };
        let mut rand_dense = |shape: Vec<usize>| {
            let n: usize = if shape.is_empty() { 1 } else { shape.iter().product() };
            let data: Vec<f32> = (0..n).map(|_| next()).collect();
            dense(shape, &data)
        };

        let cases: &[(&str, &[&[usize]], &[&[usize]])] = &[
            ("ab,bc->ac", &[&[5, 7], &[7, 3]], &[&[5, 3]]),
            ("abc,acd->abd", &[&[2, 4, 3], &[2, 3, 5]], &[&[2, 4, 5]]),
            ("ab->ba", &[&[6, 4]], &[&[4, 6]]),
            ("ij,ij->", &[&[4, 5], &[4, 5]], &[&[]]),
            ("ab,bc,cd->ad", &[&[2, 3], &[3, 4], &[4, 2]], &[&[2, 2]]),
            ("ab,bc->ac,ca", &[&[3, 4], &[4, 3]], &[&[3, 3], &[3, 3]]),
        ];

        for (spec, in_shapes, out_shapes) in cases {
            let ins: Vec<Dense<f32>> = in_shapes.iter().map(|s| rand_dense(s.to_vec())).collect();
            let jit_inputs: Vec<JitInput> = ins.iter().map(d).collect();
            let in_refs: Vec<&Dense<f32>> = ins.iter().collect();

            let jit = DenseF32Jit::compile(
                spec,
                &jit_inputs,
                &out_shapes.iter().map(|s| s.to_vec()).collect::<Vec<_>>(),
            )
            .unwrap();

            let mut jit_outs: Vec<Dense<f32>> =
                out_shapes.iter().map(|s| Dense::<f32>::zeros(s.to_vec())).collect();
            let mut jit_refs: Vec<&mut Dense<f32>> = jit_outs.iter_mut().collect();
            jit.run(&jit_inputs, &mut jit_refs);

            let mut vm_outs: Vec<Dense<f32>> =
                out_shapes.iter().map(|s| Dense::<f32>::zeros(s.to_vec())).collect();
            let mut vm_refs: Vec<&mut Dense<f32>> = vm_outs.iter_mut().collect();
            einsum_homogenous::<f32, _, _>(spec, &in_refs, &mut vm_refs).unwrap();

            for (oi, (j, v)) in jit_outs.iter().zip(vm_outs.iter()).enumerate() {
                for (k, (jv, vv)) in j.data.iter().zip(v.data.iter()).enumerate() {
                    assert!(
                        (jv - vv).abs() <= 1e-4 * (1.0 + vv.abs()),
                        "spec {spec} output {oi} elem {k}: jit {jv} vs vm {vv}"
                    );
                }
            }
        }
    }

    #[test]
    fn spec_errors_surface() {
        let a = dense(vec![2, 3], &[0.; 6]);
        let b = dense(vec![3, 2], &[0.; 6]);
        let b_bad = dense(vec![4, 2], &[0.; 8]);
        assert_eq!(
            DenseF32Jit::compile("ab,bc", &[d(&a), d(&b)], &[vec![2, 2]]).err(),
            Some(JitError::Spec(InvalidSpec::MissingArrow)),
        );
        assert_eq!(
            DenseF32Jit::compile("ab,bc->az", &[d(&a), d(&b)], &[vec![2, 2]]).err(),
            Some(JitError::Spec(InvalidSpec::UnboundOutputIndex { index: 'z' })),
        );
        assert_eq!(
            DenseF32Jit::compile("ab,bc->ac", &[d(&a), d(&b_bad)], &[vec![2, 2]]).err(),
            Some(JitError::Spec(InvalidSpec::DimensionMismatch {
                index: 'b',
                expected: 3,
                got: 4
            })),
        );
    }
}
