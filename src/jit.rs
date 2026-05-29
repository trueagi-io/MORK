//! Cranelift JIT backend for Einstein summation over [`Dense<f32>`].
//!
//! This is the native-code counterpart to the interpreted [`crate::einsum`]
//! VM. A spec like `"ab,bc->ac"` plus concrete input/output shapes is
//! compiled — once — into a machine-code loop nest that reads and writes the
//! tensors' backing storage directly (no per-element trait dispatch). The
//! compiled [`DenseF32Jit`] is then reused across many executions of the same
//! spec and shapes.
//!
//! # Design
//!
//! - **Direct memory.** The codegen emits native loads/stores against the raw
//!   `f32` data pointers, with row-major strides baked in as constants. There
//!   is no callback into `NDIndex`.
//! - **Shape-specialized.** Dimensions are baked into the generated code as
//!   constants, so a given [`DenseF32Jit`] is valid only for the exact shapes
//!   it was compiled for ([`run`](DenseF32Jit::run) asserts this).
//! - **Layout seam.** [`Layout`] abstracts "how to address an element of this
//!   tensor struct". [`DenseLayout`] is the only implementation today; CSR /
//!   blocked layouts can plug in later without touching the loop-nest logic.
//!
//! Inputs and outputs are passed across the JIT boundary as arrays of raw
//! pointers, so the Rust-side call is a single monomorphic `extern "C"`
//! invocation regardless of arity:
//!
//! ```text
//! extern "C" fn(ins: *const *const f32, outs: *const *mut f32)
//! ```
//!
//! # Output convention
//!
//! Outputs are **accumulated into** and must be zeroed by the caller before
//! [`run`](DenseF32Jit::run) (same convention as [`crate::einsum`]). For a
//! single output the contraction sum is held in a register and stored once
//! per free-index tuple; multiple outputs fall back to read-modify-write.
//!
//! # Example
//!
//! ```
//! use linalg::jit::DenseF32Jit;
//! use linalg::dense::Dense;
//! use linalg::tensor::NDIndex;
//!
//! let jit = DenseF32Jit::compile("ab,bc->ac", &[vec![2, 3], vec![3, 2]], &[vec![2, 2]]).unwrap();
//!
//! let mut a = Dense::<f32>::zeros(vec![2, 3]);
//! a.fill_from(&[1., 2., 3., 4., 5., 6.]);
//! let mut b = Dense::<f32>::zeros(vec![3, 2]);
//! b.fill_from(&[7., 8., 9., 10., 11., 12.]);
//! let mut c = Dense::<f32>::zeros(vec![2, 2]);
//!
//! jit.run(&[&a, &b], &mut [&mut c]);
//! assert_eq!(c.get(&[0, 0]), 58.0);
//! assert_eq!(c.get(&[1, 1]), 154.0);
//! ```

use std::mem;

use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::{types, AbiParam, Block, InstBuilder, MemFlags, Type, Value};
use cranelift_codegen::settings::{self, Configurable};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Variable};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{Linkage, Module};

use crate::dense::Dense;
use crate::einsum::{parse_spec, InvalidSpec};

// ─────────────────────────────────────────────────────────────────────────
// Layout seam
// ─────────────────────────────────────────────────────────────────────────

/// How to address an element of a particular tensor struct from JIT'd code.
///
/// The loop-nest lowering is layout-agnostic: it hands a layout the current
/// per-axis index [`Value`]s and gets back the element address. `DenseLayout`
/// is the only implementor for now; other storage formats (CSR, blocked)
/// would implement this to plug into the same codegen.
trait Layout {
    /// Emit code computing the byte address of the element selected by
    /// `indices` (one [`Value`] per axis, outermost first) relative to `base`.
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
    /// Build from the per-axis dimensions of one tensor (outermost first).
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

/// A compiled, shape-specialized einsum over [`Dense<f32>`].
///
/// Construct with [`compile`](Self::compile); execute with
/// [`run`](Self::run). Holds the owning [`JITModule`] so the generated code
/// stays mapped for the lifetime of this value.
pub struct DenseF32Jit {
    // Kept alive so the finalized code memory `func` points into stays valid.
    _module: JITModule,
    func: extern "C" fn(*const *const f32, *const *mut f32),
    input_shapes: Vec<Vec<usize>>,
    output_shapes: Vec<Vec<usize>>,
}

impl DenseF32Jit {
    /// Compile `spec` for the given input and output shapes.
    ///
    /// Shapes are outermost-axis-first, matching [`Dense::shape`]. Dimensions
    /// are validated for consistency across repeated indices and baked into
    /// the generated code, so the returned program is valid only for these
    /// exact shapes.
    pub fn compile(
        spec: &str,
        input_shapes: &[Vec<usize>],
        output_shapes: &[Vec<usize>],
    ) -> Result<Self, InvalidSpec> {
        let parsed = parse_spec(spec, input_shapes.len())?;

        // Collect and validate per-slot dimensions from the input shapes.
        let mut dims = [0usize; 26];
        let mut dim_set = [false; 26];
        for (pi, pattern) in parsed.inputs.iter().enumerate() {
            if input_shapes[pi].len() != pattern.len() {
                return Err(InvalidSpec::InputNdimMismatch {
                    input: pi,
                    array_ndim: input_shapes[pi].len(),
                    spec_ndim: pattern.len(),
                });
            }
            for (pos, &s) in pattern.iter().enumerate() {
                let si = s as usize;
                let d = input_shapes[pi][pos];
                if dim_set[si] {
                    if dims[si] != d {
                        return Err(InvalidSpec::DimensionMismatch {
                            index: (s + b'a') as char,
                            expected: dims[si],
                            got: d,
                        });
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
            });
        }
        for (oi, pattern) in parsed.outputs.iter().enumerate() {
            if output_shapes[oi].len() != pattern.len() {
                return Err(InvalidSpec::OutputNdimMismatch {
                    array_ndim: output_shapes[oi].len(),
                    spec_ndim: pattern.len(),
                });
            }
            for (pos, &s) in pattern.iter().enumerate() {
                if output_shapes[oi][pos] != dims[s as usize] {
                    return Err(InvalidSpec::OutputDimMismatch {
                        axis: pos,
                        expected: dims[s as usize],
                        got: output_shapes[oi][pos],
                    });
                }
            }
        }

        let func = codegen(&parsed.inputs, &parsed.outputs, &dims);

        Ok(Self {
            _module: func.0,
            func: func.1,
            input_shapes: input_shapes.to_vec(),
            output_shapes: output_shapes.to_vec(),
        })
    }

    /// Execute against concrete tensors.
    ///
    /// Panics if any input/output count or shape does not match what this
    /// program was compiled for. Outputs must be pre-zeroed (results are
    /// accumulated in).
    pub fn run(&self, inputs: &[&Dense<f32>], outputs: &mut [&mut Dense<f32>]) {
        assert_eq!(
            inputs.len(),
            self.input_shapes.len(),
            "input count mismatch: got {}, compiled for {}",
            inputs.len(),
            self.input_shapes.len()
        );
        assert_eq!(
            outputs.len(),
            self.output_shapes.len(),
            "output count mismatch: got {}, compiled for {}",
            outputs.len(),
            self.output_shapes.len()
        );
        for (i, inp) in inputs.iter().enumerate() {
            assert_eq!(
                inp.shape, self.input_shapes[i],
                "input {i} shape mismatch: got {:?}, compiled for {:?}",
                inp.shape, self.input_shapes[i]
            );
        }
        for (o, out) in outputs.iter().enumerate() {
            assert_eq!(
                out.shape, self.output_shapes[o],
                "output {o} shape mismatch: got {:?}, compiled for {:?}",
                out.shape, self.output_shapes[o]
            );
        }

        let in_ptrs: Vec<*const f32> = inputs.iter().map(|d| d.data.as_ptr()).collect();
        let mut out_ptrs: Vec<*mut f32> = outputs.iter_mut().map(|d| d.data.as_mut_ptr()).collect();
        // SAFETY: the generated code reads exactly `in_ptrs.len()` input base
        // pointers and `out_ptrs.len()` output base pointers (both fixed at
        // compile time and asserted equal above), and addresses only elements
        // within the validated shapes.
        (self.func)(in_ptrs.as_ptr(), out_ptrs.as_mut_ptr());
    }
}

// ─────────────────────────────────────────────────────────────────────────
// Code generation
// ─────────────────────────────────────────────────────────────────────────

/// Open a counted loop `for v in 0..dim`. Returns `(header, exit)` blocks;
/// after this call the builder is positioned in the (sealed) loop body.
fn open_loop(b: &mut FunctionBuilder, ptr_ty: Type, v: Variable, dim: usize) -> (Block, Block) {
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

/// Close a loop opened by [`open_loop`]: increment, back-edge, seal header,
/// then position the builder in the (sealed) exit block.
fn close_loop(b: &mut FunctionBuilder, v: Variable, header: Block, exit: Block) {
    let idx = b.use_var(v);
    let next = b.ins().iadd_imm(idx, 1);
    b.def_var(v, next);
    b.ins().jump(header, &[]);
    b.seal_block(header);
    b.switch_to_block(exit);
    b.seal_block(exit);
}

/// Emit the product of all input elements at the current index values.
fn emit_product(
    b: &mut FunctionBuilder,
    ptr_ty: Type,
    inputs: &[Vec<u8>],
    layouts: &[DenseLayout],
    bases: &[Value],
    vars: &[Variable; 26],
) -> Value {
    let mut product: Option<Value> = None;
    for (i, pattern) in inputs.iter().enumerate() {
        let idx_vals: Vec<Value> = pattern.iter().map(|&s| b.use_var(vars[s as usize])).collect();
        let addr = layouts[i].emit_elem_addr(b, ptr_ty, bases[i], &idx_vals);
        let v = b.ins().load(types::F32, MemFlags::trusted(), addr, 0);
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
    dims: &[usize; 26],
) -> (JITModule, extern "C" fn(*const *const f32, *const *mut f32)) {
    // Classify slots: free (appear in some output) vs contracted (only inputs).
    let mut in_output = [false; 26];
    for out in outputs {
        for &s in out {
            in_output[s as usize] = true;
        }
    }

    // Order: first appearance across inputs then outputs.
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

    // Per-tensor row-major layouts (strides from each tensor's axis dims).
    let axis_dims = |pattern: &[u8]| -> Vec<usize> {
        pattern.iter().map(|&s| dims[s as usize]).collect()
    };
    let in_layouts: Vec<DenseLayout> =
        inputs.iter().map(|p| DenseLayout::new(&axis_dims(p))).collect();
    let out_layouts: Vec<DenseLayout> =
        outputs.iter().map(|p| DenseLayout::new(&axis_dims(p))).collect();

    let mut module = new_module();
    let ptr_ty = module.target_config().pointer_type();
    let ptr_bytes = ptr_ty.bytes() as i32;

    let mut ctx = module.make_context();
    let mut sig = module.make_signature();
    sig.params.push(AbiParam::new(ptr_ty)); // ins:  *const *const f32
    sig.params.push(AbiParam::new(ptr_ty)); // outs: *const *mut  f32
    ctx.func.signature = sig;

    let mut fbctx = FunctionBuilderContext::new();
    {
        let mut b = FunctionBuilder::new(&mut ctx.func, &mut fbctx);

        // One index variable per slot (0..26) plus the accumulator register.
        // Unused slot variables are harmless: they are never read or written.
        let vars: [Variable; 26] = std::array::from_fn(|_| b.declare_var(ptr_ty));
        let acc = b.declare_var(types::F32);

        let entry = b.create_block();
        b.append_block_params_for_function_params(entry);
        b.switch_to_block(entry);
        b.seal_block(entry);
        let ins_ptr = b.block_params(entry)[0];
        let outs_ptr = b.block_params(entry)[1];

        // Load base pointers for every input and output.
        let in_bases: Vec<Value> = (0..inputs.len())
            .map(|i| b.ins().load(ptr_ty, MemFlags::trusted(), ins_ptr, i as i32 * ptr_bytes))
            .collect();
        let out_bases: Vec<Value> = (0..outputs.len())
            .map(|i| b.ins().load(ptr_ty, MemFlags::trusted(), outs_ptr, i as i32 * ptr_bytes))
            .collect();

        if outputs.len() == 1 {
            // ── Single output: register accumulator over the contraction. ──
            // for free: { acc = 0; for contracted { acc += prod }; out[free] = acc }
            let mut free_loops = Vec::new();
            for &s in &free {
                free_loops.push((s, open_loop(&mut b, ptr_ty, vars[s as usize], dims[s as usize])));
            }

            let zero = b.ins().f32const(0.0);
            b.def_var(acc, zero);

            let mut c_loops = Vec::new();
            for &s in &contracted {
                c_loops.push((s, open_loop(&mut b, ptr_ty, vars[s as usize], dims[s as usize])));
            }

            let prod = emit_product(&mut b, ptr_ty, inputs, &in_layouts, &in_bases, &vars);
            let cur = b.use_var(acc);
            let sum = b.ins().fadd(cur, prod);
            b.def_var(acc, sum);

            for (s, (header, exit)) in c_loops.into_iter().rev() {
                close_loop(&mut b, vars[s as usize], header, exit);
            }

            // Store the accumulated value for this free-index tuple.
            let acc_val = b.use_var(acc);
            let idx_vals: Vec<Value> =
                outputs[0].iter().map(|&s| b.use_var(vars[s as usize])).collect();
            let addr = out_layouts[0].emit_elem_addr(&mut b, ptr_ty, out_bases[0], &idx_vals);
            b.ins().store(MemFlags::trusted(), acc_val, addr, 0);

            for (s, (header, exit)) in free_loops.into_iter().rev() {
                close_loop(&mut b, vars[s as usize], header, exit);
            }
        } else {
            // ── Multiple outputs: read-modify-write into each output. ──
            // Free slots differ per output, so no single accumulator applies.
            let mut loops = Vec::new();
            for &s in free.iter().chain(contracted.iter()) {
                loops.push((s, open_loop(&mut b, ptr_ty, vars[s as usize], dims[s as usize])));
            }

            let prod = emit_product(&mut b, ptr_ty, inputs, &in_layouts, &in_bases, &vars);
            for (oi, pattern) in outputs.iter().enumerate() {
                let idx_vals: Vec<Value> =
                    pattern.iter().map(|&s| b.use_var(vars[s as usize])).collect();
                let addr =
                    out_layouts[oi].emit_elem_addr(&mut b, ptr_ty, out_bases[oi], &idx_vals);
                let cur = b.ins().load(types::F32, MemFlags::trusted(), addr, 0);
                let sum = b.ins().fadd(cur, prod);
                b.ins().store(MemFlags::trusted(), sum, addr, 0);
            }

            for (s, (header, exit)) in loops.into_iter().rev() {
                close_loop(&mut b, vars[s as usize], header, exit);
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
    // SAFETY: `code` points at a finalized function with exactly the signature
    // we declared (two pointer params, no return). `module` is returned
    // alongside and kept alive by the caller, so the code stays mapped.
    let func = unsafe {
        mem::transmute::<*const u8, extern "C" fn(*const *const f32, *const *mut f32)>(code)
    };
    (module, func)
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

    #[test]
    fn matmul() {
        let jit =
            DenseF32Jit::compile("ab,bc->ac", &[vec![2, 3], vec![3, 2]], &[vec![2, 2]]).unwrap();
        let a = dense(vec![2, 3], &[1., 2., 3., 4., 5., 6.]);
        let b = dense(vec![3, 2], &[7., 8., 9., 10., 11., 12.]);
        let mut c = Dense::<f32>::zeros(vec![2, 2]);
        jit.run(&[&a, &b], &mut [&mut c]);
        assert_eq!(c.data, vec![58., 64., 139., 154.]);
    }

    #[test]
    fn transpose() {
        let jit = DenseF32Jit::compile("ab->ba", &[vec![2, 3]], &[vec![3, 2]]).unwrap();
        let a = dense(vec![2, 3], &[1., 2., 3., 4., 5., 6.]);
        let mut t = Dense::<f32>::zeros(vec![3, 2]);
        jit.run(&[&a], &mut [&mut t]);
        assert_eq!(t.data, vec![1., 4., 2., 5., 3., 6.]);
    }

    #[test]
    fn dot_to_scalar() {
        let jit = DenseF32Jit::compile("i,i->", &[vec![4], vec![4]], &[vec![]]).unwrap();
        let a = dense(vec![4], &[1., 2., 3., 4.]);
        let b = dense(vec![4], &[5., 6., 7., 8.]);
        let mut s = Dense::<f32>::zeros(vec![]);
        jit.run(&[&a, &b], &mut [&mut s]);
        assert_eq!(s.get(&[]), 70.0);
    }

    #[test]
    fn trace() {
        let jit = DenseF32Jit::compile("aa->", &[vec![3, 3]], &[vec![]]).unwrap();
        let m = dense(vec![3, 3], &[1., 2., 3., 4., 5., 6., 7., 8., 9.]);
        let mut s = Dense::<f32>::zeros(vec![]);
        jit.run(&[&m], &mut [&mut s]);
        assert_eq!(s.get(&[]), 15.0); // 1 + 5 + 9
    }

    #[test]
    fn three_input_chain() {
        let jit = DenseF32Jit::compile(
            "ab,bc,cd->ad",
            &[vec![2, 3], vec![3, 4], vec![4, 2]],
            &[vec![2, 2]],
        )
        .unwrap();
        let a = dense(vec![2, 3], &[1., 2., 3., 4., 5., 6.]);
        let b = dense(vec![3, 4], &[1., 0., 0., 0., 0., 1., 0., 0., 0., 0., 1., 0.]);
        let c = dense(vec![4, 2], &[1., 2., 3., 4., 5., 6., 7., 8.]);
        let mut d = Dense::<f32>::zeros(vec![2, 2]);
        jit.run(&[&a, &b, &c], &mut [&mut d]);
        assert_eq!(d.data, vec![22., 28., 49., 64.]);
    }

    #[test]
    fn multi_output() {
        let jit = DenseF32Jit::compile(
            "ab,bc->ac,ca",
            &[vec![2, 2], vec![2, 2]],
            &[vec![2, 2], vec![2, 2]],
        )
        .unwrap();
        let a = dense(vec![2, 2], &[1., 2., 3., 4.]);
        let b = dense(vec![2, 2], &[5., 6., 7., 8.]);
        let mut ac = Dense::<f32>::zeros(vec![2, 2]);
        let mut ca = Dense::<f32>::zeros(vec![2, 2]);
        jit.run(&[&a, &b], &mut [&mut ac, &mut ca]);
        assert_eq!(ac.data, vec![19., 22., 43., 50.]);
        assert_eq!(ca.data, vec![19., 43., 22., 50.]);
    }

    #[test]
    fn reused_across_executions() {
        let jit =
            DenseF32Jit::compile("ab,bc->ac", &[vec![2, 2], vec![2, 2]], &[vec![2, 2]]).unwrap();
        for k in 1..4u32 {
            let f = k as f32;
            let a = dense(vec![2, 2], &[f, 0., 0., f]); // f * I
            let b = dense(vec![2, 2], &[1., 2., 3., 4.]);
            let mut c = Dense::<f32>::zeros(vec![2, 2]);
            jit.run(&[&a, &b], &mut [&mut c]);
            assert_eq!(c.data, vec![f * 1., f * 2., f * 3., f * 4.]);
        }
    }

    /// Cross-check the JIT against the interpreted VM on random data for a
    /// spread of specs, beyond the hand-computed small cases above.
    #[test]
    fn matches_vm_on_random() {
        use crate::einsum::einsum_homogenous;

        // Cheap deterministic LCG so the test needs no rand dependency.
        let mut state = 0x2545F4914F6CDD1Du64;
        let mut next = || {
            state = state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            ((state >> 33) as f32 / u32::MAX as f32) * 2.0 - 1.0
        };
        let mut rand_dense = |shape: Vec<usize>| {
            let n: usize = if shape.is_empty() { 1 } else { shape.iter().product() };
            let data: Vec<f32> = (0..n).map(|_| next()).collect();
            let mut d = Dense::<f32>::zeros(shape);
            d.fill_from(&data);
            d
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
            let in_refs: Vec<&Dense<f32>> = ins.iter().collect();

            let jit = DenseF32Jit::compile(
                spec,
                &in_shapes.iter().map(|s| s.to_vec()).collect::<Vec<_>>(),
                &out_shapes.iter().map(|s| s.to_vec()).collect::<Vec<_>>(),
            )
            .unwrap();

            let mut jit_outs: Vec<Dense<f32>> =
                out_shapes.iter().map(|s| Dense::<f32>::zeros(s.to_vec())).collect();
            let mut jit_refs: Vec<&mut Dense<f32>> = jit_outs.iter_mut().collect();
            jit.run(&in_refs, &mut jit_refs);

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
        assert_eq!(
            DenseF32Jit::compile("ab,bc", &[vec![2, 3], vec![3, 2]], &[vec![2, 2]]).err(),
            Some(InvalidSpec::MissingArrow),
        );
        assert_eq!(
            DenseF32Jit::compile("ab,bc->az", &[vec![2, 3], vec![3, 2]], &[vec![2, 2]]).err(),
            Some(InvalidSpec::UnboundOutputIndex { index: 'z' }),
        );
        assert_eq!(
            DenseF32Jit::compile("ab,bc->ac", &[vec![2, 3], vec![4, 2]], &[vec![2, 2]]).err(),
            Some(InvalidSpec::DimensionMismatch { index: 'b', expected: 3, got: 4 }),
        );
    }
}
