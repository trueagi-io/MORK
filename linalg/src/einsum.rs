//! Runtime Einstein summation over arbitrary [`NDIndex`] inputs.
//!
//! A spec like `"ab,bc->ac"` is compiled into VM bytecode by [`compile`],
//! then [`Program::exec`] runs it against actual inputs and outputs. The
//! compiler emits sparse row-iteration loops for any input that exposes
//! a [`Sparse2D`] view via [`NDIndex::as_sparse_2d`], and dense loops
//! otherwise — so dense + sparse + block-sparse all compose.
//!
//! For one-shot use there are two convenience wrappers:
//!
//! - [`einsum`] — all inputs the same concrete type, all outputs the same
//!   concrete type. The wrapper still erases to `&dyn` internally; this is
//!   purely an ergonomic shortcut.
//! - [`einsum`] — public dyn-dispatch entry point.
//! - [`einsum_dyn`] — generic `?Sized` wrapper used by `einsum`; accepts
//!   either concrete types or trait objects.
//! - [`einsum_homogenous`] — strict-monomorphic version for one concrete
//!   `In` and one concrete `Out` (no vtable on NDIndex calls).
//!
//! # Spec format
//!
//! Lowercase letters `a..z` are index names; `->` separates inputs from
//! outputs; commas separate input groups (and optionally output groups for
//! multi-output specs).
//!
//! - `"ab,bc->ac"` — matrix multiply (contract over `b`)
//! - `"ab->ba"` — transpose
//! - `"i,i->"` — dot product (scalar output; pass a 0-dim tensor)
//! - `"aa->"` — trace
//! - `"ab,bc,cd->ad"` — N-ary chain
//! - `"ab,bc->ac,ca"` — multi-output: matmul and its transpose in one pass
//!
//! Indices in inputs but missing from the output are contracted (summed
//! over). All output indices must appear in at least one input.
//!
//! # Generalized reductions
//!
//! [`einsum_reduce`] generalizes the contraction to an arbitrary reduction
//! ⊕ ([`Reduce`]) over an elementwise combination ⊗ ([`Combine`]) — einsum
//! over a commutative semiring:
//!
//! ```text
//! out[free…] = ⊕ over contracted…  ( in₀[…] ⊗ in₁[…] ⊗ … )
//! ```
//!
//! - `einsum_reduce("j,ikq,kq->ijk", Reduce::Max, Combine::Mul, …)` computes
//!   `A[i,j,k] = max over q of B[j] * C[i,k,q] * D[k,q]`.
//! - `einsum_reduce("ij,jk->ik", Reduce::Min, Combine::Add, …)` is min-plus
//!   (tropical) matrix multiplication — one all-pairs-shortest-path
//!   relaxation step.
//! - `Reduce::Sum` + `Combine::Mul` is plain einsum.
//!
//! Unlike [`einsum`] (which accumulates into caller-zeroed outputs), the
//! `einsum_reduce` wrappers first fill every output with the reduction
//! identity ([`Reduce::identity`]) — overwrite semantics. An empty
//! contraction range therefore yields the identity (e.g. `-∞` for
//! `Reduce::Max` over `f32`). To accumulate into existing output contents
//! instead, use [`compile_reduce`] + [`Program::exec`] with outputs
//! pre-filled however you like.
//!
//! Sparse row iteration (skipping structural zeros) is only used when a
//! structurally-missing operand annihilates its whole contribution to the
//! reduce identity — true precisely for (`Sum`, `Mul`), where a zero factor
//! makes the product 0 and adding 0 is a no-op. For every other op pair a
//! structural zero is an actual `0` value that must still compete in the
//! reduction (e.g. `max(…, 0)`), so sparse inputs are iterated densely via
//! `get_opt` (correct, but without the sparse speedup).
//!
//! ---
//!
//! <small>The generalized-reduction design — the operator set, the
//! per-operator identity table, and the overwrite-with-identity output
//! semantics — is modelled after the Julia library
//! [Tullio.jl](https://github.com/mcabbott/Tullio.jl).</small>

use std::fmt;

use crate::tensor::{NDIndex, Scalar, Sparse2D};

// ─────────────────────────────────────────────────────────────────────────
// Reduction / combination operators
// ─────────────────────────────────────────────────────────────────────────

/// Reduction operator ⊕: how contributions from contracted index tuples are
/// folded into an output element.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Reduce {
    Sum,
    Prod,
    Max,
    Min,
}

impl Reduce {
    /// The identity element of the operator: `apply(identity(), v) == v`.
    ///
    /// Outputs are pre-filled with this by the [`einsum_reduce`] wrappers,
    /// and it is the result of reducing over an empty range:
    /// `Sum → 0`, `Prod → 1`, `Max → -∞`/`T::MIN`, `Min → +∞`/`T::MAX`.
    pub fn identity<T: Scalar>(self) -> T {
        match self {
            Reduce::Sum => T::ZERO,
            Reduce::Prod => T::ONE,
            Reduce::Max => T::LEAST,
            Reduce::Min => T::GREATEST,
        }
    }

    /// Fold one contribution into the accumulator.
    ///
    /// `Max`/`Min` are comparison-based; their behaviour when a float
    /// operand is NaN is unspecified.
    #[inline]
    pub fn apply<T: Scalar>(self, acc: T, v: T) -> T {
        match self {
            Reduce::Sum => acc + v,
            Reduce::Prod => acc * v,
            Reduce::Max => if v > acc { v } else { acc },
            Reduce::Min => if v < acc { v } else { acc },
        }
    }
}

/// Elementwise combination ⊗: how the input operands at one index tuple are
/// merged into a single contribution (left-to-right in input order).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Combine {
    Mul,
    Add,
    Min,
    Max,
}

impl Combine {
    /// Combine the next operand into the partial contribution.
    ///
    /// `Max`/`Min` are comparison-based; their behaviour when a float
    /// operand is NaN is unspecified.
    #[inline]
    pub fn apply<T: Scalar>(self, a: T, b: T) -> T {
        match self {
            Combine::Mul => a * b,
            Combine::Add => a + b,
            Combine::Min => if b < a { b } else { a },
            Combine::Max => if b > a { b } else { a },
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────
// Error type
// ─────────────────────────────────────────────────────────────────────────

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InvalidSpec {
    MissingArrow,
    InvalidIndex { ch: char },
    WrongInputCount { expected: usize, got: usize },
    EmptyInput { input: usize },
    UnboundOutputIndex { index: char },
    InputNdimMismatch { input: usize, array_ndim: usize, spec_ndim: usize },
    DimensionMismatch { index: char, expected: usize, got: usize },
    OutputNdimMismatch { array_ndim: usize, spec_ndim: usize },
    OutputDimMismatch { axis: usize, expected: usize, got: usize },
}

fn slot_to_char(s: u8) -> char {
    (s + b'a') as char
}

impl fmt::Display for InvalidSpec {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingArrow => write!(f, "missing '->'"),
            Self::InvalidIndex { ch } => write!(f, "index '{ch}' is not a lowercase letter"),
            Self::WrongInputCount { expected, got } => {
                write!(f, "expected {expected} input(s), got {got}")
            }
            Self::EmptyInput { input } => write!(f, "input {input} has no indices"),
            Self::UnboundOutputIndex { index } => {
                write!(f, "output index '{index}' does not appear in any input")
            }
            Self::InputNdimMismatch { input, array_ndim, spec_ndim } => write!(
                f,
                "input {input} has {array_ndim} dimensions but spec has {spec_ndim} indices"
            ),
            Self::DimensionMismatch { index, expected, got } => {
                write!(f, "dimension mismatch for index '{index}': {expected} vs {got}")
            }
            Self::OutputNdimMismatch { array_ndim, spec_ndim } => write!(
                f,
                "output has {array_ndim} dimensions but spec has {spec_ndim} output indices"
            ),
            Self::OutputDimMismatch { axis, expected, got } => {
                write!(f, "output dimension {axis} is {got} but expected {expected}")
            }
        }
    }
}

impl std::error::Error for InvalidSpec {}

// ─────────────────────────────────────────────────────────────────────────
// Spec parser
// ─────────────────────────────────────────────────────────────────────────

pub(crate) struct Spec {
    pub(crate) inputs: Vec<Vec<u8>>,
    pub(crate) outputs: Vec<Vec<u8>>,
}

impl Spec {
    fn output(&self) -> &[u8] {
        &self.outputs[0]
    }

    fn all_output_slots(&self) -> Vec<u8> {
        let mut seen = [false; 26];
        let mut slots = Vec::new();
        for out in &self.outputs {
            for &s in out {
                if !seen[s as usize] {
                    seen[s as usize] = true;
                    slots.push(s);
                }
            }
        }
        slots
    }
}

pub(crate) fn parse_spec(spec: &str, expected_inputs: usize) -> Result<Spec, InvalidSpec> {
    let spec = spec.replace(' ', "");
    let (lhs, rhs) = spec.split_once("->").ok_or(InvalidSpec::MissingArrow)?;

    let mut inputs: Vec<Vec<u8>> = Vec::new();
    for part in lhs.split(',') {
        let mut slots = Vec::new();
        for ch in part.bytes() {
            if !ch.is_ascii_lowercase() {
                return Err(InvalidSpec::InvalidIndex { ch: ch as char });
            }
            slots.push(ch - b'a');
        }
        inputs.push(slots);
    }

    if inputs.len() != expected_inputs {
        return Err(InvalidSpec::WrongInputCount {
            expected: expected_inputs,
            got: inputs.len(),
        });
    }

    for (i, inp) in inputs.iter().enumerate() {
        if inp.is_empty() {
            return Err(InvalidSpec::EmptyInput { input: i });
        }
    }

    let mut outputs: Vec<Vec<u8>> = Vec::new();
    for part in rhs.split(',') {
        let mut slots = Vec::new();
        for ch in part.bytes() {
            if !ch.is_ascii_lowercase() {
                return Err(InvalidSpec::InvalidIndex { ch: ch as char });
            }
            slots.push(ch - b'a');
        }
        outputs.push(slots);
    }

    let mut seen = [false; 26];
    for inp in &inputs {
        for &s in inp {
            seen[s as usize] = true;
        }
    }
    for out in &outputs {
        for &s in out {
            if !seen[s as usize] {
                return Err(InvalidSpec::UnboundOutputIndex { index: slot_to_char(s) });
            }
        }
    }

    Ok(Spec { inputs, outputs })
}

fn validate_output<T, Out: NDIndex<T> + ?Sized>(
    spec_pattern: &[u8],
    dims: &[usize; 26],
    out: &Out,
) -> Result<(), InvalidSpec> {
    if out.ndim() != spec_pattern.len() {
        return Err(InvalidSpec::OutputNdimMismatch {
            array_ndim: out.ndim(),
            spec_ndim: spec_pattern.len(),
        });
    }
    for (pos, &s) in spec_pattern.iter().enumerate() {
        if out.dim(pos) != dims[s as usize] {
            return Err(InvalidSpec::OutputDimMismatch {
                axis: pos,
                expected: dims[s as usize],
                got: out.dim(pos),
            });
        }
    }
    Ok(())
}

// ─────────────────────────────────────────────────────────────────────────
// VM bytecode
// ─────────────────────────────────────────────────────────────────────────

#[derive(Debug)]
enum VmOp {
    /// Iterate `slot` from 0 to `dim-1`. `end_pc` is one past the matching
    /// `LoopEnd`. `fused` = body is a single `MulAcc`; run inline.
    DenseLoop { slot: u8, dim: usize, end_pc: usize, fused: bool },
    /// For each non-zero in `inputs[input_idx]`'s compound row — formed by
    /// flattening `leading` (row-major, using `leading_dims`) from the current
    /// `vals` — set `vals[col_slot]` to the column index. Same `end_pc`/`fused`
    /// meaning. For a 2D input `leading` is a single row slot.
    SparseRowLoop {
        input_idx: usize,
        leading: Vec<u8>,
        leading_dims: Vec<usize>,
        col_slot: u8,
        end_pc: usize,
        fused: bool,
    },
    LoopEnd,
    /// Allocate dense accumulator of size `dim`, indexed by `acc_slot`.
    AccStart { acc_slot: u8, acc_out_pos: u8, dim: usize },
    /// Flush accumulator: scatter-gather write touched entries, then clear.
    AccFlush,
    /// Multiply input values at current slot positions and accumulate.
    MulAcc,
}

/// Compiled einsum program. Construct via [`compile`] or [`compile_reduce`],
/// execute via [`Program::exec`].
pub struct Program {
    ops: Vec<VmOp>,
    input_patterns: Vec<Vec<u8>>,
    output_patterns: Vec<Vec<u8>>,
    /// For each input: `Some(loop_index)` of the `SparseRowLoop` that
    /// covers both axes — `MulAcc` reads the cached value instead of
    /// re-querying `get_opt`.
    sparse_value_source: Vec<Option<usize>>,
    reduce: Reduce,
    combine: Combine,
    /// True iff a structurally-missing operand annihilates its whole
    /// contribution to the reduce identity, so the tuple can be skipped
    /// outright — precisely the (Sum, Mul) semiring. Also gates whether
    /// the scheduler emitted `SparseRowLoop`s.
    skip_missing: bool,
}

/// Compile an einsum spec into a [`Program`] for the given input shapes.
///
/// Only the dimensionality and sparsity of each input matters here — the
/// actual input data is passed separately to [`Program::exec`], which can
/// re-use the compiled program across many executions.
///
/// Generic over `In: NDIndex<T> + ?Sized` so the same call works for both
/// concrete inputs and `&dyn NDIndex<T>` trait objects.
pub fn compile<T, In: NDIndex<T> + ?Sized>(
    spec_str: &str,
    inputs: &[&In],
) -> Result<Program, InvalidSpec> {
    compile_reduce::<T, In>(spec_str, Reduce::Sum, Combine::Mul, inputs)
}

/// [`compile`] generalized to an arbitrary ([`Reduce`], [`Combine`])
/// semiring. See the module docs for the semantics and the sparse-input
/// caveat: only (`Sum`, `Mul`) programs use sparse row iteration.
pub fn compile_reduce<T, In: NDIndex<T> + ?Sized>(
    spec_str: &str,
    reduce: Reduce,
    combine: Combine,
    inputs: &[&In],
) -> Result<Program, InvalidSpec> {
    let spec = parse_spec(spec_str, inputs.len())?;
    let skip_missing = reduce == Reduce::Sum && combine == Combine::Mul;

    // Validate dim consistency and capture per-slot dims.
    let mut dims = [0usize; 26];
    let mut dim_set = [false; 26];
    for (pi, inp_spec) in spec.inputs.iter().enumerate() {
        if inputs[pi].ndim() != inp_spec.len() {
            return Err(InvalidSpec::InputNdimMismatch {
                input: pi,
                array_ndim: inputs[pi].ndim(),
                spec_ndim: inp_spec.len(),
            });
        }
        for (pos, &s) in inp_spec.iter().enumerate() {
            let si = s as usize;
            let d = inputs[pi].dim(pos);
            if dim_set[si] {
                if dims[si] != d {
                    return Err(InvalidSpec::DimensionMismatch {
                        index: slot_to_char(s),
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

    // For each input exposing a sparse row view (any rank >= 2), record its
    // leading (compound-row) slots and trailing stored-column slot. Sparse
    // loops skip structural zeros, which is only sound under (Sum, Mul) —
    // for any other semiring a missing entry is a real 0 that must still
    // compete in the reduction, so we iterate those inputs densely.
    let sparse_axes: Vec<Option<(Vec<u8>, u8)>> = spec
        .inputs
        .iter()
        .zip(inputs.iter())
        .map(|(inp_spec, arr)| {
            if skip_missing && inp_spec.len() >= 2 && arr.as_sparse_2d().is_some() {
                let n = inp_spec.len();
                Some((inp_spec[..n - 1].to_vec(), inp_spec[n - 1]))
            } else {
                None
            }
        })
        .collect();

    // All slots in order of first appearance.
    let mut all_slots = Vec::new();
    let mut seen = [false; 26];
    for inp in &spec.inputs {
        for &s in inp {
            if !seen[s as usize] {
                seen[s as usize] = true;
                all_slots.push(s);
            }
        }
    }
    for out in &spec.outputs {
        for &s in out {
            if !seen[s as usize] {
                seen[s as usize] = true;
                all_slots.push(s);
            }
        }
    }

    // Greedy scheduler: pick sparse loops first when all their leading axes
    // are fixed, otherwise dense — preferring leading axes of sparse inputs to
    // unlock them.
    let mut fixed = [false; 26];
    let mut loop_order: Vec<VmOp> = Vec::new();
    let mut n_fixed = 0usize;

    while n_fixed < all_slots.len() {
        let mut found_sparse = false;
        for &s in &all_slots {
            if fixed[s as usize] {
                continue;
            }
            for (idx, axes) in sparse_axes.iter().enumerate() {
                if let Some((leading, col)) = axes {
                    let leads_fixed = leading.iter().all(|&l| fixed[l as usize]);
                    if *col == s && !leading.contains(&s) && leads_fixed {
                        let leading_dims =
                            leading.iter().map(|&l| dims[l as usize]).collect();
                        loop_order.push(VmOp::SparseRowLoop {
                            input_idx: idx,
                            leading: leading.clone(),
                            leading_dims,
                            col_slot: s,
                            end_pc: 0,
                            fused: false,
                        });
                        fixed[s as usize] = true;
                        n_fixed += 1;
                        found_sparse = true;
                        break;
                    }
                }
            }
            if found_sparse {
                break;
            }
        }

        if !found_sparse {
            let mut best = None;
            for &s in &all_slots {
                if fixed[s as usize] {
                    continue;
                }
                let is_sparse_lead = sparse_axes
                    .iter()
                    .any(|axes| matches!(axes, Some((leading, _)) if leading.contains(&s)));
                if is_sparse_lead || best.is_none() {
                    best = Some(s);
                    if is_sparse_lead {
                        break;
                    }
                }
            }
            let s = best.unwrap();
            loop_order.push(VmOp::DenseLoop {
                slot: s,
                dim: dims[s as usize],
                end_pc: 0,
                fused: false,
            });
            fixed[s as usize] = true;
            n_fixed += 1;
        }
    }

    // Cache: which inputs have all their axes covered by one SparseRowLoop?
    let sparse_value_source: Vec<Option<usize>> = spec
        .inputs
        .iter()
        .enumerate()
        .map(|(inp_idx, _)| {
            for (loop_idx, op) in loop_order.iter().enumerate() {
                if let VmOp::SparseRowLoop { input_idx, .. } = op {
                    if *input_idx == inp_idx {
                        return Some(loop_idx);
                    }
                }
            }
            None
        })
        .collect();

    // Dense accumulator: if the innermost loop's slot appears in the output
    // and at least one other output slot is in scope, batch writes.
    let all_output_slots = spec.all_output_slots();
    let mut acc_info: Option<(u8, u8, usize, usize)> = None;
    if spec.outputs.len() == 1 {
        if let Some(last_op) = loop_order.last() {
            let inner_slot = match last_op {
                VmOp::DenseLoop { slot, .. } => *slot,
                VmOp::SparseRowLoop { col_slot, .. } => *col_slot,
                _ => unreachable!(),
            };
            if let Some(pos) = spec.output().iter().position(|&s| s == inner_slot) {
                for (i, op) in loop_order.iter().enumerate().rev() {
                    let s = match op {
                        VmOp::DenseLoop { slot, .. } => *slot,
                        VmOp::SparseRowLoop { col_slot, .. } => *col_slot,
                        _ => unreachable!(),
                    };
                    if s != inner_slot && all_output_slots.contains(&s) {
                        acc_info = Some((inner_slot, pos as u8, dims[inner_slot as usize], i));
                        break;
                    }
                }
            }
        }
    }

    // Emit bytecode: loop-starts (with AccStart injection), then MulAcc,
    // then LoopEnds (with AccFlush injection).
    let n_loops = loop_order.len();
    let mut ops: Vec<VmOp> = Vec::with_capacity(n_loops * 2 + 4);

    for (i, op) in loop_order.into_iter().enumerate() {
        ops.push(op);
        if let Some((acc_slot, acc_out_pos, dim, flush_idx)) = acc_info {
            if i == flush_idx {
                ops.push(VmOp::AccStart { acc_slot, acc_out_pos, dim });
            }
        }
    }
    ops.push(VmOp::MulAcc);

    for i in 0..n_loops {
        let loop_idx = n_loops - 1 - i;
        if let Some((_, _, _, flush_idx)) = acc_info {
            if loop_idx == flush_idx {
                ops.push(VmOp::AccFlush);
            }
        }
        let start_pc = ops
            .iter()
            .enumerate()
            .filter(|(_, op)| matches!(op, VmOp::DenseLoop { .. } | VmOp::SparseRowLoop { .. }))
            .nth(loop_idx)
            .unwrap()
            .0;
        let end_pc = ops.len() + 1;
        match &mut ops[start_pc] {
            VmOp::DenseLoop { end_pc: ep, .. } => *ep = end_pc,
            VmOp::SparseRowLoop { end_pc: ep, .. } => *ep = end_pc,
            _ => unreachable!(),
        }
        ops.push(VmOp::LoopEnd);
    }

    // Fusion: a loop whose body is exactly `MulAcc` can call mul_acc inline.
    for pc in 0..ops.len() - 1 {
        let is_loop = matches!(&ops[pc], VmOp::DenseLoop { .. } | VmOp::SparseRowLoop { .. });
        if is_loop && matches!(&ops[pc + 1], VmOp::MulAcc) {
            match &mut ops[pc] {
                VmOp::DenseLoop { fused, .. } => *fused = true,
                VmOp::SparseRowLoop { fused, .. } => *fused = true,
                _ => unreachable!(),
            }
        }
    }

    Ok(Program {
        ops,
        input_patterns: spec.inputs.clone(),
        output_patterns: spec.outputs.clone(),
        sparse_value_source,
        reduce,
        combine,
        skip_missing,
    })
}

// ─────────────────────────────────────────────────────────────────────────
// VM interpreter
// ─────────────────────────────────────────────────────────────────────────

struct AccState<T> {
    acc: Vec<T>,
    /// Explicit set membership for `nz_cols`. Using a separate bool mask
    /// avoids false negatives when partial sums temporarily cancel to zero
    /// or when the first product into a slot is itself zero.
    touched: Vec<bool>,
    nz_cols: Vec<usize>,
    acc_slot: u8,
    acc_out_pos: u8,
}

impl Program {
    /// Execute against actual inputs and outputs.
    ///
    /// Generic over `In` and `Out` with a `?Sized` bound, so the same body
    /// covers two distinct dispatch styles:
    ///
    /// - `In = dyn NDIndex<T>` (called from [`einsum`]) — every `get_opt`
    ///   and `set` is a vtable call.
    /// - `In = SomeConcreteType` (called from [`einsum_homogenous`]) — the
    ///   monomorphisation inlines the NDIndex methods.
    ///
    /// `SparseRowLoop` always goes through `as_sparse_2d()`, which returns
    /// a `&dyn Sparse2D<T>` trait object — so the per-iteration `row_nnz`
    /// and `row_entry` calls remain vtable dispatched in both cases.
    pub fn exec<T: Scalar, In: NDIndex<T> + ?Sized, Out: NDIndex<T> + ?Sized>(
        &self,
        inputs: &[&In],
        outs: &mut [&mut Out],
    ) {
        // Cache one sparse view per input up front so the inner loop only
        // pays one vtable per row_entry call (not two).
        let sparse_views: Vec<Option<&dyn Sparse2D<T>>> =
            inputs.iter().map(|i| i.as_sparse_2d()).collect();

        let mut vals = [0usize; 26];
        let mut buf = [0usize; 26];
        let mut sparse_vals: Vec<T> = vec![T::default(); inputs.len()];
        let mut acc_state: Option<AccState<T>> = None;
        self.exec_at(
            0,
            &mut vals,
            &mut buf,
            &mut sparse_vals,
            &mut acc_state,
            inputs,
            &sparse_views,
            outs,
        );
    }

    fn exec_at<T: Scalar, In: NDIndex<T> + ?Sized, Out: NDIndex<T> + ?Sized>(
        &self,
        mut pc: usize,
        vals: &mut [usize; 26],
        buf: &mut [usize; 26],
        sparse_vals: &mut [T],
        acc_state: &mut Option<AccState<T>>,
        inputs: &[&In],
        sparse_views: &[Option<&dyn Sparse2D<T>>],
        outs: &mut [&mut Out],
    ) -> usize {
        let ops = &self.ops;
        while pc < ops.len() {
            match &ops[pc] {
                VmOp::DenseLoop { slot, dim, end_pc, fused } => {
                    let s = *slot as usize;
                    if *fused {
                        for v in 0..*dim {
                            vals[s] = v;
                            self.mul_acc(vals, buf, sparse_vals, acc_state, inputs, outs);
                        }
                    } else {
                        for v in 0..*dim {
                            vals[s] = v;
                            self.exec_at(
                                pc + 1,
                                vals,
                                buf,
                                sparse_vals,
                                acc_state,
                                inputs,
                                sparse_views,
                                outs,
                            );
                        }
                    }
                    pc = *end_pc;
                }
                VmOp::SparseRowLoop { input_idx, leading, leading_dims, col_slot, end_pc, fused } => {
                    // Compound row: row-major flatten of the leading slots.
                    let mut row = 0usize;
                    for (k, &ls) in leading.iter().enumerate() {
                        row = row * leading_dims[k] + vals[ls as usize];
                    }
                    let cs = *col_slot as usize;
                    // Compile guarantees: this input has as_sparse_2d() == Some(_)
                    let sparse = sparse_views[*input_idx]
                        .expect("SparseRowLoop on input without Sparse2D view");
                    let nnz = sparse.row_nnz(row);
                    if *fused {
                        for ei in 0..nnz {
                            let (col, val) = sparse.row_entry(row, ei);
                            vals[cs] = col;
                            sparse_vals[*input_idx] = val;
                            self.mul_acc(vals, buf, sparse_vals, acc_state, inputs, outs);
                        }
                    } else {
                        for ei in 0..nnz {
                            let (col, val) = sparse.row_entry(row, ei);
                            vals[cs] = col;
                            sparse_vals[*input_idx] = val;
                            self.exec_at(
                                pc + 1,
                                vals,
                                buf,
                                sparse_vals,
                                acc_state,
                                inputs,
                                sparse_views,
                                outs,
                            );
                        }
                    }
                    pc = *end_pc;
                }
                VmOp::LoopEnd => return pc + 1,
                VmOp::AccStart { acc_slot, acc_out_pos, dim } => {
                    *acc_state = Some(AccState {
                        acc: vec![self.reduce.identity(); *dim],
                        touched: vec![false; *dim],
                        nz_cols: Vec::new(),
                        acc_slot: *acc_slot,
                        acc_out_pos: *acc_out_pos,
                    });
                    pc += 1;
                }
                VmOp::AccFlush => {
                    if let Some(st) = acc_state {
                        let pattern = &self.output_patterns[0];
                        let len = pattern.len();
                        for &j in st.nz_cols.iter() {
                            for (i, &s) in pattern.iter().enumerate() {
                                buf[i] = vals[s as usize];
                            }
                            buf[st.acc_out_pos as usize] = j;
                            // RMW, not overwrite: when a contracted slot sits
                            // outside the accumulator's scope (e.g. `acd->cd`
                            // where `a` is outermost and the acc is over `d`),
                            // we visit each output element once per outer
                            // contracted tuple and the contributions must be
                            // reduced together. Output is pre-filled with the
                            // reduce identity by convention, so the first
                            // flush lands on the identity and later flushes
                            // keep reducing.
                            let cur = outs[0].get(&buf[..len]);
                            outs[0].set(&buf[..len], self.reduce.apply(cur, st.acc[j]));
                            st.acc[j] = self.reduce.identity();
                            st.touched[j] = false;
                        }
                        st.nz_cols.clear();
                    }
                    pc += 1;
                }
                VmOp::MulAcc => {
                    self.mul_acc(vals, buf, sparse_vals, acc_state, inputs, outs);
                    pc += 1;
                }
            }
        }
        pc
    }

    #[inline]
    fn mul_acc<T: Scalar, In: NDIndex<T> + ?Sized, Out: NDIndex<T> + ?Sized>(
        &self,
        vals: &[usize; 26],
        buf: &mut [usize; 26],
        sparse_vals: &[T],
        acc_state: &mut Option<AccState<T>>,
        inputs: &[&In],
        outs: &mut [&mut Out],
    ) {
        let mut contrib = None::<T>;
        for (i, pattern) in self.input_patterns.iter().enumerate() {
            let v = if self.sparse_value_source[i].is_some() {
                Some(sparse_vals[i])
            } else {
                let len = pattern.len();
                for (p, &s) in pattern.iter().enumerate() {
                    buf[p] = vals[s as usize];
                }
                inputs[i].get_opt(&buf[..len])
            };
            let v = match v {
                Some(v) => v,
                // Structurally missing. Under (Sum, Mul) the whole tuple's
                // contribution collapses to the reduce identity — skip it.
                // Under any other semiring it's an actual 0 value that must
                // still compete in the reduction (e.g. max(…, 0)).
                None if self.skip_missing => return,
                None => T::ZERO,
            };
            contrib = Some(match contrib {
                Some(p) => self.combine.apply(p, v),
                None => v,
            });
        }
        if let Some(p) = contrib {
            if let Some(st) = acc_state {
                let idx = vals[st.acc_slot as usize];
                if !st.touched[idx] {
                    st.touched[idx] = true;
                    st.nz_cols.push(idx);
                }
                st.acc[idx] = self.reduce.apply(st.acc[idx], p);
            } else {
                for (oi, pattern) in self.output_patterns.iter().enumerate() {
                    let len = pattern.len();
                    for (i, &s) in pattern.iter().enumerate() {
                        buf[i] = vals[s as usize];
                    }
                    let cur = outs[oi].get(&buf[..len]);
                    outs[oi].set(&buf[..len], self.reduce.apply(cur, p));
                }
            }
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────
// Convenience wrappers
// ─────────────────────────────────────────────────────────────────────────

/// Top-level dyn-dispatch entry point — every input and output is passed
/// as a `&dyn NDIndex<T>` trait object, so the inner loop's `get_opt`
/// and `set` calls are dispatched via vtable.
///
/// Use this when inputs are of *mixed concrete types* (e.g. one sparse
/// CSR matrix and one dense tensor), since the trait object erases the
/// concrete type. For all-same-type calls where speed matters, prefer
/// [`einsum_homogenous`].
///
/// # Example (requires the `dense` feature)
///
/// ```
/// # #[cfg(not(feature = "dense"))] fn main() {}
/// # #[cfg(feature = "dense")] fn main() {
/// use linalg::einsum::einsum;
/// use linalg::tensor::NDIndex;
/// use linalg::dense::Dense;
///
/// let mut a = Dense::<f32>::zeros(vec![2, 3]);
/// a.fill_from(&[1., 2., 3., 4., 5., 6.]);
/// let mut b = Dense::<f32>::zeros(vec![3, 2]);
/// b.fill_from(&[7., 8., 9., 10., 11., 12.]);
/// let mut c = Dense::<f32>::zeros(vec![2, 2]);
///
/// einsum::<f32>(
///     "ab,bc->ac",
///     &[&a as &dyn NDIndex<f32>, &b],
///     &mut [&mut c as &mut dyn NDIndex<f32>],
/// ).unwrap();
///
/// assert_eq!(c.get(&[0, 0]), 58.0);
/// assert_eq!(c.get(&[1, 1]), 154.0);
/// # }
/// ```
pub fn einsum<T: Scalar>(
    spec: &str,
    inputs: &[&dyn NDIndex<T>],
    outs: &mut [&mut dyn NDIndex<T>],
) -> Result<(), InvalidSpec> {
    einsum_dyn::<T, dyn NDIndex<T>, dyn NDIndex<T>>(spec, inputs, outs)
}

/// Generalized einsum over a ([`Reduce`], [`Combine`]) semiring —
/// dyn-dispatch entry point, mirroring [`einsum`].
///
/// Every output is first **filled with the reduction identity**
/// ([`Reduce::identity`]), then each contribution
/// `in₀[…] ⊗ in₁[…] ⊗ …` from the contracted index space is folded in
/// with ⊕ — overwrite semantics; an empty contraction leaves the
/// identity behind.
///
/// # Example: max-product and min-plus (requires the `dense` feature)
///
/// ```
/// # #[cfg(not(feature = "dense"))] fn main() {}
/// # #[cfg(feature = "dense")] fn main() {
/// use linalg::einsum::{einsum_reduce, Reduce, Combine};
/// use linalg::tensor::NDIndex;
/// use linalg::dense::Dense;
///
/// let mut a = Dense::<f32>::zeros(vec![2, 2]);
/// a.fill_from(&[1., -2., 3., 4.]);
/// let mut b = Dense::<f32>::zeros(vec![2, 2]);
/// b.fill_from(&[5., 6., -7., 8.]);
/// let mut c = Dense::<f32>::zeros(vec![2, 2]);
///
/// // c[a][c] = max_b a[a][b] * b[b][c]
/// einsum_reduce::<f32>(
///     "ab,bc->ac",
///     Reduce::Max,
///     Combine::Mul,
///     &[&a as &dyn NDIndex<f32>, &b],
///     &mut [&mut c as &mut dyn NDIndex<f32>],
/// ).unwrap();
/// assert_eq!(c.get(&[0, 0]), 14.0); // max(1·5, -2·-7)
///
/// // Min-plus (tropical): one shortest-path relaxation step.
/// let mut d = Dense::<f32>::zeros(vec![2, 2]);
/// einsum_reduce::<f32>(
///     "ab,bc->ac",
///     Reduce::Min,
///     Combine::Add,
///     &[&a as &dyn NDIndex<f32>, &b],
///     &mut [&mut d as &mut dyn NDIndex<f32>],
/// ).unwrap();
/// assert_eq!(d.get(&[0, 0]), -9.0); // min(1+5, -2+-7)
/// # }
/// ```
pub fn einsum_reduce<T: Scalar>(
    spec: &str,
    reduce: Reduce,
    combine: Combine,
    inputs: &[&dyn NDIndex<T>],
    outs: &mut [&mut dyn NDIndex<T>],
) -> Result<(), InvalidSpec> {
    einsum_reduce_dyn::<T, dyn NDIndex<T>, dyn NDIndex<T>>(spec, reduce, combine, inputs, outs)
}

/// Fill every element of `out` with `v` (row-major odometer over its dims).
fn fill_output<T: Scalar, Out: NDIndex<T> + ?Sized>(out: &mut Out, v: T) {
    let nd = out.ndim();
    let mut ix = vec![0usize; nd];
    for ax in 0..nd {
        if out.dim(ax) == 0 {
            return; // no elements
        }
    }
    loop {
        out.set(&ix[..nd], v);
        let mut ax = nd;
        loop {
            if ax == 0 {
                return;
            }
            ax -= 1;
            ix[ax] += 1;
            if ix[ax] < out.dim(ax) {
                break;
            }
            ix[ax] = 0;
        }
    }
}

/// Generic einsum wrapper — accepts both concrete inputs (`&[&Csr]`,
/// `&[&Dense]`, etc.) and trait objects (`&[&dyn NDIndex<T>]`). The
/// `?Sized` bound on `In`/`Out` is what makes `dyn` types valid here.
///
/// This is the function [`einsum`] forwards to — it's also the right
/// choice if you have a concrete type but don't care to declare intent
/// as strict-monomorphic via [`einsum_homogenous`].
pub fn einsum_dyn<T: Scalar, In: NDIndex<T> + ?Sized, Out: NDIndex<T> + ?Sized>(
    spec: &str,
    inputs: &[&In],
    outs: &mut [&mut Out],
) -> Result<(), InvalidSpec> {
    einsum_impl::<T, In, Out>(spec, Reduce::Sum, Combine::Mul, inputs, outs, false)
}

/// [`einsum_reduce`] generalized over the input/output types — accepts both
/// concrete tensors and `&dyn NDIndex<T>` trait objects, mirroring
/// [`einsum_dyn`]. Outputs are pre-filled with the reduction identity.
pub fn einsum_reduce_dyn<T: Scalar, In: NDIndex<T> + ?Sized, Out: NDIndex<T> + ?Sized>(
    spec: &str,
    reduce: Reduce,
    combine: Combine,
    inputs: &[&In],
    outs: &mut [&mut Out],
) -> Result<(), InvalidSpec> {
    einsum_impl::<T, In, Out>(spec, reduce, combine, inputs, outs, true)
}

/// Shared compile + validate + (optionally identity-fill) + exec body.
///
/// `fill` distinguishes the two output conventions: the plain einsum entry
/// points accumulate into caller-prepared (zeroed) outputs, while the
/// `einsum_reduce` entry points overwrite by pre-filling with the reduce
/// identity.
fn einsum_impl<T: Scalar, In: NDIndex<T> + ?Sized, Out: NDIndex<T> + ?Sized>(
    spec: &str,
    reduce: Reduce,
    combine: Combine,
    inputs: &[&In],
    outs: &mut [&mut Out],
    fill: bool,
) -> Result<(), InvalidSpec> {
    let program = compile_reduce::<T, In>(spec, reduce, combine, inputs)?;

    // Validate output shapes against the parsed spec.
    let spec = parse_spec(spec, inputs.len())?;
    let mut dims = [0usize; 26];
    for (pi, inp_spec) in spec.inputs.iter().enumerate() {
        for (pos, &s) in inp_spec.iter().enumerate() {
            dims[s as usize] = inputs[pi].dim(pos);
        }
    }
    if outs.len() != spec.outputs.len() {
        return Err(InvalidSpec::WrongInputCount {
            expected: spec.outputs.len(),
            got: outs.len(),
        });
    }
    for (oi, out_spec) in spec.outputs.iter().enumerate() {
        validate_output::<T, Out>(out_spec, &dims, &*outs[oi])?;
    }

    if fill {
        for out in outs.iter_mut() {
            fill_output::<T, Out>(&mut **out, reduce.identity());
        }
    }

    program.exec::<T, In, Out>(inputs, outs);
    Ok(())
}

/// Monomorphic einsum — all inputs are the same concrete type `In`, all
/// outputs the same concrete type `Out`. The `Sized` bound rules out
/// `dyn NDIndex<T>`, so the compiler is free to inline every NDIndex
/// call site (no vtable on `get_opt`/`set`).
///
/// Sparse loops still pay one vtable per `row_nnz`/`row_entry` because
/// `as_sparse_2d` returns `&dyn Sparse2D<T>`; if you need a fully
/// vtable-free sparse path, write a specialised SpGEMM by hand
/// (e.g. [`crate::csr::Csr::matmul`]).
///
/// # Example (requires the `dense` feature)
///
/// ```
/// # #[cfg(not(feature = "dense"))] fn main() {}
/// # #[cfg(feature = "dense")] fn main() {
/// use linalg::einsum::einsum_homogenous;
/// use linalg::dense::Dense;
/// use linalg::tensor::NDIndex;
///
/// let mut a = Dense::<f32>::zeros(vec![2, 3]);
/// a.fill_from(&[1., 2., 3., 4., 5., 6.]);
/// let mut b = Dense::<f32>::zeros(vec![3, 2]);
/// b.fill_from(&[7., 8., 9., 10., 11., 12.]);
/// let mut c = Dense::<f32>::zeros(vec![2, 2]);
///
/// einsum_homogenous::<f32, _, _>("ab,bc->ac", &[&a, &b], &mut [&mut c]).unwrap();
/// assert_eq!(c.get(&[0, 0]), 58.0);
/// # }
/// ```
pub fn einsum_homogenous<T: Scalar, In: NDIndex<T>, Out: NDIndex<T>>(
    spec: &str,
    inputs: &[&In],
    outs: &mut [&mut Out],
) -> Result<(), InvalidSpec> {
    einsum_dyn::<T, In, Out>(spec, inputs, outs)
}

// ─────────────────────────────────────────────────────────────────────────
// Display
// ─────────────────────────────────────────────────────────────────────────

impl fmt::Display for Program {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Program:")?;
        writeln!(
            f,
            "  inputs:  {:?}",
            self.input_patterns
                .iter()
                .map(|p| p.iter().map(|&s| (s + b'a') as char).collect::<String>())
                .collect::<Vec<_>>()
        )?;
        writeln!(
            f,
            "  outputs: {:?}",
            self.output_patterns
                .iter()
                .map(|p| p.iter().map(|&s| (s + b'a') as char).collect::<String>())
                .collect::<Vec<_>>()
        )?;
        writeln!(f, "  plan:")?;
        let mut indent = 2usize;
        for op in &self.ops {
            let pad = "  ".repeat(indent);
            match op {
                VmOp::DenseLoop { slot, dim, fused, .. } => {
                    let ch = (slot + b'a') as char;
                    let tag = if *fused { "  [FUSED]" } else { "" };
                    writeln!(f, "{pad}FOR {ch} IN 0..{dim}{tag}")?;
                    indent += 1;
                }
                VmOp::SparseRowLoop { input_idx, leading, col_slot, fused, .. } => {
                    let row_str: String = leading.iter().map(|&s| (s + b'a') as char).collect();
                    let col_ch = (col_slot + b'a') as char;
                    let tag = if *fused { "  [SPARSE,FUSED]" } else { "  [SPARSE]" };
                    writeln!(
                        f,
                        "{pad}FOR ({col_ch}, val) IN input[{input_idx}].row({row_str}){tag}"
                    )?;
                    indent += 1;
                }
                VmOp::LoopEnd => {
                    if indent > 0 {
                        indent -= 1;
                    }
                }
                VmOp::AccStart { acc_slot, dim, .. } => {
                    let ch = (acc_slot + b'a') as char;
                    writeln!(f, "{pad}ACC_START {ch}[0..{dim}]")?;
                }
                VmOp::AccFlush => writeln!(f, "{pad}ACC_FLUSH -> output")?,
                VmOp::MulAcc => writeln!(f, "{pad}MUL_ACC -> acc")?,
            }
        }
        Ok(())
    }
}

// ─────────────────────────────────────────────────────────────────────────
// Tests
// ─────────────────────────────────────────────────────────────────────────

#[cfg(all(test, feature = "dense"))]
mod tests {
    use super::*;
    use crate::dense::Dense;

    #[test]
    fn matmul_dense_dense() {
        let mut a = Dense::<f32>::zeros(vec![2, 3]);
        a.fill_from(&[1., 2., 3., 4., 5., 6.]);
        let mut b = Dense::<f32>::zeros(vec![3, 2]);
        b.fill_from(&[7., 8., 9., 10., 11., 12.]);
        let mut c = Dense::<f32>::zeros(vec![2, 2]);
        einsum_homogenous::<f32, _, _>("ab,bc->ac", &[&a, &b], &mut [&mut c]).unwrap();
        assert_eq!(c.data, vec![58., 64., 139., 154.]);
    }

    #[test]
    fn transpose() {
        let mut a = Dense::<f32>::zeros(vec![2, 3]);
        a.fill_from(&[1., 2., 3., 4., 5., 6.]);
        let mut t = Dense::<f32>::zeros(vec![3, 2]);
        einsum_homogenous::<f32, _, _>("ab->ba", &[&a], &mut [&mut t]).unwrap();
        assert_eq!(t.data, vec![1., 4., 2., 5., 3., 6.]);
    }

    #[test]
    fn dot_to_scalar() {
        let mut a = Dense::<f32>::zeros(vec![4]);
        a.fill_from(&[1., 2., 3., 4.]);
        let mut b = Dense::<f32>::zeros(vec![4]);
        b.fill_from(&[5., 6., 7., 8.]);
        let mut s = Dense::<f32>::zeros(vec![]);
        einsum_homogenous::<f32, _, _>("i,i->", &[&a, &b], &mut [&mut s]).unwrap();
        assert_eq!(s.get(&[]), 70.0);
    }

    #[test]
    fn three_input_chain() {
        let mut a = Dense::<f32>::zeros(vec![2, 3]);
        a.fill_from(&[1., 2., 3., 4., 5., 6.]);
        let mut b = Dense::<f32>::zeros(vec![3, 4]);
        b.fill_from(&[
            1., 0., 0., 0., 0., 1., 0., 0., 0., 0., 1., 0.,
        ]);
        let mut c = Dense::<f32>::zeros(vec![4, 2]);
        c.fill_from(&[1., 2., 3., 4., 5., 6., 7., 8.]);
        let mut d = Dense::<f32>::zeros(vec![2, 2]);
        einsum_homogenous::<f32, _, _>("ab,bc,cd->ad", &[&a, &b, &c], &mut [&mut d]).unwrap();
        // AB = [[1,2,3,0],[4,5,6,0]], then ABC = [[22,28],[49,64]]
        assert_eq!(d.data, vec![22., 28., 49., 64.]);
    }

    #[test]
    fn multi_output() {
        let mut a = Dense::<f32>::zeros(vec![2, 2]);
        a.fill_from(&[1., 2., 3., 4.]);
        let mut b = Dense::<f32>::zeros(vec![2, 2]);
        b.fill_from(&[5., 6., 7., 8.]);

        let mut ac = Dense::<f32>::zeros(vec![2, 2]);
        let mut ca = Dense::<f32>::zeros(vec![2, 2]);
        einsum::<f32>(
            "ab,bc->ac,ca",
            &[&a as &dyn NDIndex<f32>, &b],
            &mut [&mut ac as &mut dyn NDIndex<f32>, &mut ca],
        )
        .unwrap();
        // AB = [[19,22],[43,50]]
        assert_eq!(ac.data, vec![19., 22., 43., 50.]);
        assert_eq!(ca.data, vec![19., 43., 22., 50.]);
    }

    #[test]
    fn errors() {
        let a = Dense::<f32>::zeros(vec![2, 3]);
        let b = Dense::<f32>::zeros(vec![3, 2]);
        let mut c = Dense::<f32>::zeros(vec![2, 2]);
        assert_eq!(
            einsum_homogenous::<f32, _, _>("ab,bc", &[&a, &b], &mut [&mut c]).unwrap_err(),
            InvalidSpec::MissingArrow,
        );
        assert_eq!(
            einsum_homogenous::<f32, _, _>("ab,bc->az", &[&a, &b], &mut [&mut c]).unwrap_err(),
            InvalidSpec::UnboundOutputIndex { index: 'z' },
        );
    }

    /// Naive semiring reference: iterate the full cartesian index space.
    fn naive_reduce(
        spec: &str,
        reduce: Reduce,
        combine: Combine,
        inputs: &[&Dense<f32>],
        dims: &[usize; 26],
        out_shape: Vec<usize>,
    ) -> Dense<f32> {
        let parsed = parse_spec(spec, inputs.len()).unwrap();
        let mut slots = Vec::new();
        let mut seen = [false; 26];
        for pat in &parsed.inputs {
            for &s in pat {
                if !seen[s as usize] {
                    seen[s as usize] = true;
                    slots.push(s);
                }
            }
        }
        let mut out = Dense::<f32>::zeros(out_shape);
        let ident = reduce.identity::<f32>();
        for v in out.data.iter_mut() {
            *v = ident;
        }
        let n_tuples: usize = slots.iter().map(|&s| dims[s as usize]).product();
        let mut vals = [0usize; 26];
        for mut t in 0..n_tuples {
            for &s in slots.iter().rev() {
                vals[s as usize] = t % dims[s as usize];
                t /= dims[s as usize];
            }
            let mut contrib: Option<f32> = None;
            for (pat, inp) in parsed.inputs.iter().zip(inputs) {
                let ix: Vec<usize> = pat.iter().map(|&s| vals[s as usize]).collect();
                let v = inp.get(&ix);
                contrib = Some(match contrib {
                    Some(p) => combine.apply(p, v),
                    None => v,
                });
            }
            let ix: Vec<usize> =
                parsed.outputs[0].iter().map(|&s| vals[s as usize]).collect();
            let cur = out.get(&ix);
            out.set(&ix, reduce.apply(cur, contrib.unwrap()));
        }
        out
    }

    #[test]
    fn tullio_example_max_product() {
        // A[i,j,k] = max_q B[j] * C[i,k,q] * D[k,q]
        // (Tullio: @tullio (max) A[i,j,k] := B[j] * C[i,k,q] * D[k,q])
        let (di, dj, dk, dq) = (2usize, 3usize, 2usize, 4usize);
        let mut dims = [0usize; 26];
        dims[(b'i' - b'a') as usize] = di;
        dims[(b'j' - b'a') as usize] = dj;
        dims[(b'k' - b'a') as usize] = dk;
        dims[(b'q' - b'a') as usize] = dq;

        // Deterministic small ints of mixed sign (0 included).
        let fill = |d: &mut Dense<f32>, seed: u64| {
            let mut x = seed;
            for v in d.data.iter_mut() {
                x = x.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
                *v = ((x >> 33) % 5) as f32 - 2.0;
            }
        };
        let mut b = Dense::<f32>::zeros(vec![dj]);
        let mut c = Dense::<f32>::zeros(vec![di, dk, dq]);
        let mut d = Dense::<f32>::zeros(vec![dk, dq]);
        fill(&mut b, 1);
        fill(&mut c, 2);
        fill(&mut d, 3);

        let mut a = Dense::<f32>::zeros(vec![di, dj, dk]);
        einsum_reduce::<f32>(
            "j,ikq,kq->ijk",
            Reduce::Max,
            Combine::Mul,
            &[&b as &dyn NDIndex<f32>, &c, &d],
            &mut [&mut a as &mut dyn NDIndex<f32>],
        )
        .unwrap();

        let expect = naive_reduce(
            "j,ikq,kq->ijk",
            Reduce::Max,
            Combine::Mul,
            &[&b, &c, &d],
            &dims,
            vec![di, dj, dk],
        );
        assert_eq!(a.data, expect.data);
    }

    #[test]
    fn min_plus_shortest_path_step() {
        // Tropical semiring: D[i,k] = min_j (A[i,j] + B[j,k]).
        let mut a = Dense::<f32>::zeros(vec![2, 2]);
        a.fill_from(&[0., 3., 7., 0.]);
        let mut b = Dense::<f32>::zeros(vec![2, 2]);
        b.fill_from(&[0., 4., 1., 0.]);
        let mut d = Dense::<f32>::zeros(vec![2, 2]);
        einsum_reduce::<f32>(
            "ij,jk->ik",
            Reduce::Min,
            Combine::Add,
            &[&a as &dyn NDIndex<f32>, &b],
            &mut [&mut d as &mut dyn NDIndex<f32>],
        )
        .unwrap();
        // d[0][1] = min(0+4, 3+0) = 3; d[1][0] = min(7+0, 0+1) = 1.
        assert_eq!(d.data, vec![0., 3., 1., 0.]);
    }

    #[test]
    fn prod_reduction() {
        let mut a = Dense::<f32>::zeros(vec![2, 3]);
        a.fill_from(&[1., 2., 3., 4., 5., 6.]);
        let mut p = Dense::<f32>::zeros(vec![2]);
        einsum_reduce::<f32>(
            "ij->i",
            Reduce::Prod,
            Combine::Mul,
            &[&a as &dyn NDIndex<f32>],
            &mut [&mut p as &mut dyn NDIndex<f32>],
        )
        .unwrap();
        assert_eq!(p.data, vec![6., 120.]);
    }

    #[test]
    fn empty_reduction_yields_identity() {
        let a = Dense::<f32>::zeros(vec![2, 0]);
        let mut m = Dense::<f32>::zeros(vec![2]);
        einsum_reduce::<f32>(
            "iq->i",
            Reduce::Max,
            Combine::Mul,
            &[&a as &dyn NDIndex<f32>],
            &mut [&mut m as &mut dyn NDIndex<f32>],
        )
        .unwrap();
        assert_eq!(m.data, vec![f32::NEG_INFINITY; 2]);
    }

    #[test]
    fn max_with_accumulator_flush_path() {
        // "acd->cd" triggers the AccFlush RMW edge (contracted `a` sits
        // outside the accumulator scope) — the flush must fold with max,
        // not overwrite or add.
        let mut dims = [0usize; 26];
        dims[0] = 3; // a
        dims[2] = 2; // c
        dims[3] = 4; // d
        let mut x = Dense::<f32>::zeros(vec![3, 2, 4]);
        let mut s = 7u64;
        for v in x.data.iter_mut() {
            s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            *v = ((s >> 33) % 7) as f32 - 3.0;
        }
        let mut got = Dense::<f32>::zeros(vec![2, 4]);
        einsum_reduce::<f32>(
            "acd->cd",
            Reduce::Max,
            Combine::Mul,
            &[&x as &dyn NDIndex<f32>],
            &mut [&mut got as &mut dyn NDIndex<f32>],
        )
        .unwrap();
        let expect =
            naive_reduce("acd->cd", Reduce::Max, Combine::Mul, &[&x], &dims, vec![2, 4]);
        assert_eq!(got.data, expect.data);
    }

    #[test]
    fn integer_max_uses_type_min_identity() {
        // All-negative integers: a zero-seeded accumulator would wrongly
        // return 0; the identity must be i32::MIN.
        let mut a = Dense::<i32>::zeros(vec![2, 2]);
        a.fill_from(&[-5, -3, -9, -1]);
        let mut m = Dense::<i32>::zeros(vec![2]);
        einsum_reduce::<i32>(
            "ij->i",
            Reduce::Max,
            Combine::Mul,
            &[&a as &dyn NDIndex<i32>],
            &mut [&mut m as &mut dyn NDIndex<i32>],
        )
        .unwrap();
        assert_eq!(m.data, vec![-3, -1]);
    }

    #[test]
    fn sum_mul_reduce_matches_plain_einsum() {
        let mut a = Dense::<f32>::zeros(vec![2, 3]);
        a.fill_from(&[1., 2., 3., 4., 5., 6.]);
        let mut b = Dense::<f32>::zeros(vec![3, 2]);
        b.fill_from(&[7., 8., 9., 10., 11., 12.]);
        let mut c = Dense::<f32>::zeros(vec![2, 2]);
        einsum_reduce::<f32>(
            "ab,bc->ac",
            Reduce::Sum,
            Combine::Mul,
            &[&a as &dyn NDIndex<f32>, &b],
            &mut [&mut c as &mut dyn NDIndex<f32>],
        )
        .unwrap();
        assert_eq!(c.data, vec![58., 64., 139., 154.]);
    }

    #[cfg(feature = "csr")]
    #[test]
    fn sparse_input_with_max_iterates_densely() {
        use crate::csr::Csr;

        // Sparse input with negative stored values: the structural zeros
        // must compete in the max (0 > negative products), so the plan may
        // not skip them via a sparse row loop.
        let a = Csr::<u32, f32>::from_parts(
            vec![2, 3],
            vec![0, 2, 3],
            vec![1, 2, 0],
            vec![-2.0, -3.0, -1.0],
        );
        let mut a_dense = Dense::<f32>::zeros(vec![2, 3]);
        a_dense.fill_from(&[0., -2., -3., -1., 0., 0.]);
        let mut b = Dense::<f32>::zeros(vec![3, 2]);
        b.fill_from(&[1., -2., 3., 4., -5., 6.]);

        let prog = compile_reduce::<f32, dyn NDIndex<f32>>(
            "ab,bc->ac",
            Reduce::Max,
            Combine::Mul,
            &[&a as &dyn NDIndex<f32>, &b],
        )
        .unwrap();
        let plan = format!("{prog}");
        assert!(!plan.contains("[SPARSE"), "max must not use sparse skipping:\n{plan}");

        let mut got = Dense::<f32>::zeros(vec![2, 2]);
        einsum_reduce::<f32>(
            "ab,bc->ac",
            Reduce::Max,
            Combine::Mul,
            &[&a as &dyn NDIndex<f32>, &b],
            &mut [&mut got as &mut dyn NDIndex<f32>],
        )
        .unwrap();

        let mut dims = [0usize; 26];
        dims[0] = 2;
        dims[1] = 3;
        dims[2] = 2;
        let expect = naive_reduce(
            "ab,bc->ac",
            Reduce::Max,
            Combine::Mul,
            &[&a_dense, &b],
            &dims,
            vec![2, 2],
        );
        assert_eq!(got.data, expect.data);
    }

    #[cfg(feature = "csr")]
    #[test]
    fn batched_sparse_uses_compound_row_loop() {
        use crate::csr::Csr;

        // 3D sparse A "bij" [2,2,2]; dense B "bjk" [2,2,3]; out "bik".
        let a = Csr::<u32, f32>::from_parts(
            vec![2, 2, 2],
            vec![0, 2, 3, 4, 5],
            vec![0, 1, 1, 0, 0],
            vec![1.0, 2.0, 3.0, 4.0, 5.0],
        );
        let mut a_dense = Dense::<f32>::zeros(vec![2, 2, 2]);
        a_dense.fill_from(&[1., 2., 0., 3., 4., 0., 5., 0.]);
        let mut bb = Dense::<f32>::zeros(vec![2, 2, 3]);
        bb.fill_from(&[1., 2., 3., 4., 5., 6., 7., 8., 9., 10., 11., 12.]);

        // The plan walks the sparse compound (b, i) row, not a get_opt fallback.
        let prog =
            compile::<f32, dyn NDIndex<f32>>("bij,bjk->bik", &[&a as &dyn NDIndex<f32>, &bb])
                .unwrap();
        let plan = format!("{prog}");
        assert!(plan.contains("[SPARSE]"), "expected a sparse loop:\n{plan}");
        assert!(plan.contains(".row(bi)"), "expected compound (b,i) row:\n{plan}");

        // Result matches the all-dense VM.
        let mut out_sp = Dense::<f32>::zeros(vec![2, 2, 3]);
        einsum::<f32>(
            "bij,bjk->bik",
            &[&a as &dyn NDIndex<f32>, &bb],
            &mut [&mut out_sp as &mut dyn NDIndex<f32>],
        )
        .unwrap();

        let mut out_de = Dense::<f32>::zeros(vec![2, 2, 3]);
        einsum_homogenous::<f32, _, _>("bij,bjk->bik", &[&a_dense, &bb], &mut [&mut out_de])
            .unwrap();

        assert_eq!(out_sp.data, out_de.data);
        // Spot value: out[0,1,:] = 3 * B[0,1,:] = [12,15,18].
        assert_eq!(&out_sp.data[3..6], &[12., 15., 18.]);
    }

    #[cfg(feature = "csr")]
    #[test]
    fn rectangular_sparse_via_vm() {
        use crate::csr::Csr;

        // Non-square sparse A (2×3) times dense X (3×4).
        let a = Csr::<u32, f32>::from_parts(vec![2, 3], vec![0, 2, 3], vec![1, 2, 0], vec![2.0, 3.0, 1.0]);
        let mut a_dense = Dense::<f32>::zeros(vec![2, 3]);
        a_dense.fill_from(&[0., 2., 3., 1., 0., 0.]);
        let mut x = Dense::<f32>::zeros(vec![3, 4]);
        x.fill_from(&[1., 2., 3., 4., 5., 6., 7., 8., 9., 10., 11., 12.]);

        let mut out_sp = Dense::<f32>::zeros(vec![2, 4]);
        einsum::<f32>(
            "ab,bc->ac",
            &[&a as &dyn NDIndex<f32>, &x],
            &mut [&mut out_sp as &mut dyn NDIndex<f32>],
        )
        .unwrap();

        let mut out_de = Dense::<f32>::zeros(vec![2, 4]);
        einsum_homogenous::<f32, _, _>("ab,bc->ac", &[&a_dense, &x], &mut [&mut out_de]).unwrap();

        assert_eq!(out_sp.data, out_de.data);
    }
}
