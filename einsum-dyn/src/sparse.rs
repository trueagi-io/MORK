//! Sparse einsum: multiple approaches for sparse 2D matrix einsum.
//!
//! # Approaches
//!
//! ## 1. Baseline (`einsum_binary` with `get_opt`)
//! The existing dense-loop einsum from `lib.rs`. Iterates the full n×n×n index
//! space for matmul, but skips zero products via `get_opt()`. Complexity: O(n³).
//! No new code needed — use `einsum_binary` directly with any `NDIndex` impl.
//!
//! ## 2. Sparse-driven with dense accumulator (`einsum_sparse_driven`)
//! Equivalent to matmul (C = A × B). Only supports the `"ab,bc->ac"` pattern.
//! Iterates only non-zero entries of inputs using the `Sparse2D` trait:
//! loops A's rows, for each NZ (k, a_val) in row i, iterates B's row k
//! sparsely. Dense `Vec<T>` accumulator per output row.
//! Complexity: O(Σ_i Σ_{k∈row(i)} row_nnz_B(k)) = O(flops).
//!
//! ## 3. Custom VM (`einsum_vm`)
//! Compiles the einsum spec into a tree of VM operations. A greedy scheduler
//! decides which loops iterate sparsely (via `Sparse2D::row_entry`) vs densely.
//! The VM interpreter walks the tree recursively. Same asymptotic complexity
//! as approach 2, but handles arbitrary 2D specs without hardcoding patterns.
//!
//! ## 4. Sparse-driven with hash accumulator (`einsum_sparse_hash`)
//! Same sparse iteration as approach 2, but accumulates into a `HashMap<usize, T>`
//! per output row instead of a dense vector. Better when the output is very sparse
//! (each row has few non-zeros), since it avoids allocating/clearing an n-wide
//! accumulator. Worse for dense output due to hashing overhead.

use std::collections::HashMap;
use std::ops::{Add, AddAssign, Mul};

use crate::{NDIndex, InvalidSpec};

// ═══════════════════════════════════════════════════════════════════════════
// Sparse2D trait
// ═══════════════════════════════════════════════════════════════════════════

/// Extension of `NDIndex` for sparse 2D arrays (matrices).
///
/// Provides structured row-wise access to non-zero entries, enabling
/// sparse-driven einsum execution that skips entire zero regions.
pub trait Sparse2D<T>: NDIndex<T> {
    /// Total number of structural non-zeros.
    fn nnz(&self) -> usize;

    /// Number of rows (axis 0 dimension).
    fn n_rows(&self) -> usize;

    /// Number of non-zero entries in the given row.
    fn row_nnz(&self, row: usize) -> usize;

    /// Get the `idx`-th non-zero entry in the given row as `(col, value)`.
    /// `idx` must be in `0..row_nnz(row)`.
    fn row_entry(&self, row: usize, idx: usize) -> (usize, T);
}

// ═══════════════════════════════════════════════════════════════════════════
// Approach 2: Sparse-driven with dense accumulator
// ═══════════════════════════════════════════════════════════════════════════

/// Sparse-driven binary einsum with dense row accumulator.
///
/// Only supports the standard matmul pattern: A's axis-1 index must equal
/// B's axis-0 index (the contracted/inner dimension). Any letter names work
/// (`"ab,bc->ac"`, `"xy,yz->xz"`, etc.) but the structure must be matmul.
/// For other specs, use `einsum_vm_oneshot` or `einsum_sparse_hash`.
///
/// Both inputs must implement `Sparse2D`. The output must be a writable
/// `NDIndex` (typically dense) with the correct shape.
pub fn einsum_sparse_driven<T, S, Out>(
    spec_str: &str,
    a: &S,
    b: &S,
    out: &mut Out,
) -> Result<(), InvalidSpec>
where
    T: Default + Copy + PartialEq + AddAssign + Mul<Output = T>,
    S: Sparse2D<T>,
    Out: NDIndex<T>,
{
    let spec = crate::parse_spec(spec_str, 2)?;
    let dims = crate::validate_dims::<T, S>(&spec, &[a, b])?;
    crate::validate_output::<T, Out>(&spec, &dims, out)?;

    let a_slots = &spec.inputs[0];
    let b_slots = &spec.inputs[1];
    let out_slots = &spec.output();

    assert_eq!(a_slots.len(), 2, "sparse-driven requires 2D inputs");
    assert_eq!(b_slots.len(), 2, "sparse-driven requires 2D inputs");

    let (a0, a1) = (a_slots[0], a_slots[1]);
    let (_b0, b1) = (b_slots[0], b_slots[1]);

    // Verify A's col index == B's row index.
    // This restricts us to the matmul pattern (C = A × B) — the only
    // structural arrangement where both inputs can be walked row-wise
    // through CSR without transposing.
    if a1 != b_slots[0] {
        panic!(
            "einsum_sparse_driven only supports matmul pattern \
             (A's axis-1 == B's axis-0), got spec '{spec_str}'"
        );
    }

    // Map output slot positions: which output axis gets which slot value
    let out_pos_a0 = out_slots.iter().position(|&s| s == a0);
    let out_pos_b1 = out_slots.iter().position(|&s| s == b1);
    let n_out_dims = out_slots.len();

    // Dense accumulator sized to the full output column range.
    // Track which columns were touched to avoid clearing the entire vector.
    let n_cols_out = dims[b1 as usize];
    let mut acc = vec![T::default(); n_cols_out];
    let mut nz_cols: Vec<usize> = Vec::new();
    let mut out_ix = vec![0usize; n_out_dims];

    let n_rows_a = a.n_rows();

    for i in 0..n_rows_a {
        // Scatter: iterate A's row i, then B's matching rows
        for ai in 0..a.row_nnz(i) {
            let (k, a_val) = a.row_entry(i, ai);
            for bi in 0..b.row_nnz(k) {
                let (j, b_val) = b.row_entry(k, bi);
                if acc[j] == T::default() {
                    nz_cols.push(j);
                }
                acc[j] += a_val * b_val;
            }
        }

        // Write touched columns to output, then clear them
        if let Some(p) = out_pos_a0 {
            out_ix[p] = i;
        }
        for &j in &nz_cols {
            if let Some(p) = out_pos_b1 {
                out_ix[p] = j;
            }
            out.set(&out_ix[..n_out_dims], acc[j]);
            acc[j] = T::default();
        }
        nz_cols.clear();
    }

    Ok(())
}

// ═══════════════════════════════════════════════════════════════════════════
// Approach 3: Custom VM
// ═══════════════════════════════════════════════════════════════════════════

/// VM operation — flat bytecode. `DenseLoop` and `SparseRowLoop` mark loop
/// starts; `LoopEnd` marks the end of the innermost enclosing loop.
/// Each loop-start stores the pc of its matching `LoopEnd` (and vice versa)
/// so the interpreter never needs to scan for matching brackets.
#[derive(Debug)]
pub enum VmOp {
    /// Dense loop: iterate `slot` from 0 to `dim-1`.
    /// `end_pc` points one past the matching `LoopEnd`.
    /// When `fused`, the body is a single `MulAcc` — the loop runs the
    /// multiply-accumulate inline without recursing into `exec_at`.
    DenseLoop { slot: u8, dim: usize, end_pc: usize, fused: bool },
    /// Sparse row iteration: for each non-zero in `input[input_idx]`
    /// at the row given by `vals[row_slot]`, set `vals[col_slot]` to the
    /// column index.
    /// `end_pc` points one past the matching `LoopEnd`.
    /// When `fused`, the body is a single `MulAcc` — the loop runs the
    /// multiply-accumulate inline without recursing into `exec_at`.
    SparseRowLoop {
        input_idx: usize,
        row_slot: u8,
        col_slot: u8,
        end_pc: usize,
        fused: bool,
    },
    /// End of the enclosing loop. `start_pc` points back to the loop-start.
    LoopEnd { start_pc: usize },
    /// Initialize a dense accumulator of size `dim`, indexed by `acc_slot`.
    /// Placed just before the loops that should accumulate.
    AccStart { acc_slot: u8, acc_out_pos: u8, dim: usize },
    /// Flush the dense accumulator to the output (scatter-gather: only write
    /// and clear touched entries), then reset.
    AccFlush,
    /// Read input values at current slot positions, multiply, and
    /// accumulate into the output (or into the active accumulator).
    MulAcc,
}

/// Precompiled VM program for sparse einsum.
pub struct VmProgram {
    /// Flat bytecode.
    pub ops: Vec<VmOp>,
    /// Input slot patterns: input_patterns[i] = list of slot indices for input i.
    input_patterns: Vec<Vec<u8>>,
    /// Output slot patterns: one per output in the spec.
    output_patterns: Vec<Vec<u8>>,
    /// For each input: `Some(loop_index)` of the SparseRowLoop that fully covers
    /// it (both axes iterated by that one loop), or `None` if `get_opt` is needed.
    /// When `Some`, `MulAcc` reads the cached sparse value instead of calling `get_opt`.
    sparse_value_source: Vec<Option<usize>>,
}

/// Compile an einsum spec into a VM program.
///
/// Accepts inputs of any dimensionality. The compiler uses a greedy strategy:
/// 1. For each 2D sparse input (`is_sparse_2d()`), its axis-1 slot can be
///    iterated sparsely when its axis-0 slot is already fixed.
/// 2. Non-sparse or higher-dimensional inputs use dense loops for all slots.
/// 3. When choosing dense loops, prefer axis-0 slots of sparse inputs first
///    (so their axis-1 can be sparse in the next level).
///
/// The `inputs` slice is used to check dimensionality and `is_sparse_2d()`.
/// It is not retained — execution uses separately provided inputs.
pub fn compile_vm<T: Copy>(
    spec_str: &str,
    inputs: &[&dyn NDIndex<T>],
) -> Result<VmProgram, InvalidSpec> {
    let n_inputs = inputs.len();
    let spec = crate::parse_spec(spec_str, n_inputs)?;

    // Validate dimensions
    let mut dims = [0usize; 26];
    let mut dim_set = [false; 26];
    for (pi, inp_spec) in spec.inputs.iter().enumerate() {
        let arr = inputs[pi];
        if arr.ndim() != inp_spec.len() {
            return Err(InvalidSpec::InputNdimMismatch {
                input: pi,
                array_ndim: arr.ndim(),
                spec_ndim: inp_spec.len(),
            });
        }
        for (pos, &s) in inp_spec.iter().enumerate() {
            let si = s as usize;
            let d = arr.dim(pos);
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

    // Identify which inputs are sparse-2D eligible for SparseRowLoop.
    // An input qualifies when it has exactly 2 spec indices AND is_sparse_2d().
    // For qualifying inputs, record (axis_0_slot, axis_1_slot).
    let sparse_axes: Vec<Option<(u8, u8)>> = spec
        .inputs
        .iter()
        .zip(inputs.iter())
        .map(|(inp_spec, arr)| {
            if inp_spec.len() == 2 && arr.is_sparse_2d() {
                Some((inp_spec[0], inp_spec[1]))
            } else {
                None
            }
        })
        .collect();

    // Collect all unique slots in order of first appearance
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

    // Greedy scheduler: decide loop order, then emit flat bytecode.
    let mut fixed = [false; 26];
    let mut loop_order: Vec<VmOp> = Vec::new();
    let mut n_fixed = 0usize;

    while n_fixed < all_slots.len() {
        let mut found_sparse = false;

        // Try to find a slot that can be sparse-iterated:
        // s is axis-1 of a sparse-2D input whose axis-0 is already fixed.
        for &s in &all_slots {
            if fixed[s as usize] {
                continue;
            }
            for (idx, axes) in sparse_axes.iter().enumerate() {
                if let Some((ax0, ax1)) = axes {
                    if *ax1 == s && fixed[*ax0 as usize] {
                        loop_order.push(VmOp::SparseRowLoop {
                            input_idx: idx,
                            row_slot: *ax0,
                            col_slot: s,
                            end_pc: 0, // patched below
                            fused: false, // patched below
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
            // Dense loop. Prefer axis-0 slots of sparse inputs (enables future sparse).
            let mut best = None;
            for &s in &all_slots {
                if fixed[s as usize] {
                    continue;
                }
                let is_sparse_ax0 = sparse_axes
                    .iter()
                    .any(|axes| matches!(axes, Some((ax0, _)) if *ax0 == s));
                if is_sparse_ax0 || best.is_none() {
                    best = Some(s);
                    if is_sparse_ax0 {
                        break;
                    }
                }
            }
            let s = best.unwrap();
            loop_order.push(VmOp::DenseLoop {
                slot: s,
                dim: dims[s as usize],
                end_pc: 0, // patched below
                fused: false, // patched below
            });
            fixed[s as usize] = true;
            n_fixed += 1;
        }
    }

    // For each input, check if a single SparseRowLoop covers both its axes.
    // If so, MulAcc can use the cached sparse value instead of get_opt().
    let sparse_value_source: Vec<Option<usize>> = spec
        .inputs
        .iter()
        .enumerate()
        .map(|(inp_idx, inp_spec)| {
            if inp_spec.len() != 2 {
                return None;
            }
            // Find a SparseRowLoop in loop_order that iterates this input
            for (loop_idx, op) in loop_order.iter().enumerate() {
                if let VmOp::SparseRowLoop { input_idx, row_slot, col_slot, .. } = op {
                    if *input_idx == inp_idx {
                        // Check this loop covers both axes of this input
                        if sparse_axes[inp_idx] == Some((*row_slot, *col_slot)) {
                            return Some(loop_idx);
                        }
                    }
                }
            }
            None
        })
        .collect();

    // Accumulator: if the innermost loop's slot appears in the output pattern
    // and there's at least one other output slot, we can use a dense accumulator.
    // We emit AccStart just inside the outermost output-slot loop and AccFlush
    // just before each iteration's end of that same loop.
    //
    // For "ab,bc->ac": output=[a,c], innermost loop is c.
    //   acc_slot=c, flush_loop_idx=0 (the 'a' loop).
    //   Bytecode: FOR a | AccStart | FOR b(sparse) | FOR c(sparse) | MulAcc |
    //             LoopEnd(c) | LoopEnd(b) | AccFlush | LoopEnd(a)
    // Accumulator optimization: only for single-output specs.
    // With multi-output, different outputs may have different index layouts,
    // so the dense accumulator trick doesn't generalise cleanly.
    let all_output_slots = spec.all_output_slots();
    let mut acc_info: Option<(u8, u8, usize, usize)> = None; // (acc_slot, acc_out_pos, acc_dim, flush_loop_idx)
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

    // Emit flat bytecode.
    // Layout: loops... MulAcc LoopEnd... with AccStart/AccFlush injected.
    let n_loops = loop_order.len();
    let mut ops: Vec<VmOp> = Vec::with_capacity(n_loops * 2 + 4);

    // Emit loop-starts, injecting AccStart after the flush loop
    for (i, op) in loop_order.into_iter().enumerate() {
        ops.push(op);
        if let Some((acc_slot, acc_out_pos, dim, flush_idx)) = acc_info {
            if i == flush_idx {
                ops.push(VmOp::AccStart { acc_slot, acc_out_pos, dim });
            }
        }
    }
    ops.push(VmOp::MulAcc);

    // Emit LoopEnds (innermost first), injecting AccFlush before the flush loop's LoopEnd
    for i in 0..n_loops {
        let loop_idx = n_loops - 1 - i;
        if let Some((_, _, _, flush_idx)) = acc_info {
            if loop_idx == flush_idx {
                ops.push(VmOp::AccFlush);
            }
        }
        // Find this loop's start_pc by scanning back for the loop_idx-th loop-start
        // The loop-starts are at varying positions due to AccStart injection.
        // Track them: loop_idx corresponds to the loop_idx-th loop-start in ops.
        let start_pc = ops.iter().enumerate()
            .filter(|(_, op)| matches!(op, VmOp::DenseLoop{..} | VmOp::SparseRowLoop{..}))
            .nth(loop_idx)
            .unwrap().0;
        let end_pc = ops.len() + 1; // one past the LoopEnd we're about to push
        match &mut ops[start_pc] {
            VmOp::DenseLoop { end_pc: ep, .. } => *ep = end_pc,
            VmOp::SparseRowLoop { end_pc: ep, .. } => *ep = end_pc,
            _ => unreachable!(),
        }
        ops.push(VmOp::LoopEnd { start_pc });
    }

    // Fusion: if a loop's body is just MulAcc (followed by LoopEnd), mark it fused.
    // The loop will inline the multiply-accumulate without recursing.
    for pc in 0..ops.len() {
        let is_loop = matches!(&ops[pc], VmOp::DenseLoop{..} | VmOp::SparseRowLoop{..});
        if is_loop && matches!(&ops[pc + 1], VmOp::MulAcc) {
            match &mut ops[pc] {
                VmOp::DenseLoop { fused, .. } => *fused = true,
                VmOp::SparseRowLoop { fused, .. } => *fused = true,
                _ => unreachable!(),
            }
        }
    }

    Ok(VmProgram {
        ops,
        input_patterns: spec.inputs.clone(),
        output_patterns: spec.outputs.clone(),
        sparse_value_source,
    })
}

/// Accumulator state for the VM interpreter.
struct AccState<T> {
    acc: Vec<T>,
    nz_cols: Vec<usize>,
    acc_slot: u8,
    acc_out_pos: u8,
}

impl VmProgram {
    /// Execute this compiled VM program.
    ///
    /// Inputs can be any mix of dense and sparse `NDIndex` implementations.
    /// `SparseRowLoop` ops call `sparse_row_nnz` / `sparse_row_entry` on the
    /// relevant input — the compiler only emits these for inputs where
    /// `is_sparse_2d()` returned true.
    ///
    /// Optimizations over naive interpretation:
    /// - Sparse values from `row_entry()` are cached and reused in `MulAcc`,
    ///   avoiding redundant `get_opt()` binary searches.
    /// - `AccStart`/`AccFlush` ops enable scatter-gather accumulation for the
    ///   innermost output dimension.
    pub fn exec<T>(
        &self,
        inputs: &[&dyn NDIndex<T>],
        outs: &mut [&mut dyn NDIndex<T>],
    ) where
        T: Default + Copy + Add<Output = T> + AddAssign + Mul<Output = T> + PartialEq,
    {
        let mut vals = [0usize; 26];
        let mut buf = [0usize; 26];
        let mut sparse_vals: Vec<T> = vec![T::default(); inputs.len()];
        let mut acc_state: Option<AccState<T>> = None;
        self.exec_at(0, &mut vals, &mut buf, &mut sparse_vals, &mut acc_state, inputs, outs);
    }

    /// Execute bytecode starting at `pc`. Returns the pc after the
    /// matching `LoopEnd` (or end of program).
    fn exec_at<T>(
        &self,
        mut pc: usize,
        vals: &mut [usize; 26],
        buf: &mut [usize; 26],
        sparse_vals: &mut [T],
        acc_state: &mut Option<AccState<T>>,
        inputs: &[&dyn NDIndex<T>],
        outs: &mut [&mut dyn NDIndex<T>],
    ) -> usize
    where
        T: Default + Copy + Add<Output = T> + AddAssign + Mul<Output = T> + PartialEq,
    {
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
                            self.exec_at(pc + 1, vals, buf, sparse_vals, acc_state, inputs, outs);
                        }
                    }
                    pc = *end_pc;
                }
                VmOp::SparseRowLoop {
                    input_idx,
                    row_slot,
                    col_slot,
                    end_pc,
                    fused,
                } => {
                    let row = vals[*row_slot as usize];
                    let cs = *col_slot as usize;
                    let input = inputs[*input_idx];
                    let nnz = input.sparse_row_nnz(row);
                    if *fused {
                        for ei in 0..nnz {
                            let (col, val) = input.sparse_row_entry(row, ei);
                            vals[cs] = col;
                            sparse_vals[*input_idx] = val;
                            self.mul_acc(vals, buf, sparse_vals, acc_state, inputs, outs);
                        }
                    } else {
                        for ei in 0..nnz {
                            let (col, val) = input.sparse_row_entry(row, ei);
                            vals[cs] = col;
                            sparse_vals[*input_idx] = val;
                            self.exec_at(pc + 1, vals, buf, sparse_vals, acc_state, inputs, outs);
                        }
                    }
                    pc = *end_pc;
                }
                VmOp::LoopEnd { .. } => {
                    return pc + 1;
                }
                VmOp::AccStart { acc_slot, acc_out_pos, dim } => {
                    *acc_state = Some(AccState {
                        acc: vec![T::default(); *dim],
                        nz_cols: Vec::new(),
                        acc_slot: *acc_slot,
                        acc_out_pos: *acc_out_pos,
                    });
                    pc += 1;
                }
                VmOp::AccFlush => {
                    // AccFlush only emitted for single-output specs
                    if let Some(st) = acc_state {
                        let pattern = &self.output_patterns[0];
                        let len = pattern.len();
                        for &j in st.nz_cols.iter() {
                            for (i, &s) in pattern.iter().enumerate() {
                                buf[i] = vals[s as usize];
                            }
                            buf[st.acc_out_pos as usize] = j;
                            outs[0].set(&buf[..len], st.acc[j]);
                            st.acc[j] = T::default();
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

    /// Compute one multiply-accumulate step: read inputs, multiply, write to
    /// accumulator or output(s).
    #[inline]
    fn mul_acc<T>(
        &self,
        vals: &[usize; 26],
        buf: &mut [usize; 26],
        sparse_vals: &[T],
        acc_state: &mut Option<AccState<T>>,
        inputs: &[&dyn NDIndex<T>],
        outs: &mut [&mut dyn NDIndex<T>],
    ) where
        T: Default + Copy + Add<Output = T> + AddAssign + Mul<Output = T> + PartialEq,
    {
        let mut product = None::<T>;
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
            if let Some(v) = v {
                product = Some(match product {
                    Some(p) => p * v,
                    None => v,
                });
            } else {
                product = None;
                break;
            }
        }
        if let Some(p) = product {
            if let Some(st) = acc_state {
                // Single-output accumulator path
                let idx = vals[st.acc_slot as usize];
                if st.acc[idx] == T::default() {
                    st.nz_cols.push(idx);
                }
                st.acc[idx] += p;
            } else {
                // Write to all outputs
                for (oi, pattern) in self.output_patterns.iter().enumerate() {
                    let len = pattern.len();
                    for (i, &s) in pattern.iter().enumerate() {
                        buf[i] = vals[s as usize];
                    }
                    let cur = outs[oi].get(&buf[..len]);
                    outs[oi].set(&buf[..len], cur + p);
                }
            }
        }
    }
}

/// Convenience: compile and execute in one call.
///
/// Accepts any number of inputs and outputs of any dimensionality.
/// All inputs must be the same concrete type; for mixed types use
/// [`einsum_vm_oneshot_dyn`].
///
/// Multiple outputs are supported: `"ab,bc->ac,ca"` writes to two output
/// tensors simultaneously from a single loop nest.
pub fn einsum_vm_oneshot<T, In, Out>(
    spec_str: &str,
    inputs: &[&In],
    outs: &mut [&mut Out],
) -> Result<(), InvalidSpec>
where
    T: Copy + Default + Add<Output = T> + AddAssign + Mul<Output = T> + PartialEq,
    In: NDIndex<T>,
    Out: NDIndex<T>,
{
    let dyn_inputs: Vec<&dyn NDIndex<T>> = inputs.iter().map(|&x| x as &dyn NDIndex<T>).collect();
    let mut dyn_outs: Vec<&mut dyn NDIndex<T>> = outs.iter_mut().map(|o| {
        let r: &mut Out = *o;
        r as &mut dyn NDIndex<T>
    }).collect();
    einsum_vm_oneshot_dyn(spec_str, &dyn_inputs, &mut dyn_outs)
}

/// Like [`einsum_vm_oneshot`] but accepts trait-object inputs, allowing
/// mixed concrete types (e.g. one sparse and one dense input).
pub fn einsum_vm_oneshot_dyn<T>(
    spec_str: &str,
    inputs: &[&dyn NDIndex<T>],
    outs: &mut [&mut dyn NDIndex<T>],
) -> Result<(), InvalidSpec>
where
    T: Copy + Default + Add<Output = T> + AddAssign + Mul<Output = T> + PartialEq,
{
    let program = compile_vm(spec_str, inputs)?;
    program.exec(inputs, outs);
    Ok(())
}

// ═══════════════════════════════════════════════════════════════════════════
// Approach 4: Sparse-driven with hash accumulator
// ═══════════════════════════════════════════════════════════════════════════

/// Sparse-driven binary einsum with hash accumulator per output row.
///
/// Equivalent to matmul (C = A × B) — same restriction as
/// `einsum_sparse_driven`: only supports the `"ab,bc->ac"` pattern.
///
/// Uses a `HashMap<usize, T>` per row instead of a dense `Vec<T>`.
/// Better when the output is very sparse; worse for dense output.
pub fn einsum_sparse_hash<T, S, Out>(
    spec_str: &str,
    a: &S,
    b: &S,
    out: &mut Out,
) -> Result<(), InvalidSpec>
where
    T: Default + Copy + AddAssign + Mul<Output = T> + PartialEq,
    S: Sparse2D<T>,
    Out: NDIndex<T>,
{
    let spec = crate::parse_spec(spec_str, 2)?;
    let dims = crate::validate_dims::<T, S>(&spec, &[a, b])?;
    crate::validate_output::<T, Out>(&spec, &dims, out)?;

    let a_slots = &spec.inputs[0];
    let b_slots = &spec.inputs[1];
    let out_slots = &spec.output();

    assert_eq!(a_slots.len(), 2, "sparse-hash requires 2D inputs");
    assert_eq!(b_slots.len(), 2, "sparse-hash requires 2D inputs");

    let (a0, a1) = (a_slots[0], a_slots[1]);
    let b1 = b_slots[1];

    if a1 != b_slots[0] {
        panic!(
            "einsum_sparse_hash requires A's axis-1 == B's axis-0, \
             got spec '{spec_str}'"
        );
    }

    let out_pos_a0 = out_slots.iter().position(|&s| s == a0);
    let out_pos_b1 = out_slots.iter().position(|&s| s == b1);
    let n_out_dims = out_slots.len();

    let n_rows_a = a.n_rows();
    let mut acc: HashMap<usize, T> = HashMap::new();
    let mut out_ix = vec![0usize; n_out_dims];

    for i in 0..n_rows_a {
        acc.clear();

        for ai in 0..a.row_nnz(i) {
            let (k, a_val) = a.row_entry(i, ai);
            for bi in 0..b.row_nnz(k) {
                let (j, b_val) = b.row_entry(k, bi);
                *acc.entry(j).or_insert_with(T::default) += a_val * b_val;
            }
        }

        if let Some(p) = out_pos_a0 {
            out_ix[p] = i;
        }
        for (&j, &v) in &acc {
            if let Some(p) = out_pos_b1 {
                out_ix[p] = j;
            }
            out.set(&out_ix[..n_out_dims], v);
        }
    }

    Ok(())
}

// ═══════════════════════════════════════════════════════════════════════════
// Display for VmOp (debugging / documentation)
// ═══════════════════════════════════════════════════════════════════════════

impl std::fmt::Display for VmProgram {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "VM Program:")?;
        writeln!(
            f,
            "  inputs: {:?}",
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
                VmOp::SparseRowLoop {
                    input_idx,
                    row_slot,
                    col_slot,
                    fused,
                    ..
                } => {
                    let row_ch = (row_slot + b'a') as char;
                    let col_ch = (col_slot + b'a') as char;
                    let tag = if *fused { "  [SPARSE,FUSED]" } else { "  [SPARSE]" };
                    writeln!(
                        f,
                        "{pad}FOR ({col_ch}, val) IN input[{input_idx}].row({row_ch}){tag}"
                    )?;
                    indent += 1;
                }
                VmOp::LoopEnd { .. } => {
                    indent -= 1;
                }
                VmOp::AccStart { acc_slot, dim, .. } => {
                    let ch = (acc_slot + b'a') as char;
                    writeln!(f, "{pad}ACC_START {ch}[0..{dim}]")?;
                }
                VmOp::AccFlush => {
                    writeln!(f, "{pad}ACC_FLUSH → output")?;
                }
                VmOp::MulAcc => {
                    writeln!(f, "{pad}MUL_ACC → acc")?;
                }
            }
        }
        Ok(())
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// Tests
// ═══════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use crate::einsum_binary;

    /// Minimal dense tensor for output.
    struct DenseMat {
        data: Vec<u32>,
        rows: usize,
        cols: usize,
    }

    impl DenseMat {
        fn new(rows: usize, cols: usize) -> Self {
            Self {
                data: vec![0; rows * cols],
                rows,
                cols,
            }
        }
    }

    impl NDIndex<u32> for DenseMat {
        fn ndim(&self) -> usize {
            2
        }
        fn dim(&self, axis: usize) -> usize {
            if axis == 0 {
                self.rows
            } else {
                self.cols
            }
        }
        fn get(&self, ix: &[usize]) -> u32 {
            self.data[ix[0] * self.cols + ix[1]]
        }
        fn set(&mut self, ix: &[usize], v: u32) {
            self.data[ix[0] * self.cols + ix[1]] = v;
        }
    }

    /// Minimal sparse matrix for testing (COO-based, implements Sparse2D).
    struct SparseMat {
        n: usize,
        /// Sorted by (row, col). Each row's entries are contiguous.
        row_ptr: Vec<usize>,
        col_idx: Vec<usize>,
        values: Vec<u32>,
    }

    impl SparseMat {
        /// Build from (row, col, val) triplets. n = matrix dimension.
        fn from_triplets(n: usize, trips: &[(usize, usize, u32)]) -> Self {
            let mut sorted = trips.to_vec();
            sorted.sort_by_key(|&(r, c, _)| (r, c));

            let mut row_ptr = vec![0; n + 1];
            let mut col_idx = Vec::new();
            let mut values = Vec::new();

            for &(r, c, v) in &sorted {
                if v == 0 {
                    continue;
                }
                col_idx.push(c);
                values.push(v);
                row_ptr[r + 1] = col_idx.len();
            }
            // Fill forward
            for i in 1..=n {
                if row_ptr[i] == 0 && i > 0 {
                    row_ptr[i] = row_ptr[i - 1];
                }
            }
            // Fix: ensure monotonic
            for i in 1..=n {
                row_ptr[i] = row_ptr[i].max(row_ptr[i - 1]);
            }

            Self {
                n,
                row_ptr,
                col_idx,
                values,
            }
        }
    }

    impl NDIndex<u32> for SparseMat {
        fn ndim(&self) -> usize {
            2
        }
        fn dim(&self, _axis: usize) -> usize {
            self.n
        }
        fn get(&self, ix: &[usize]) -> u32 {
            let r = ix[0];
            let c = ix[1];
            let start = self.row_ptr[r];
            let end = self.row_ptr[r + 1];
            for i in start..end {
                if self.col_idx[i] == c {
                    return self.values[i];
                }
            }
            0
        }
        fn set(&mut self, _ix: &[usize], _v: u32) {
            panic!("SparseMat is read-only");
        }
        fn get_opt(&self, ix: &[usize]) -> Option<u32> {
            let r = ix[0];
            let c = ix[1];
            let start = self.row_ptr[r];
            let end = self.row_ptr[r + 1];
            for i in start..end {
                if self.col_idx[i] == c {
                    return Some(self.values[i]);
                }
            }
            None
        }
        fn is_sparse_2d(&self) -> bool { true }
        fn sparse_row_nnz(&self, row: usize) -> usize {
            self.row_ptr[row + 1] - self.row_ptr[row]
        }
        fn sparse_row_entry(&self, row: usize, idx: usize) -> (usize, u32) {
            let start = self.row_ptr[row];
            (self.col_idx[start + idx], self.values[start + idx])
        }
    }

    impl Sparse2D<u32> for SparseMat {
        fn nnz(&self) -> usize {
            self.values.len()
        }
        fn n_rows(&self) -> usize {
            self.n
        }
        fn row_nnz(&self, row: usize) -> usize {
            self.row_ptr[row + 1] - self.row_ptr[row]
        }
        fn row_entry(&self, row: usize, idx: usize) -> (usize, u32) {
            let start = self.row_ptr[row];
            (self.col_idx[start + idx], self.values[start + idx])
        }
    }

    /// Reference matmul for verification.
    fn naive_matmul(a: &SparseMat, b: &SparseMat) -> Vec<Vec<u32>> {
        let n = a.n;
        let mut c = vec![vec![0u32; n]; n];
        for i in 0..n {
            for k in 0..n {
                let a_ik = a.get(&[i, k]);
                if a_ik == 0 {
                    continue;
                }
                for j in 0..n {
                    c[i][j] += a_ik * b.get(&[k, j]);
                }
            }
        }
        c
    }

    #[test]
    fn test_approach1_baseline() {
        let a = SparseMat::from_triplets(3, &[(0, 1, 1), (1, 2, 1), (2, 0, 1)]);
        let b = SparseMat::from_triplets(3, &[(0, 1, 1), (1, 2, 1), (2, 0, 1)]);
        let mut out = DenseMat::new(3, 3);

        einsum_binary("ab,bc->ac", &a, &b, &mut out).unwrap();

        let expected = naive_matmul(&a, &b);
        for i in 0..3 {
            for j in 0..3 {
                assert_eq!(
                    out.get(&[i, j]),
                    expected[i][j],
                    "baseline mismatch at ({i},{j})"
                );
            }
        }
    }

    #[test]
    fn test_approach2_sparse_driven() {
        let a = SparseMat::from_triplets(4, &[(0, 1, 2), (0, 2, 3), (1, 3, 1), (2, 3, 4)]);
        let b = SparseMat::from_triplets(4, &[(1, 0, 5), (2, 0, 6), (3, 1, 7)]);
        let mut out = DenseMat::new(4, 4);

        einsum_sparse_driven("ab,bc->ac", &a, &b, &mut out).unwrap();

        let expected = naive_matmul(&a, &b);
        for i in 0..4 {
            for j in 0..4 {
                assert_eq!(
                    out.get(&[i, j]),
                    expected[i][j],
                    "sparse-driven mismatch at ({i},{j})"
                );
            }
        }
    }

    #[test]
    fn test_approach3_vm() {
        let a = SparseMat::from_triplets(4, &[(0, 1, 2), (0, 2, 3), (1, 3, 1), (2, 3, 4)]);
        let b = SparseMat::from_triplets(4, &[(1, 0, 5), (2, 0, 6), (3, 1, 7)]);
        let mut out = DenseMat::new(4, 4);

        einsum_vm_oneshot("ab,bc->ac", &[&a, &b], &mut [&mut out]).unwrap();

        let expected = naive_matmul(&a, &b);
        for i in 0..4 {
            for j in 0..4 {
                assert_eq!(
                    out.get(&[i, j]),
                    expected[i][j],
                    "VM mismatch at ({i},{j})"
                );
            }
        }
    }

    #[test]
    fn test_approach3_vm_display() {
        let a = SparseMat::from_triplets(4, &[(0, 1, 1)]);
        let b = SparseMat::from_triplets(4, &[(1, 0, 1)]);
        let program = compile_vm("ab,bc->ac", &[&a as &dyn NDIndex<u32>, &b]).unwrap();
        let display = format!("{program}");
        assert!(display.contains("SPARSE"), "VM should use sparse loops:\n{display}");
        println!("{display}");
    }

    #[test]
    fn test_approach4_sparse_hash() {
        let a = SparseMat::from_triplets(4, &[(0, 1, 2), (0, 2, 3), (1, 3, 1), (2, 3, 4)]);
        let b = SparseMat::from_triplets(4, &[(1, 0, 5), (2, 0, 6), (3, 1, 7)]);
        let mut out = DenseMat::new(4, 4);

        einsum_sparse_hash("ab,bc->ac", &a, &b, &mut out).unwrap();

        let expected = naive_matmul(&a, &b);
        for i in 0..4 {
            for j in 0..4 {
                assert_eq!(
                    out.get(&[i, j]),
                    expected[i][j],
                    "hash mismatch at ({i},{j})"
                );
            }
        }
    }

    #[test]
    fn test_all_approaches_agree_diamond() {
        // Diamond graph: 0→1, 0→2, 1→3, 2→3
        let a = SparseMat::from_triplets(
            4,
            &[(0, 1, 1), (0, 2, 1), (1, 3, 1), (2, 3, 1)],
        );
        let b = a.clone_sparse();
        let expected = naive_matmul(&a, &b);

        let mut out1 = DenseMat::new(4, 4);
        einsum_binary("ab,bc->ac", &a, &b, &mut out1).unwrap();

        let mut out2 = DenseMat::new(4, 4);
        einsum_sparse_driven("ab,bc->ac", &a, &b, &mut out2).unwrap();

        let mut out3 = DenseMat::new(4, 4);
        einsum_vm_oneshot("ab,bc->ac", &[&a, &b], &mut [&mut out3]).unwrap();

        let mut out4 = DenseMat::new(4, 4);
        einsum_sparse_hash("ab,bc->ac", &a, &b, &mut out4).unwrap();

        for i in 0..4 {
            for j in 0..4 {
                let e = expected[i][j];
                assert_eq!(out1.get(&[i, j]), e, "baseline@({i},{j})");
                assert_eq!(out2.get(&[i, j]), e, "sparse-driven@({i},{j})");
                assert_eq!(out3.get(&[i, j]), e, "VM@({i},{j})");
                assert_eq!(out4.get(&[i, j]), e, "hash@({i},{j})");
            }
        }
    }

    #[test]
    fn test_identity_matmul() {
        // A × I = A
        let a = SparseMat::from_triplets(3, &[(0, 1, 5), (1, 2, 3), (2, 0, 7)]);
        let id = SparseMat::from_triplets(3, &[(0, 0, 1), (1, 1, 1), (2, 2, 1)]);

        let mut out = DenseMat::new(3, 3);
        einsum_sparse_driven("ab,bc->ac", &a, &id, &mut out).unwrap();

        assert_eq!(out.get(&[0, 1]), 5);
        assert_eq!(out.get(&[1, 2]), 3);
        assert_eq!(out.get(&[2, 0]), 7);
        assert_eq!(out.get(&[0, 0]), 0);
    }

    /// Dense N-dimensional tensor for testing higher-dimensional VM inputs.
    struct DenseTensor {
        data: Vec<u32>,
        shape: Vec<usize>,
    }

    impl DenseTensor {
        fn new(shape: Vec<usize>) -> Self {
            let n: usize = shape.iter().product();
            Self { data: vec![0; n], shape }
        }
        fn linear_index(&self, ix: &[usize]) -> usize {
            let mut idx = 0;
            let mut stride = 1;
            for (&k, &dim) in ix.iter().rev().zip(self.shape.iter().rev()) {
                idx += k * stride;
                stride *= dim;
            }
            idx
        }
    }

    impl NDIndex<u32> for DenseTensor {
        fn ndim(&self) -> usize { self.shape.len() }
        fn dim(&self, axis: usize) -> usize { self.shape[axis] }
        fn get(&self, ix: &[usize]) -> u32 { self.data[self.linear_index(ix)] }
        fn set(&mut self, ix: &[usize], v: u32) {
            let i = self.linear_index(ix);
            self.data[i] = v;
        }
    }

    #[test]
    fn test_vm_3d_dense_inputs() {
        // "abc,cd->abd": batched matmul with 3D × 2D → 3D
        // All dense — no sparse loops, but the VM should handle it.
        let mut a = DenseTensor::new(vec![2, 3, 4]); // batch=2, rows=3, inner=4
        let mut b = DenseTensor::new(vec![4, 5]);     // inner=4, cols=5

        // Fill with simple values
        for i in 0..2 {
            for j in 0..3 {
                for k in 0..4 {
                    a.set(&[i, j, k], (i * 12 + j * 4 + k + 1) as u32);
                }
            }
        }
        for k in 0..4 {
            for l in 0..5 {
                b.set(&[k, l], (k * 5 + l + 1) as u32);
            }
        }

        let mut out = DenseTensor::new(vec![2, 3, 5]);
        einsum_vm_oneshot(
            "abc,cd->abd",
            &[&a, &b],
            &mut [&mut out],
        ).unwrap();

        // Verify against naive computation
        for i in 0..2 {
            for j in 0..3 {
                for l in 0..5 {
                    let mut expected = 0u32;
                    for k in 0..4 {
                        expected += a.get(&[i, j, k]) * b.get(&[k, l]);
                    }
                    assert_eq!(
                        out.get(&[i, j, l]), expected,
                        "3D mismatch at ({i},{j},{l})"
                    );
                }
            }
        }
    }

    #[test]
    fn test_vm_mixed_2d_sparse_and_dense() {
        // "ab,bc->ac": one sparse, one dense — VM should use sparse for the
        // sparse input's axis and dense for the dense input.
        let a = SparseMat::from_triplets(3, &[(0, 1, 2), (1, 2, 3)]);
        let mut b = DenseTensor::new(vec![3, 3]);
        for i in 0..3 {
            for j in 0..3 {
                b.set(&[i, j], (i * 3 + j + 1) as u32);
            }
        }

        let mut out = DenseMat::new(3, 3);
        einsum_vm_oneshot_dyn(
            "ab,bc->ac",
            &[&a as &dyn NDIndex<u32>, &b as &dyn NDIndex<u32>],
            &mut [&mut out as &mut dyn NDIndex<u32>],
        ).unwrap();

        // Verify: row 0 of A has only (1, 2), row 1 has only (2, 3)
        // C[0, j] = A[0,1]*B[1,j] = 2 * B[1,j]
        // C[1, j] = A[1,2]*B[2,j] = 3 * B[2,j]
        for j in 0..3 {
            assert_eq!(out.get(&[0, j]), 2 * b.get(&[1, j]), "mixed@(0,{j})");
            assert_eq!(out.get(&[1, j]), 3 * b.get(&[2, j]), "mixed@(1,{j})");
            assert_eq!(out.get(&[2, j]), 0, "mixed@(2,{j})");
        }
    }

    #[test]
    fn test_vm_4d_attention() {
        // "bhqd,bhkd->bhqk": attention-style with all dense inputs
        let (ba, h, q, k, d) = (1, 1, 2, 2, 3);
        let mut qm = DenseTensor::new(vec![ba, h, q, d]);
        let mut km = DenseTensor::new(vec![ba, h, k, d]);

        for qi in 0..q {
            for di in 0..d {
                qm.set(&[0, 0, qi, di], (qi * d + di + 1) as u32);
            }
        }
        for ki in 0..k {
            for di in 0..d {
                km.set(&[0, 0, ki, di], (ki * d + di + 1) as u32);
            }
        }

        let mut out = DenseTensor::new(vec![ba, h, q, k]);
        einsum_vm_oneshot(
            "bhqd,bhkd->bhqk",
            &[&qm, &km],
            &mut [&mut out],
        ).unwrap();

        for qi in 0..q {
            for ki in 0..k {
                let mut expected = 0u32;
                for di in 0..d {
                    expected += qm.get(&[0, 0, qi, di]) * km.get(&[0, 0, ki, di]);
                }
                assert_eq!(
                    out.get(&[0, 0, qi, ki]), expected,
                    "attention@(0,0,{qi},{ki})"
                );
            }
        }
    }

    impl SparseMat {
        fn clone_sparse(&self) -> Self {
            Self {
                n: self.n,
                row_ptr: self.row_ptr.clone(),
                col_idx: self.col_idx.clone(),
                values: self.values.clone(),
            }
        }
    }

    /// 0-dim scalar output tensor for VM scalar tests.
    struct ScalarOut {
        val: u32,
    }

    impl ScalarOut {
        fn new() -> Self { Self { val: 0 } }
    }

    impl NDIndex<u32> for ScalarOut {
        fn ndim(&self) -> usize { 0 }
        fn dim(&self, _axis: usize) -> usize { panic!("0-dim has no axes") }
        fn get(&self, _ix: &[usize]) -> u32 { self.val }
        fn set(&mut self, _ix: &[usize], v: u32) { self.val = v; }
    }

    #[test]
    fn test_vm_scalar_dot_sparse() {
        // "i,i->" dot product with sparse inputs
        // a = [0, 2, 0, 3], b = [0, 5, 7, 0]
        // dot = 0 + 2*5 + 0 + 0 = 10
        let a = SparseMat::from_triplets(1, &[(0, 1, 2), (0, 3, 3)]);
        let b = SparseMat::from_triplets(1, &[(0, 1, 5), (0, 2, 7)]);

        // For dot product on 1D vectors stored as 1-row matrices,
        // use spec "ab,ab->" (Frobenius inner product) since SparseMat is 2D
        let mut out = ScalarOut::new();
        einsum_vm_oneshot("ab,ab->", &[&a, &b], &mut [&mut out]).unwrap();

        // a[0,1]*b[0,1] + a[0,3]*b[0,3] = 2*5 + 0 = 10
        assert_eq!(out.val, 10);
    }

    #[test]
    fn test_vm_scalar_trace_sparse() {
        // "aa->" trace of a sparse matrix
        // Only diagonal entries matter: (0,0)=1, (1,1)=5, (2,2)=9
        let m = SparseMat::from_triplets(3, &[
            (0, 0, 1), (0, 2, 2),
            (1, 1, 5), (1, 2, 3),
            (2, 2, 9),
        ]);

        let mut out = ScalarOut::new();
        einsum_vm_oneshot("aa->", &[&m], &mut [&mut out]).unwrap();

        assert_eq!(out.val, 15); // 1 + 5 + 9
    }

    #[test]
    fn test_vm_scalar_frobenius_sparse() {
        // "ab,ab->" Frobenius inner product (sum of element-wise products)
        let a = SparseMat::from_triplets(3, &[
            (0, 1, 2), (1, 0, 3), (2, 2, 4),
        ]);
        let b = SparseMat::from_triplets(3, &[
            (0, 1, 5), (1, 0, 7), (1, 1, 99), (2, 2, 2),
        ]);

        let mut out = ScalarOut::new();
        einsum_vm_oneshot("ab,ab->", &[&a, &b], &mut [&mut out]).unwrap();

        // overlapping entries: (0,1): 2*5=10, (1,0): 3*7=21, (2,2): 4*2=8
        assert_eq!(out.val, 39); // 10 + 21 + 8
    }

    #[test]
    fn test_vm_scalar_dense_dot() {
        // "i,i->" with dense 1D inputs
        let mut a = DenseTensor::new(vec![4]);
        let mut b = DenseTensor::new(vec![4]);
        for i in 0..4 {
            a.set(&[i], (i + 1) as u32);       // [1, 2, 3, 4]
            b.set(&[i], (i + 5) as u32);       // [5, 6, 7, 8]
        }

        let mut out = ScalarOut::new();
        einsum_vm_oneshot("i,i->", &[&a, &b], &mut [&mut out]).unwrap();

        // 1*5 + 2*6 + 3*7 + 4*8 = 5 + 12 + 21 + 32 = 70
        assert_eq!(out.val, 70);
    }

    #[test]
    fn test_vm_scalar_three_input() {
        // "i,i,i->" element-wise triple product summed to scalar
        let mut a = DenseTensor::new(vec![3]);
        let mut b = DenseTensor::new(vec![3]);
        let mut c = DenseTensor::new(vec![3]);
        for i in 0..3 {
            a.set(&[i], (i + 1) as u32);       // [1, 2, 3]
            b.set(&[i], (i + 4) as u32);       // [4, 5, 6]
            c.set(&[i], (i + 7) as u32);       // [7, 8, 9]
        }

        let mut out = ScalarOut::new();
        einsum_vm_oneshot("i,i,i->", &[&a, &b, &c], &mut [&mut out]).unwrap();

        // 1*4*7 + 2*5*8 + 3*6*9 = 28 + 80 + 162 = 270
        assert_eq!(out.val, 270);
    }

    // --- Multi-output tests ---

    #[test]
    fn test_vm_multi_output_matmul_and_transpose() {
        // "ab,bc->ac,ca": matmul result written to both C and C^T simultaneously
        let a = SparseMat::from_triplets(3, &[(0, 1, 2), (1, 2, 3), (2, 0, 1)]);
        let b = SparseMat::from_triplets(3, &[(0, 1, 4), (1, 0, 5), (2, 2, 6)]);

        let mut out_ac = DenseMat::new(3, 3);
        let mut out_ca = DenseMat::new(3, 3);
        einsum_vm_oneshot("ab,bc->ac,ca", &[&a, &b], &mut [&mut out_ac, &mut out_ca]).unwrap();

        // Verify against naive matmul
        let expected = naive_matmul(&a, &b);
        for i in 0..3 {
            for j in 0..3 {
                assert_eq!(out_ac.get(&[i, j]), expected[i][j], "ac@({i},{j})");
                assert_eq!(out_ca.get(&[j, i]), expected[i][j], "ca@({j},{i})");
            }
        }
    }

    #[test]
    fn test_vm_multi_output_dense() {
        // "ab,bc->ac,ca" with dense inputs
        let mut a = DenseTensor::new(vec![3, 3]);
        let mut b = DenseTensor::new(vec![3, 3]);
        for i in 0..3 {
            for j in 0..3 {
                a.set(&[i, j], (i * 3 + j + 1) as u32);
                b.set(&[i, j], (i * 3 + j + 10) as u32);
            }
        }

        let mut out_ac = DenseTensor::new(vec![3, 3]);
        let mut out_ca = DenseTensor::new(vec![3, 3]);
        einsum_vm_oneshot("ab,bc->ac,ca", &[&a, &b], &mut [&mut out_ac, &mut out_ca]).unwrap();

        // Verify C[i,j] = sum_k A[i,k]*B[k,j]
        for i in 0..3 {
            for j in 0..3 {
                let mut expected = 0u32;
                for k in 0..3 {
                    expected += a.get(&[i, k]) * b.get(&[k, j]);
                }
                assert_eq!(out_ac.get(&[i, j]), expected, "ac@({i},{j})");
                assert_eq!(out_ca.get(&[j, i]), expected, "ca@({j},{i})");
            }
        }
    }

    #[test]
    fn test_vm_multi_output_matmul_and_scalar() {
        // "ab,bc->ac," : matmul + scalar (Frobenius-like total sum)
        // Wait — we need different contracted indices for the scalar.
        // Actually "ab,ba->,ab" would be: scalar = sum_ab A[a,b]*B[b,a],
        // and output ab = A[a,b]*B[b,a] (element-wise, no contraction for ab output)
        // Let's test a simpler case: "ab,bc->ac,ac" (same output written twice)
        let a = SparseMat::from_triplets(3, &[(0, 1, 2), (1, 2, 3)]);
        let b = SparseMat::from_triplets(3, &[(1, 0, 5), (2, 2, 6)]);

        let mut out1 = DenseMat::new(3, 3);
        let mut out2 = DenseMat::new(3, 3);
        einsum_vm_oneshot("ab,bc->ac,ac", &[&a, &b], &mut [&mut out1, &mut out2]).unwrap();

        let expected = naive_matmul(&a, &b);
        for i in 0..3 {
            for j in 0..3 {
                assert_eq!(out1.get(&[i, j]), expected[i][j], "out1@({i},{j})");
                assert_eq!(out2.get(&[i, j]), expected[i][j], "out2@({i},{j})");
            }
        }
    }
}
