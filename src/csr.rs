//! Compressed sparse row matrix with sequential and parallel SpGEMM.
//!
//! [`Csr<I, V>`] stores a sparse tensor as three flat arrays (`row_ptr`,
//! `col_idx`, `values`) and is immutable after construction. The logical
//! shape is `ndim >= 2`: the **last** axis is the stored column and all
//! preceding axes form the compound row index (flattened row-major into
//! `row_ptr`). This covers square 2D matrices, **rectangular** 2D matrices,
//! and **batched / higher-rank** sparse tensors.
//!
//! The square-2D graph operations ([`matmul`](Csr::matmul),
//! [`connected_components`](Csr::connected_components),
//! [`rcm`](Csr::rcm), …) assert a square 2D shape and panic otherwise.
//!
//! The `Csr<u32, V>` specialisation implements [`NDIndex`] (for any shape)
//! and [`Sparse2D`] (only when 2D) so it composes with [`crate::einsum`];
//! other `(I, V)` pairs are storage-only.
//!
//! # Example
//!
//! ```
//! use linalg::csr::Csr;
//!
//! // Triangle: 0 → 1 → 2 → 0
//! let a = Csr::<u32, u32>::from_edges(3, &[(0, 1), (1, 2), (2, 0)]);
//! let a2 = a.matmul(&a);
//! // A² paths: 0→1→2, 1→2→0, 2→0→1
//! assert_eq!(a2.get(0, 2), 1);
//! assert_eq!(a2.get(1, 0), 1);
//! assert_eq!(a2.get(2, 1), 1);
//! ```

use std::collections::VecDeque;
use std::num::Saturating;

use crate::tensor::{NDIndex, Sparse2D};

/// Index type — values stored in `row_ptr`, `col_idx`, and `perm`.
pub trait Index: Copy + Ord {
    fn to_usize(self) -> usize;
    fn from_usize(x: usize) -> Self;
}

impl Index for u32 {
    #[inline] fn to_usize(self) -> usize { self as usize }
    #[inline] fn from_usize(x: usize) -> Self { x as u32 }
}

impl Index for u64 {
    #[inline] fn to_usize(self) -> usize { self as usize }
    #[inline] fn from_usize(x: usize) -> Self { x as u64 }
}

/// Value type — saturating arithmetic in matmul for integers, normal
/// arithmetic for floats. `Default` is the additive identity (zero) and
/// `one()` is the multiplicative identity (used by [`Csr::identity`] and
/// [`Csr::from_edges`]).
pub trait Value: Copy + Default + PartialEq {
    fn one() -> Self;
    fn sat_add(a: Self, b: Self) -> Self;
    fn sat_mul(a: Self, b: Self) -> Self;
}

impl Value for u32 {
    #[inline] fn one() -> Self { 1 }
    #[inline] fn sat_add(a: Self, b: Self) -> Self { (Saturating(a) + Saturating(b)).0 }
    #[inline] fn sat_mul(a: Self, b: Self) -> Self { (Saturating(a) * Saturating(b)).0 }
}

impl Value for u64 {
    #[inline] fn one() -> Self { 1 }
    #[inline] fn sat_add(a: Self, b: Self) -> Self { (Saturating(a) + Saturating(b)).0 }
    #[inline] fn sat_mul(a: Self, b: Self) -> Self { (Saturating(a) * Saturating(b)).0 }
}

impl Value for f32 {
    #[inline] fn one() -> Self { 1.0 }
    #[inline] fn sat_add(a: Self, b: Self) -> Self { a + b }
    #[inline] fn sat_mul(a: Self, b: Self) -> Self { a * b }
}

impl Value for f64 {
    #[inline] fn one() -> Self { 1.0 }
    #[inline] fn sat_add(a: Self, b: Self) -> Self { a + b }
    #[inline] fn sat_mul(a: Self, b: Self) -> Self { a * b }
}

/// Compressed-sparse-row sparse tensor.
///
/// `shape` has `ndim >= 2`; the last axis is the stored column, the preceding
/// axes form the (row-major) compound row index. `row_ptr` has length
/// `compound_rows + 1`.
#[derive(Clone, Debug)]
pub struct Csr<I = u32, V = u32> {
    pub shape: Vec<usize>,
    pub row_ptr: Vec<usize>,
    pub col_idx: Vec<I>,
    pub values: Vec<V>,
}

// ─────────────────────────────────────────────────────────────────────────
// Send-pointer for the parallel matmul scratch pads
// ─────────────────────────────────────────────────────────────────────────

#[cfg(feature = "rayon")]
#[derive(Clone, Copy)]
struct SendPtr<T>(*mut T);
#[cfg(feature = "rayon")]
unsafe impl<T> Send for SendPtr<T> {}
#[cfg(feature = "rayon")]
unsafe impl<T> Sync for SendPtr<T> {}
#[cfg(feature = "rayon")]
impl<T> SendPtr<T> {
    #[inline]
    fn ptr(self) -> *mut T { self.0 }
}

// ─────────────────────────────────────────────────────────────────────────
// Construction
// ─────────────────────────────────────────────────────────────────────────

impl<I: Index, V: Value> Csr<I, V> {
    /// Empty n×n matrix.
    pub fn new(n: I) -> Self {
        let nu = n.to_usize();
        Self {
            shape: vec![nu, nu],
            row_ptr: vec![0; nu + 1],
            col_idx: Vec::new(),
            values: Vec::new(),
        }
    }

    /// Identity matrix — `V::one()` on the diagonal.
    pub fn identity(n: I) -> Self {
        let nu = n.to_usize();
        let mut row_ptr = Vec::with_capacity(nu + 1);
        let mut col_idx = Vec::with_capacity(nu);
        let mut values = Vec::with_capacity(nu);
        let one = V::one();
        for i in 0..nu {
            row_ptr.push(i);
            col_idx.push(I::from_usize(i));
            values.push(one);
        }
        row_ptr.push(nu);
        Self { shape: vec![nu, nu], row_ptr, col_idx, values }
    }

    /// Build from a directed edge list — each edge contributes `V::one()`.
    pub fn from_edges(n: I, edges: &[(I, I)]) -> Self {
        let one = V::one();
        let mut triplets: Vec<(I, I, V)> = edges.iter().map(|&(r, c)| (r, c, one)).collect();
        Self::from_coo(n, &mut triplets)
    }

    /// Build a square `n×n` matrix from COO triplets. Sorts by (row, col) and
    /// merges duplicates by summing.
    pub fn from_coo(n: I, triplets: &mut Vec<(I, I, V)>) -> Self {
        let nu = n.to_usize();
        triplets.sort_unstable_by_key(|&(r, c, _)| (r, c));

        let mut deduped: Vec<(I, I, V)> = Vec::with_capacity(triplets.len());
        let mut prev: Option<(I, I)> = None;
        for &(r, c, v) in triplets.iter() {
            if prev == Some((r, c)) {
                let last = deduped.last_mut().unwrap();
                last.2 = V::sat_add(last.2, v);
            } else {
                deduped.push((r, c, v));
                prev = Some((r, c));
            }
        }

        let mut col_idx_out = Vec::with_capacity(deduped.len());
        let mut values_out = Vec::with_capacity(deduped.len());
        let mut row_ptr = vec![0usize; nu + 1];
        let mut cur_row = 0usize;

        for &(r, c, v) in &deduped {
            if v == V::default() { continue; }
            let ru = r.to_usize();
            while cur_row <= ru {
                row_ptr[cur_row] = col_idx_out.len();
                cur_row += 1;
            }
            col_idx_out.push(c);
            values_out.push(v);
        }
        while cur_row <= nu {
            row_ptr[cur_row] = col_idx_out.len();
            cur_row += 1;
        }

        Self { shape: vec![nu, nu], row_ptr, col_idx: col_idx_out, values: values_out }
    }

    /// Build directly from CSR-style arrays for an arbitrary (rectangular or
    /// batched) shape. The last axis of `shape` is the stored column; the
    /// product of the preceding axes is the number of compound rows.
    ///
    /// Panics if the lengths are inconsistent with `shape`.
    pub fn from_parts(
        shape: Vec<usize>,
        row_ptr: Vec<usize>,
        col_idx: Vec<I>,
        values: Vec<V>,
    ) -> Self {
        assert!(shape.len() >= 2, "Csr shape needs ndim >= 2, got {shape:?}");
        let rows: usize = shape[..shape.len() - 1].iter().product();
        assert_eq!(
            row_ptr.len(),
            rows + 1,
            "row_ptr length {} must be product(leading dims)+1 = {}",
            row_ptr.len(),
            rows + 1
        );
        assert_eq!(col_idx.len(), values.len(), "col_idx and values length differ");
        Self { shape, row_ptr, col_idx, values }
    }

    // ── Shape accessors ──

    /// Number of axes (`>= 2`).
    #[inline]
    pub fn ndim(&self) -> usize {
        self.shape.len()
    }

    /// Size of `axis`.
    #[inline]
    pub fn dim(&self, axis: usize) -> usize {
        self.shape[axis]
    }

    /// Number of stored columns (size of the last axis).
    #[inline]
    pub fn n_cols(&self) -> usize {
        self.shape[self.shape.len() - 1]
    }

    /// Number of compound rows (product of all but the last axis).
    #[inline]
    pub fn n_rows(&self) -> usize {
        self.row_ptr.len() - 1
    }

    #[inline]
    fn is_square_2d(&self) -> bool {
        self.shape.len() == 2 && self.shape[0] == self.shape[1]
    }

    #[inline]
    fn assert_square_2d(&self, what: &str) {
        assert!(
            self.is_square_2d(),
            "Csr::{what} requires a square 2D matrix, but shape is {:?}",
            self.shape
        );
    }

    /// Side length of a square 2D matrix. Panics unless the shape is square 2D.
    #[inline]
    pub fn n(&self) -> I {
        self.assert_square_2d("n");
        I::from_usize(self.shape[0])
    }
}

// ─────────────────────────────────────────────────────────────────────────
// Queries
// ─────────────────────────────────────────────────────────────────────────

impl<I: Index, V: Value> Csr<I, V> {
    /// Number of structural non-zeros.
    pub fn nnz(&self) -> usize { self.values.len() }

    /// Value at `(r, c)` via binary search within the row, or `V::default()`.
    /// Requires a 2D shape (rectangular is fine); panics otherwise.
    pub fn get(&self, r: I, c: I) -> V {
        assert_eq!(self.shape.len(), 2, "Csr::get(r, c) requires a 2D matrix");
        let start = self.row_ptr[r.to_usize()];
        let end = self.row_ptr[r.to_usize() + 1];
        match self.col_idx[start..end].binary_search(&c) {
            Ok(i) => self.values[start + i],
            Err(_) => V::default(),
        }
    }

    /// Iterate `(col, value)` pairs in row `r`. Requires a 2D shape.
    pub fn row(&self, r: I) -> impl Iterator<Item = (I, V)> + '_ {
        assert_eq!(self.shape.len(), 2, "Csr::row(r) requires a 2D matrix");
        let start = self.row_ptr[r.to_usize()];
        let end = self.row_ptr[r.to_usize() + 1];
        self.col_idx[start..end]
            .iter()
            .zip(&self.values[start..end])
            .map(|(&c, &v)| (c, v))
    }
}

// ─────────────────────────────────────────────────────────────────────────
// SpGEMM and element-wise add
// ─────────────────────────────────────────────────────────────────────────

impl<I: Index, V: Value> Csr<I, V> {
    /// Sequential SpGEMM: `self × other`, dense `Vec<V>` accumulator per row.
    /// Time `O(flops + n × touched_rows)`, scratch `O(n)`.
    pub fn matmul(&self, other: &Self) -> Self {
        self.assert_square_2d("matmul");
        other.assert_square_2d("matmul");
        assert_eq!(self.shape[0], other.shape[0], "matmul shape mismatch");
        let nu = self.shape[0];

        let mut row_ptr = Vec::with_capacity(nu + 1);
        let mut col_idx = Vec::new();
        let mut values = Vec::new();
        row_ptr.push(0);

        let mut acc = vec![V::default(); nu];
        let mut nz_cols: Vec<I> = Vec::new();

        for i in 0..nu {
            let a_start = self.row_ptr[i];
            let a_end = self.row_ptr[i + 1];
            for idx in a_start..a_end {
                let k = self.col_idx[idx].to_usize();
                let a_ik = self.values[idx];
                let b_start = other.row_ptr[k];
                let b_end = other.row_ptr[k + 1];
                for jdx in b_start..b_end {
                    let j = other.col_idx[jdx];
                    let ju = j.to_usize();
                    if acc[ju] == V::default() {
                        nz_cols.push(j);
                    }
                    acc[ju] = V::sat_add(acc[ju], V::sat_mul(a_ik, other.values[jdx]));
                }
            }

            nz_cols.sort_unstable();
            for &j in &nz_cols {
                let ju = j.to_usize();
                let v = acc[ju];
                if v != V::default() {
                    col_idx.push(j);
                    values.push(v);
                }
                acc[ju] = V::default();
            }
            nz_cols.clear();

            row_ptr.push(col_idx.len());
        }

        Self { shape: vec![nu, nu], row_ptr, col_idx, values }
    }

    /// Parallel SpGEMM via rayon. Two-pass: symbolic (count nnz per row),
    /// then numeric (fill disjoint slices in parallel).
    #[cfg(feature = "rayon")]
    pub fn matmul_par(&self, other: &Self) -> Self
    where
        I: Send + Sync,
        V: Send + Sync,
    {
        use rayon::prelude::*;

        self.assert_square_2d("matmul_par");
        other.assert_square_2d("matmul_par");
        assert_eq!(self.shape[0], other.shape[0], "matmul_par shape mismatch");
        let nu = self.shape[0];

        // Pass 1: symbolic — count nnz per row, reusing a boolean mask.
        let mut nnz_per_row = vec![0usize; nu];
        nnz_per_row.par_iter_mut().enumerate().for_each_init(
            || vec![false; nu],
            |mask, (i, nnz_out)| {
                let mut count = 0usize;
                let a_start = self.row_ptr[i];
                let a_end = self.row_ptr[i + 1];
                for idx in a_start..a_end {
                    let k = self.col_idx[idx].to_usize();
                    let b_start = other.row_ptr[k];
                    let b_end = other.row_ptr[k + 1];
                    for jdx in b_start..b_end {
                        let j = other.col_idx[jdx].to_usize();
                        if !mask[j] {
                            mask[j] = true;
                            count += 1;
                        }
                    }
                }
                *nnz_out = count;
                // Clear mask
                for idx in a_start..a_end {
                    let k = self.col_idx[idx].to_usize();
                    let b_start = other.row_ptr[k];
                    let b_end = other.row_ptr[k + 1];
                    for jdx in b_start..b_end {
                        mask[other.col_idx[jdx].to_usize()] = false;
                    }
                }
            },
        );

        let mut row_ptr = Vec::with_capacity(nu + 1);
        row_ptr.push(0);
        for &c in &nnz_per_row {
            row_ptr.push(row_ptr.last().unwrap() + c);
        }
        let total_nnz = *row_ptr.last().unwrap();

        let mut col_idx_out = vec![I::from_usize(0); total_nnz];
        let mut values_out = vec![V::default(); total_nnz];

        // Pass 2: numeric — fill disjoint output slices in parallel.
        // SAFETY: each row writes to a disjoint slice [row_ptr[i]..row_ptr[i+1]].
        let col_ptr = &row_ptr;
        let out_c = SendPtr(col_idx_out.as_mut_ptr());
        let out_v = SendPtr(values_out.as_mut_ptr());

        (0..nu).into_par_iter().for_each_init(
            || (vec![V::default(); nu], Vec::<I>::new()),
            |(acc, nz_cols), i| {
                let a_start = self.row_ptr[i];
                let a_end = self.row_ptr[i + 1];
                for idx in a_start..a_end {
                    let k = self.col_idx[idx].to_usize();
                    let a_ik = self.values[idx];
                    let b_start = other.row_ptr[k];
                    let b_end = other.row_ptr[k + 1];
                    for jdx in b_start..b_end {
                        let j = other.col_idx[jdx];
                        let ju = j.to_usize();
                        if acc[ju] == V::default() {
                            nz_cols.push(j);
                        }
                        acc[ju] = V::sat_add(acc[ju], V::sat_mul(a_ik, other.values[jdx]));
                    }
                }

                nz_cols.sort_unstable();
                let mut pos = col_ptr[i];
                for &j in nz_cols.iter() {
                    let ju = j.to_usize();
                    let v = acc[ju];
                    if v != V::default() {
                        unsafe {
                            *out_c.ptr().add(pos) = j;
                            *out_v.ptr().add(pos) = v;
                        }
                        pos += 1;
                    }
                    acc[ju] = V::default();
                }
                nz_cols.clear();
            },
        );

        Self {
            shape: vec![nu, nu],
            row_ptr,
            col_idx: col_idx_out,
            values: values_out,
        }
    }

    /// Element-wise addition via sorted merge per (compound) row. Works for
    /// any shape; both operands must have the same shape.
    pub fn add(&self, other: &Self) -> Self {
        assert_eq!(self.shape, other.shape, "add shape mismatch");
        let nu = self.n_rows();

        let mut row_ptr = Vec::with_capacity(nu + 1);
        let mut col_idx = Vec::new();
        let mut values = Vec::new();
        row_ptr.push(0);

        for r in 0..nu {
            let a_start = self.row_ptr[r];
            let a_end = self.row_ptr[r + 1];
            let b_start = other.row_ptr[r];
            let b_end = other.row_ptr[r + 1];

            let mut ai = a_start;
            let mut bi = b_start;
            while ai < a_end && bi < b_end {
                let ac = self.col_idx[ai];
                let bc = other.col_idx[bi];
                if ac < bc {
                    col_idx.push(ac);
                    values.push(self.values[ai]);
                    ai += 1;
                } else if ac > bc {
                    col_idx.push(bc);
                    values.push(other.values[bi]);
                    bi += 1;
                } else {
                    let v = V::sat_add(self.values[ai], other.values[bi]);
                    if v != V::default() {
                        col_idx.push(ac);
                        values.push(v);
                    }
                    ai += 1;
                    bi += 1;
                }
            }
            while ai < a_end {
                col_idx.push(self.col_idx[ai]);
                values.push(self.values[ai]);
                ai += 1;
            }
            while bi < b_end {
                col_idx.push(other.col_idx[bi]);
                values.push(other.values[bi]);
                bi += 1;
            }
            row_ptr.push(col_idx.len());
        }

        Self { shape: self.shape.clone(), row_ptr, col_idx, values }
    }
}

// ─────────────────────────────────────────────────────────────────────────
// Graph utilities
// ─────────────────────────────────────────────────────────────────────────

impl<I: Index, V: Value> Csr<I, V> {
    /// Connected components via union-find on the directed edge set
    /// (treats the graph as undirected — an edge in either direction
    /// connects its endpoints). Returns one component id per node.
    pub fn connected_components(&self) -> Vec<usize> {
        self.assert_square_2d("connected_components");
        let nu = self.shape[0];
        let mut parent: Vec<usize> = (0..nu).collect();
        let mut rank = vec![0u8; nu];

        fn find(parent: &mut [usize], mut x: usize) -> usize {
            while parent[x] != x {
                parent[x] = parent[parent[x]];
                x = parent[x];
            }
            x
        }
        fn union(parent: &mut [usize], rank: &mut [u8], a: usize, b: usize) {
            let ra = find(parent, a);
            let rb = find(parent, b);
            if ra == rb { return; }
            if rank[ra] < rank[rb] {
                parent[ra] = rb;
            } else if rank[ra] > rank[rb] {
                parent[rb] = ra;
            } else {
                parent[rb] = ra;
                rank[ra] += 1;
            }
        }

        for r in 0..nu {
            let s = self.row_ptr[r];
            let e = self.row_ptr[r + 1];
            for idx in s..e {
                union(&mut parent, &mut rank, r, self.col_idx[idx].to_usize());
            }
        }

        let mut id_map = vec![usize::MAX; nu];
        let mut result = vec![0usize; nu];
        let mut next_id = 0;
        for i in 0..nu {
            let root = find(&mut parent, i);
            if id_map[root] == usize::MAX {
                id_map[root] = next_id;
                next_id += 1;
            }
            result[i] = id_map[root];
        }
        result
    }

    /// `(max |r − c|, avg |r − c|)` over all non-zeros — a measure of how
    /// far entries sit from the diagonal. RCM reordering can dramatically
    /// reduce this.
    pub fn bandwidth_stats(&self) -> (usize, f64) {
        self.assert_square_2d("bandwidth_stats");
        let mut max_bw = 0usize;
        let mut sum_bw: u64 = 0;
        let mut count: u64 = 0;
        for r in 0..self.shape[0] {
            let s = self.row_ptr[r];
            let e = self.row_ptr[r + 1];
            for idx in s..e {
                let c = self.col_idx[idx].to_usize();
                let d = if r > c { r - c } else { c - r };
                max_bw = max_bw.max(d);
                sum_bw += d as u64;
                count += 1;
            }
        }
        (max_bw, sum_bw as f64 / count.max(1) as f64)
    }

    /// Reverse Cuthill–McKee reordering, in place. BFS from a
    /// pseudo-peripheral seed visiting neighbours in ascending-degree
    /// order; the resulting permutation is then reversed and applied.
    /// Reduces bandwidth — useful before matmul for cache locality.
    pub fn rcm(&mut self) {
        self.assert_square_2d("rcm");
        let nu = self.shape[0];
        let mut visited = vec![false; nu];
        let mut order: Vec<I> = Vec::with_capacity(nu);

        let deg = |row_ptr: &[usize], node: usize| row_ptr[node + 1] - row_ptr[node];

        for seed in 0..nu {
            if visited[seed] { continue; }

            // Pseudo-peripheral start: BFS from `seed`, take the last node visited.
            let start = {
                let mut queue = VecDeque::new();
                queue.push_back(seed);
                let mut last = seed;
                let mut vis2 = vec![false; nu];
                vis2[seed] = true;
                while let Some(u) = queue.pop_front() {
                    last = u;
                    let s = self.row_ptr[u];
                    let e = self.row_ptr[u + 1];
                    for idx in s..e {
                        let v = self.col_idx[idx].to_usize();
                        if !vis2[v] {
                            vis2[v] = true;
                            queue.push_back(v);
                        }
                    }
                }
                last
            };

            // Main BFS, neighbours sorted by ascending degree.
            let mut queue = VecDeque::new();
            queue.push_back(start);
            visited[start] = true;
            while let Some(u) = queue.pop_front() {
                order.push(I::from_usize(u));
                let s = self.row_ptr[u];
                let e = self.row_ptr[u + 1];
                let mut nbrs: Vec<usize> = Vec::with_capacity(e - s);
                for idx in s..e {
                    let v = self.col_idx[idx].to_usize();
                    if !visited[v] {
                        nbrs.push(v);
                    }
                }
                nbrs.sort_unstable_by_key(|&v| deg(&self.row_ptr, v));
                for v in nbrs {
                    if !visited[v] {
                        visited[v] = true;
                        queue.push_back(v);
                    }
                }
            }
        }

        order.reverse();
        self.permute(&order);
    }

    /// Reorder rows and columns by a permutation. `perm[new] = old`.
    /// Square 2D only (callers — `rcm` — assert this).
    fn permute(&mut self, perm: &[I]) {
        let nu = self.shape[0];
        let nnz = self.nnz();
        assert_eq!(perm.len(), nu);

        let mut inv = vec![I::from_usize(0); nu];
        for (new_idx, &old) in perm.iter().enumerate() {
            inv[old.to_usize()] = I::from_usize(new_idx);
        }

        let mut new_row_ptr = vec![0usize; nu + 1];
        for old_r in 0..nu {
            let count = self.row_ptr[old_r + 1] - self.row_ptr[old_r];
            new_row_ptr[inv[old_r].to_usize() + 1] = count;
        }
        for i in 1..=nu {
            new_row_ptr[i] += new_row_ptr[i - 1];
        }

        let mut new_col = vec![I::from_usize(0); nnz];
        let mut new_val = vec![V::default(); nnz];
        let mut cursor = new_row_ptr[..nu].to_vec();
        for old_r in 0..nu {
            let new_r = inv[old_r].to_usize();
            let s = self.row_ptr[old_r];
            let e = self.row_ptr[old_r + 1];
            for idx in s..e {
                let pos = cursor[new_r];
                new_col[pos] = inv[self.col_idx[idx].to_usize()];
                new_val[pos] = self.values[idx];
                cursor[new_r] += 1;
            }
        }

        // Sort columns within each new row.
        let mut pairs: Vec<(I, V)> = Vec::new();
        for r in 0..nu {
            let s = new_row_ptr[r];
            let e = new_row_ptr[r + 1];
            if e - s <= 1 { continue; }
            pairs.clear();
            pairs.extend(new_col[s..e].iter().copied().zip(new_val[s..e].iter().copied()));
            pairs.sort_unstable_by_key(|&(c, _)| c);
            for (i, &(c, v)) in pairs.iter().enumerate() {
                new_col[s + i] = c;
                new_val[s + i] = v;
            }
        }

        self.row_ptr = new_row_ptr;
        self.col_idx = new_col;
        self.values = new_val;
    }
}

// ─────────────────────────────────────────────────────────────────────────
// NDIndex + Sparse2D impls for u32-indexed Csr
// ─────────────────────────────────────────────────────────────────────────

impl<V: Value> Csr<u32, V> {
    /// Flatten the leading indices `ix[..ndim-1]` (row-major) into a compound
    /// row index. `ix` must have one entry per axis.
    #[inline]
    fn compound_row(&self, ix: &[usize]) -> usize {
        let nd = self.shape.len();
        let mut row = 0usize;
        for k in 0..nd - 1 {
            row = row * self.shape[k] + ix[k];
        }
        row
    }
}

impl<V: Value + 'static> NDIndex<V> for Csr<u32, V> {
    fn ndim(&self) -> usize {
        self.shape.len()
    }
    fn dim(&self, axis: usize) -> usize {
        self.shape[axis]
    }
    fn get(&self, ix: &[usize]) -> V {
        self.get_opt(ix).unwrap_or_default()
    }
    fn set(&mut self, _ix: &[usize], _v: V) {
        panic!("Csr is immutable after construction");
    }
    fn get_opt(&self, ix: &[usize]) -> Option<V> {
        let row = self.compound_row(ix);
        let c = ix[self.shape.len() - 1] as u32;
        let start = self.row_ptr[row];
        let end = self.row_ptr[row + 1];
        match self.col_idx[start..end].binary_search(&c) {
            Ok(i) => Some(self.values[start + i]),
            Err(_) => None,
        }
    }
    /// Only 2D matrices expose the [`Sparse2D`] row-iteration view; the einsum
    /// VM falls back to `get_opt` for higher-rank sparse tensors.
    fn as_sparse_2d(&self) -> Option<&dyn Sparse2D<V>> {
        if self.shape.len() == 2 {
            Some(self)
        } else {
            None
        }
    }
}

impl<V: Value + 'static> Sparse2D<V> for Csr<u32, V> {
    fn nnz(&self) -> usize { self.values.len() }
    fn n_rows(&self) -> usize { self.row_ptr.len() - 1 }
    fn row_nnz(&self, row: usize) -> usize {
        self.row_ptr[row + 1] - self.row_ptr[row]
    }
    fn row_entry(&self, row: usize, idx: usize) -> (usize, V) {
        let start = self.row_ptr[row];
        (self.col_idx[start + idx] as usize, self.values[start + idx])
    }
}

// ─────────────────────────────────────────────────────────────────────────
// Tests
// ─────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn identity_matmul() {
        let m: Csr<u32, u32> = Csr::from_edges(3, &[(0, 1), (1, 2)]);
        let id = Csr::<u32, u32>::identity(3);
        let result = m.matmul(&id);
        assert_eq!(result.get(0, 1), 1);
        assert_eq!(result.get(1, 2), 1);
        assert_eq!(result.get(0, 2), 0);
        assert_eq!(result.nnz(), 2);
    }

    #[test]
    fn triangle_squared() {
        let a: Csr<u32, u32> = Csr::from_edges(3, &[(0, 1), (1, 2), (2, 0)]);
        let a2 = a.matmul(&a);
        // A² = paths of length 2: 0→1→2, 1→2→0, 2→0→1
        assert_eq!(a2.get(0, 2), 1);
        assert_eq!(a2.get(1, 0), 1);
        assert_eq!(a2.get(2, 1), 1);
        assert_eq!(a2.get(0, 0), 0);
        assert_eq!(a2.nnz(), 3);
    }

    #[test]
    fn diamond_two_paths() {
        // Diamond: 0→1, 0→2, 1→3, 2→3
        let a: Csr<u32, u32> = Csr::from_edges(4, &[(0, 1), (0, 2), (1, 3), (2, 3)]);
        let a2 = a.matmul(&a);
        assert_eq!(a2.get(0, 3), 2, "two length-2 paths from 0 to 3");
    }

    #[test]
    fn add_with_overlap() {
        let a: Csr<u32, u32> = Csr::from_edges(3, &[(0, 1), (1, 2)]);
        let b: Csr<u32, u32> = Csr::from_edges(3, &[(0, 1), (2, 0)]);
        let c = a.add(&b);
        assert_eq!(c.get(0, 1), 2);
        assert_eq!(c.get(1, 2), 1);
        assert_eq!(c.get(2, 0), 1);
        assert_eq!(c.nnz(), 3);
    }

    #[test]
    fn from_coo_dedups() {
        let mut triplets: Vec<(u32, u32, u32)> = vec![
            (0, 1, 2),
            (0, 1, 3), // duplicate, should sum to 5
            (1, 2, 1),
        ];
        let m = Csr::<u32, u32>::from_coo(3, &mut triplets);
        assert_eq!(m.get(0, 1), 5);
        assert_eq!(m.get(1, 2), 1);
        assert_eq!(m.nnz(), 2);
    }

    #[test]
    fn connected_components_two() {
        // Two triangles: {0,1,2} and {3,4,5}
        let m: Csr<u32, u32> = Csr::from_edges(6, &[
            (0, 1), (1, 2), (2, 0),
            (3, 4), (4, 5), (5, 3),
        ]);
        let comps = m.connected_components();
        assert_eq!(comps[0], comps[1]);
        assert_eq!(comps[1], comps[2]);
        assert_eq!(comps[3], comps[4]);
        assert_eq!(comps[4], comps[5]);
        assert_ne!(comps[0], comps[3]);
    }

    #[test]
    fn bandwidth_basic() {
        // Tridiagonal: entries on (i, i±1) only
        let m: Csr<u32, u32> = Csr::from_edges(5, &[
            (0, 1), (1, 2), (2, 3), (3, 4),
            (1, 0), (2, 1), (3, 2), (4, 3),
        ]);
        let (max_bw, _avg) = m.bandwidth_stats();
        assert_eq!(max_bw, 1);
    }

    #[test]
    fn rcm_reduces_bandwidth() {
        // Reversed labelling of a path: 0 ↔ 5, 1 ↔ 4, … so neighbours are far apart.
        let edges: Vec<(u32, u32)> = (0..5)
            .map(|i| (i, 5 - i))
            .chain((0..5).map(|i| (5 - i, i)))
            .collect();
        let mut m: Csr<u32, u32> = Csr::from_edges(6, &edges);
        let (bw0, _) = m.bandwidth_stats();
        m.rcm();
        let (bw1, _) = m.bandwidth_stats();
        assert!(bw1 <= bw0, "RCM should not increase bandwidth ({bw0} -> {bw1})");
    }

    #[test]
    fn rectangular_construction_and_index() {
        // 2×3: A[0,1]=2, A[0,2]=3, A[1,0]=1.
        let m = Csr::<u32, f32>::from_parts(
            vec![2, 3],
            vec![0, 2, 3],
            vec![1, 2, 0],
            vec![2.0, 3.0, 1.0],
        );
        assert_eq!(m.ndim(), 2);
        assert_eq!(m.dim(0), 2);
        assert_eq!(m.n_cols(), 3);
        assert_eq!(m.n_rows(), 2);
        assert_eq!(NDIndex::get_opt(&m, &[0, 1]), Some(2.0));
        assert_eq!(NDIndex::get_opt(&m, &[0, 0]), None);
        assert_eq!(NDIndex::get_opt(&m, &[1, 0]), Some(1.0));
        assert_eq!(NDIndex::get(&m, &[1, 2]), 0.0);
        // 2D still exposes the Sparse2D view.
        assert!(NDIndex::as_sparse_2d(&m).is_some());
    }

    #[test]
    fn batched_3d_index() {
        // [2,2,2]: compound row = b*2 + i.
        let m = Csr::<u32, f32>::from_parts(
            vec![2, 2, 2],
            vec![0, 2, 3, 4, 5],
            vec![0, 1, 1, 0, 0],
            vec![1.0, 2.0, 3.0, 4.0, 5.0],
        );
        assert_eq!(m.ndim(), 3);
        assert_eq!(NDIndex::get_opt(&m, &[0, 0, 0]), Some(1.0));
        assert_eq!(NDIndex::get_opt(&m, &[0, 0, 1]), Some(2.0));
        assert_eq!(NDIndex::get_opt(&m, &[0, 1, 1]), Some(3.0));
        assert_eq!(NDIndex::get_opt(&m, &[0, 1, 0]), None);
        assert_eq!(NDIndex::get_opt(&m, &[1, 0, 0]), Some(4.0));
        assert_eq!(NDIndex::get_opt(&m, &[1, 1, 0]), Some(5.0));
        // Higher-rank does not expose the 2D Sparse2D view.
        assert!(NDIndex::as_sparse_2d(&m).is_none());
    }

    #[test]
    fn add_rectangular() {
        let a = Csr::<u32, u32>::from_parts(vec![2, 3], vec![0, 1, 2], vec![1, 0], vec![5, 7]);
        let b = Csr::<u32, u32>::from_parts(vec![2, 3], vec![0, 1, 2], vec![1, 2], vec![3, 9]);
        let c = a.add(&b);
        assert_eq!(c.shape, vec![2, 3]);
        assert_eq!(NDIndex::get_opt(&c, &[0, 1]), Some(8)); // 5 + 3
        assert_eq!(NDIndex::get_opt(&c, &[1, 0]), Some(7));
        assert_eq!(NDIndex::get_opt(&c, &[1, 2]), Some(9));
    }

    #[test]
    #[should_panic(expected = "square 2D")]
    fn matmul_panics_on_rectangular() {
        let m = Csr::<u32, u32>::from_parts(vec![2, 3], vec![0, 1, 2], vec![1, 0], vec![1, 1]);
        let _ = m.matmul(&m);
    }

    #[test]
    #[should_panic(expected = "square 2D")]
    fn n_panics_on_rectangular() {
        let m = Csr::<u32, u32>::from_parts(vec![2, 3], vec![0, 1, 2], vec![1, 0], vec![1, 1]);
        let _ = m.n();
    }

    #[test]
    #[should_panic(expected = "square 2D")]
    fn connected_components_panics_on_batched() {
        let m = Csr::<u32, u32>::from_parts(
            vec![2, 2, 2],
            vec![0, 1, 1, 2, 2],
            vec![0, 1],
            vec![1, 1],
        );
        let _ = m.connected_components();
    }

    #[cfg(feature = "rayon")]
    #[test]
    fn matmul_par_agrees_with_seq() {
        let a: Csr<u32, u32> = Csr::from_edges(10, &[
            (0, 1), (1, 2), (2, 3), (3, 4), (4, 5),
            (5, 6), (6, 7), (7, 8), (8, 9), (9, 0),
            (0, 5), (1, 6), (2, 7),
        ]);
        let r1 = a.matmul(&a);
        let r2 = a.matmul_par(&a);
        assert_eq!(r1.nnz(), r2.nnz());
        for i in 0..10 {
            for j in 0..10 {
                assert_eq!(r1.get(i, j), r2.get(i, j), "mismatch at ({i},{j})");
            }
        }
    }
}
