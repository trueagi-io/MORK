//! Core tensor traits.
//!
//! [`NDIndex`] is the universal interface for any N-dimensional tensor.
//! Implement it to make a type composable with [`crate::einsum`].
//!
//! [`Sparse2D`] is an extension for 2D matrices that expose row-wise
//! non-zero iteration. The einsum VM detects `Sparse2D` participants via
//! [`NDIndex::as_sparse_2d`] and emits sparse loops for them, falling back
//! to dense loops for everything else.

/// N-dimensional tensor read/write interface.
///
/// All index slices are ordered outermost-dimension-first.
pub trait NDIndex<T> {
    fn ndim(&self) -> usize;
    fn dim(&self, axis: usize) -> usize;
    fn get(&self, ix: &[usize]) -> T;
    fn set(&mut self, ix: &[usize], v: T);

    /// Returns `None` for structurally absent (zero) entries.
    ///
    /// Default wraps `get` in `Some`. Sparse implementations override this
    /// to return `None` for entries not present in the sparse structure.
    fn get_opt(&self, ix: &[usize]) -> Option<T> {
        Some(self.get(ix))
    }

    /// Downcast to a [`Sparse2D`] view if this is a 2D sparse matrix.
    ///
    /// Default: `None`. Sparse implementations should override to return
    /// `Some(self)` so the einsum VM can use row-wise sparse iteration.
    fn as_sparse_2d(&self) -> Option<&dyn Sparse2D<T>> {
        None
    }
}

/// Extension of [`NDIndex`] for 2D sparse matrices.
///
/// Provides row-wise access to non-zero entries — the engine uses this to
/// skip entire zero columns inside the einsum inner loop.
pub trait Sparse2D<T>: NDIndex<T> {
    /// Total number of structural non-zeros.
    fn nnz(&self) -> usize;

    /// Number of rows (axis 0).
    fn n_rows(&self) -> usize;

    /// Number of non-zero entries in `row`.
    fn row_nnz(&self, row: usize) -> usize;

    /// The `idx`-th non-zero entry in `row` as `(col, value)`.
    /// `idx` must be in `0..row_nnz(row)`.
    fn row_entry(&self, row: usize, idx: usize) -> (usize, T);
}
