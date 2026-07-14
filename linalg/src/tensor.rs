//! Core tensor traits.
//!
//! [`NDIndex`] is the universal interface for any N-dimensional tensor.
//! Implement it to make a type composable with [`crate::einsum`].
//!
//! [`Scalar`] is the numeric element trait: the arithmetic the einsum VM
//! needs plus the per-operator identity elements used by generalized
//! (non-sum) reductions.
//!
//! [`Sparse2D`] is an extension for 2D matrices that expose row-wise
//! non-zero iteration. The einsum VM detects `Sparse2D` participants via
//! [`NDIndex::as_sparse_2d`] and emits sparse loops for them, falling back
//! to dense loops for everything else.

/// Numeric element for generalized (semiring) einsum reductions.
///
/// Extends the ad-hoc arithmetic bounds of the plain einsum with the
/// identity elements each [`crate::einsum::Reduce`] operator needs:
///
/// - [`ZERO`](Scalar::ZERO) — identity for `sum` (and the value of a
///   structurally-missing sparse entry);
/// - [`ONE`](Scalar::ONE) — identity for `prod`;
/// - [`LEAST`](Scalar::LEAST) — identity for `max`: `-∞` for floats,
///   `T::MIN` for integers. Note this is *not* `f32::MIN` (the smallest
///   finite value) for floats;
/// - [`GREATEST`](Scalar::GREATEST) — identity for `min`: `+∞` for floats,
///   `T::MAX` for integers.
///
/// Implemented for all the primitive numeric types.
pub trait Scalar:
    Copy
    + Default
    + PartialEq
    + PartialOrd
    + std::ops::Add<Output = Self>
    + std::ops::AddAssign
    + std::ops::Mul<Output = Self>
{
    const ZERO: Self;
    const ONE: Self;
    /// Least value of the type (`-∞` for floats): identity for `max`.
    const LEAST: Self;
    /// Greatest value of the type (`+∞` for floats): identity for `min`.
    const GREATEST: Self;
}

macro_rules! impl_scalar_int {
    ($($t:ty),*) => {$(
        impl Scalar for $t {
            const ZERO: Self = 0;
            const ONE: Self = 1;
            const LEAST: Self = <$t>::MIN;
            const GREATEST: Self = <$t>::MAX;
        }
    )*};
}
impl_scalar_int!(i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize);

macro_rules! impl_scalar_float {
    ($($t:ty),*) => {$(
        impl Scalar for $t {
            const ZERO: Self = 0.0;
            const ONE: Self = 1.0;
            const LEAST: Self = <$t>::NEG_INFINITY;
            const GREATEST: Self = <$t>::INFINITY;
        }
    )*};
}
impl_scalar_float!(f32, f64);

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

/// Extension of [`NDIndex`] for CSR-style sparse tensors.
///
/// Provides row-wise access to non-zero entries — the engine uses this to
/// skip entire zero columns inside the einsum inner loop. `row` is the
/// **compound** row index: the flattened leading axes (everything but the
/// last). For a 2D matrix that is just the row; for a batched/rectangular
/// tensor it is the row-major flattening of all axes except the stored
/// column, so the same row-iteration interface serves any rank.
pub trait Sparse2D<T>: NDIndex<T> {
    /// Total number of structural non-zeros.
    fn nnz(&self) -> usize;

    /// Number of compound rows (product of all axes but the last).
    fn n_rows(&self) -> usize;

    /// Number of non-zero entries in compound `row`.
    fn row_nnz(&self, row: usize) -> usize;

    /// The `idx`-th non-zero entry in compound `row` as `(col, value)`.
    /// `idx` must be in `0..row_nnz(row)`.
    fn row_entry(&self, row: usize, idx: usize) -> (usize, T);
}
