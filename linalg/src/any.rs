//! Closed-set enum dispatch over the crate's concrete tensor types.
//!
//! [`Tensor<'a, T>`] wraps a borrowed reference to any of the
//! T-generic tensor types ([`Dense<T>`](crate::dense::Dense),
//! [`Csr<u32, T>`](crate::csr::Csr)). [`TensorF32<'a>`] is the
//! f32-specialised version that additionally includes
//! [`Blocked8`](crate::blocked::Blocked8) /
//! [`Blocked16`](crate::blocked::Blocked16).
//!
//! Either enum implements [`NDIndex<T>`](crate::tensor::NDIndex) (and
//! [`Sparse2D<T>`](crate::tensor::Sparse2D) when a Csr variant is
//! present), so they can be passed straight to [`crate::einsum`]
//! functions. Dispatch is a `match` inside each method — branch-
//! predictable and inlinable — instead of a vtable call.
//!
//! Each variant exists only when its feature flag is on; the match
//! arms inside the trait impls are gated the same way.
//!
//! Both enums carry mixed `&` and `&mut` variants in one type — calling
//! [`NDIndex::set`] on a non-mutable variant panics (mirroring the
//! underlying type, e.g. `Csr` already panics on `set`).
//!
//! # Example
//!
//! ```
//! # #[cfg(not(all(feature = "dense", feature = "csr")))] fn main() {}
//! # #[cfg(all(feature = "dense", feature = "csr"))] fn main() {
//! use linalg::any::Tensor;
//! use linalg::csr::Csr;
//! use linalg::dense::Dense;
//! use linalg::einsum::einsum_homogenous;
//! use linalg::tensor::NDIndex;
//!
//! let a = Csr::<u32, f32>::from_coo(3, &mut vec![
//!     (0, 1, 1.0), (1, 2, 1.0), (2, 0, 1.0),
//! ]);
//! let mut x = Dense::<f32>::zeros(vec![3, 2]);
//! x.fill_from(&[1., 2., 3., 4., 5., 6.]);
//! let mut y = Dense::<f32>::zeros(vec![3, 2]);
//!
//! // Mix sparse and dense inputs through one enum type — no &dyn.
//! einsum_homogenous::<f32, Tensor<f32>, Tensor<f32>>(
//!     "ab,bc->ac",
//!     &[&Tensor::Csr(&a), &Tensor::Dense(&x)],
//!     &mut [&mut Tensor::DenseMut(&mut y)],
//! ).unwrap();
//!
//! assert_eq!(y.get(&[0, 0]), 3.0);
//! # }
//! ```

#[cfg(feature = "blocked")]
use crate::blocked::{Blocked16, Blocked8};
use crate::csr::{Csr, Value};
#[cfg(feature = "dense")]
use crate::dense::Dense;
use crate::tensor::{NDIndex, Sparse2D};

// ─────────────────────────────────────────────────────────────────────────
// Tensor<'a, T> — generic over value type
// ─────────────────────────────────────────────────────────────────────────

/// Borrowed handle to any T-generic tensor type in this crate.
///
/// Holds shared or exclusive references; calling [`NDIndex::set`] on a
/// shared variant panics. Module is gated on the `csr` feature because
/// the Csr arm's `Value` bound is what the impl's bound rests on; if
/// you only have `dense` you can call einsum on `Dense<T>` directly.
pub enum Tensor<'a, T> {
    #[cfg(feature = "dense")]
    Dense(&'a Dense<T>),
    #[cfg(feature = "dense")]
    DenseMut(&'a mut Dense<T>),
    Csr(&'a Csr<u32, T>),
}

impl<'a, T: Value + 'static> NDIndex<T> for Tensor<'a, T> {
    fn ndim(&self) -> usize {
        match self {
            #[cfg(feature = "dense")]
            Tensor::Dense(d) => d.ndim(),
            #[cfg(feature = "dense")]
            Tensor::DenseMut(d) => d.ndim(),
            Tensor::Csr(c) => c.ndim(),
        }
    }

    fn dim(&self, axis: usize) -> usize {
        match self {
            #[cfg(feature = "dense")]
            Tensor::Dense(d) => d.dim(axis),
            #[cfg(feature = "dense")]
            Tensor::DenseMut(d) => d.dim(axis),
            Tensor::Csr(c) => c.dim(axis),
        }
    }

    fn get(&self, ix: &[usize]) -> T {
        match self {
            #[cfg(feature = "dense")]
            Tensor::Dense(d) => d.get(ix),
            #[cfg(feature = "dense")]
            Tensor::DenseMut(d) => d.get(ix),
            Tensor::Csr(c) => NDIndex::get(*c, ix),
        }
    }

    fn get_opt(&self, ix: &[usize]) -> Option<T> {
        match self {
            #[cfg(feature = "dense")]
            Tensor::Dense(d) => d.get_opt(ix),
            #[cfg(feature = "dense")]
            Tensor::DenseMut(d) => d.get_opt(ix),
            Tensor::Csr(c) => NDIndex::get_opt(*c, ix),
        }
    }

    fn set(&mut self, ix: &[usize], v: T) {
        match self {
            #[cfg(feature = "dense")]
            Tensor::DenseMut(d) => d.set(ix, v),
            #[cfg(feature = "dense")]
            Tensor::Dense(_) => panic!("set on shared Tensor::Dense"),
            Tensor::Csr(_) => panic!("Csr is immutable after construction"),
        }
    }

    fn as_sparse_2d(&self) -> Option<&dyn Sparse2D<T>> {
        match self {
            #[cfg(feature = "dense")]
            Tensor::Dense(_) | Tensor::DenseMut(_) => None,
            Tensor::Csr(c) => NDIndex::as_sparse_2d(*c),
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────
// TensorF32<'a> — f32-specialised, includes Blocked variants
// ─────────────────────────────────────────────────────────────────────────

/// Borrowed handle to any f32 tensor in this crate, including the
/// block-sparse variants which are only defined for f32.
pub enum TensorF32<'a> {
    #[cfg(feature = "dense")]
    Dense(&'a Dense<f32>),
    #[cfg(feature = "dense")]
    DenseMut(&'a mut Dense<f32>),
    Csr(&'a Csr<u32, f32>),
    #[cfg(feature = "blocked")]
    Blocked8(&'a Blocked8),
    #[cfg(feature = "blocked")]
    Blocked8Mut(&'a mut Blocked8),
    #[cfg(feature = "blocked")]
    Blocked16(&'a Blocked16),
    #[cfg(feature = "blocked")]
    Blocked16Mut(&'a mut Blocked16),
}

impl<'a> NDIndex<f32> for TensorF32<'a> {
    fn ndim(&self) -> usize {
        match self {
            #[cfg(feature = "dense")]
            TensorF32::Dense(d) => d.ndim(),
            #[cfg(feature = "dense")]
            TensorF32::DenseMut(d) => d.ndim(),
            
            TensorF32::Csr(c) => c.ndim(),
            #[cfg(feature = "blocked")]
            TensorF32::Blocked8(b) => b.ndim(),
            #[cfg(feature = "blocked")]
            TensorF32::Blocked8Mut(b) => b.ndim(),
            #[cfg(feature = "blocked")]
            TensorF32::Blocked16(b) => b.ndim(),
            #[cfg(feature = "blocked")]
            TensorF32::Blocked16Mut(b) => b.ndim(),
        }
    }

    fn dim(&self, axis: usize) -> usize {
        match self {
            #[cfg(feature = "dense")]
            TensorF32::Dense(d) => d.dim(axis),
            #[cfg(feature = "dense")]
            TensorF32::DenseMut(d) => d.dim(axis),
            
            TensorF32::Csr(c) => c.dim(axis),
            #[cfg(feature = "blocked")]
            TensorF32::Blocked8(b) => b.dim(axis),
            #[cfg(feature = "blocked")]
            TensorF32::Blocked8Mut(b) => b.dim(axis),
            #[cfg(feature = "blocked")]
            TensorF32::Blocked16(b) => b.dim(axis),
            #[cfg(feature = "blocked")]
            TensorF32::Blocked16Mut(b) => b.dim(axis),
        }
    }

    fn get(&self, ix: &[usize]) -> f32 {
        match self {
            #[cfg(feature = "dense")]
            TensorF32::Dense(d) => d.get(ix),
            #[cfg(feature = "dense")]
            TensorF32::DenseMut(d) => d.get(ix),
            
            TensorF32::Csr(c) => NDIndex::get(*c, ix),
            #[cfg(feature = "blocked")]
            TensorF32::Blocked8(b) => b.get(ix),
            #[cfg(feature = "blocked")]
            TensorF32::Blocked8Mut(b) => b.get(ix),
            #[cfg(feature = "blocked")]
            TensorF32::Blocked16(b) => b.get(ix),
            #[cfg(feature = "blocked")]
            TensorF32::Blocked16Mut(b) => b.get(ix),
        }
    }

    fn get_opt(&self, ix: &[usize]) -> Option<f32> {
        match self {
            #[cfg(feature = "dense")]
            TensorF32::Dense(d) => d.get_opt(ix),
            #[cfg(feature = "dense")]
            TensorF32::DenseMut(d) => d.get_opt(ix),
            
            TensorF32::Csr(c) => NDIndex::get_opt(*c, ix),
            #[cfg(feature = "blocked")]
            TensorF32::Blocked8(b) => b.get_opt(ix),
            #[cfg(feature = "blocked")]
            TensorF32::Blocked8Mut(b) => b.get_opt(ix),
            #[cfg(feature = "blocked")]
            TensorF32::Blocked16(b) => b.get_opt(ix),
            #[cfg(feature = "blocked")]
            TensorF32::Blocked16Mut(b) => b.get_opt(ix),
        }
    }

    fn set(&mut self, ix: &[usize], v: f32) {
        match self {
            #[cfg(feature = "dense")]
            TensorF32::DenseMut(d) => d.set(ix, v),
            #[cfg(feature = "blocked")]
            TensorF32::Blocked8Mut(b) => b.set(ix, v),
            #[cfg(feature = "blocked")]
            TensorF32::Blocked16Mut(b) => b.set(ix, v),
            #[cfg(feature = "dense")]
            TensorF32::Dense(_) => panic!("set on shared TensorF32::Dense"),
            
            TensorF32::Csr(_) => panic!("Csr is immutable after construction"),
            #[cfg(feature = "blocked")]
            TensorF32::Blocked8(_) => panic!("set on shared TensorF32::Blocked8"),
            #[cfg(feature = "blocked")]
            TensorF32::Blocked16(_) => panic!("set on shared TensorF32::Blocked16"),
        }
    }

    fn as_sparse_2d(&self) -> Option<&dyn Sparse2D<f32>> {
        match self {
            
            TensorF32::Csr(c) => NDIndex::as_sparse_2d(*c),
            _ => None,
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────
// Tests
// ─────────────────────────────────────────────────────────────────────────

#[cfg(all(test, feature = "dense", feature = "csr"))]
mod tests {
    use super::*;
    use crate::einsum::einsum_homogenous;

    #[test]
    fn tensor_csr_x_dense_via_einsum() {
        let a = Csr::<u32, f32>::from_coo(3, &mut vec![
            (0, 1, 1.0), (1, 2, 1.0), (2, 0, 1.0),
        ]);
        let mut x = Dense::<f32>::zeros(vec![3, 2]);
        x.fill_from(&[1., 2., 3., 4., 5., 6.]);
        let mut y = Dense::<f32>::zeros(vec![3, 2]);

        einsum_homogenous::<f32, Tensor<f32>, Tensor<f32>>(
            "ab,bc->ac",
            &[&Tensor::Csr(&a), &Tensor::Dense(&x)],
            &mut [&mut Tensor::DenseMut(&mut y)],
        )
        .unwrap();

        // row i of y = row (i+1 mod 3) of x because the triangle sends i → i+1
        assert_eq!(y.get(&[0, 0]), 3.0);
        assert_eq!(y.get(&[1, 1]), 6.0);
        assert_eq!(y.get(&[2, 0]), 1.0);
    }

    #[test]
    fn tensor_sparse_2d_dispatch_routes_to_csr() {
        let a = Csr::<u32, f32>::from_coo(3, &mut vec![(0, 1, 1.0)]);
        let dense = Dense::<f32>::zeros(vec![3, 3]);
        let t_csr = Tensor::Csr(&a);
        let t_dense = Tensor::Dense(&dense);
        assert!(t_csr.as_sparse_2d().is_some(), "Csr variant should expose Sparse2D");
        assert!(t_dense.as_sparse_2d().is_none(), "Dense variant should not");
    }

    #[test]
    #[should_panic(expected = "set on shared")]
    fn tensor_set_panics_on_shared_variant() {
        let d = Dense::<f32>::zeros(vec![2, 2]);
        let mut t = Tensor::Dense(&d);
        t.set(&[0, 0], 1.0);
    }

    #[test]
    #[cfg(feature = "blocked")]
    fn tensor_f32_includes_blocked_variants() {
        use crate::blocked::Blocked8;
        let b = Blocked8::with_shape(vec![1, 1, 8, 8]);
        let t = TensorF32::Blocked8(&b);
        assert_eq!(t.ndim(), 4);
        assert!(t.as_sparse_2d().is_none());
    }
}
