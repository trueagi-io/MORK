//! Sparse and dense linear algebra: CSR SpGEMM, block-sparse SIMD attention,
//! and a runtime einsum VM that composes over both via a small trait pair.
//!
//! # Modules
//!
//! - [`tensor`] — [`NDIndex`](tensor::NDIndex) and [`Sparse2D`](tensor::Sparse2D)
//!   traits. The universal interface.
//! - [`dense`] (feature `dense`) — flat row-major [`Dense<T>`](dense::Dense).
//! - [`csr`] (feature `csr`) — [`Csr`](csr::Csr) compressed sparse row matrix
//!   with sequential and rayon-parallel SpGEMM.
//! - [`blocked`] (feature `blocked`) — [`Blocked<N>`](blocked::Blocked)
//!   block-sparse tensor with AVX2+FMA kernels for attention.
//! - [`einsum`] — VM-based einsum supporting arbitrary specs and mixed
//!   sparse/dense inputs via [`einsum`](einsum::einsum) /
//!   [`einsum_homogenous`](einsum::einsum_homogenous).
//!
//! # Quick example: CSR × Dense via einsum
//!
//! Requires the `dense` and `csr` features (both on by default).
//!
//! ```
//! # #[cfg(not(all(feature = "dense", feature = "csr")))] fn main() {}
//! # #[cfg(all(feature = "dense", feature = "csr"))] fn main() {
//! use linalg::{einsum::einsum, tensor::NDIndex, dense::Dense, csr::Csr};
//!
//! // 3x3 sparse adjacency
//! let a = Csr::<u32, f32>::from_coo(3, &mut vec![
//!     (0, 1, 1.0), (1, 2, 1.0), (2, 0, 1.0),
//! ]);
//!
//! // 3x2 dense features
//! let mut x = Dense::<f32>::zeros(vec![3, 2]);
//! x.fill_from(&[1.0, 2.0,  3.0, 4.0,  5.0, 6.0]);
//!
//! let mut y = Dense::<f32>::zeros(vec![3, 2]);
//!
//! einsum::<f32>(
//!     "ab,bc->ac",
//!     &[&a as &dyn NDIndex<f32>, &x],
//!     &mut [&mut y as &mut dyn NDIndex<f32>],
//! ).unwrap();
//!
//! assert_eq!(y.get(&[0, 0]), 3.0);  // row 0 picks up row 1 of x
//! assert_eq!(y.get(&[1, 1]), 6.0);  // row 1 picks up row 2 of x
//! assert_eq!(y.get(&[2, 0]), 1.0);  // row 2 picks up row 0 of x
//! # }
//! ```

pub mod tensor;

#[cfg(feature = "dense")]
pub mod dense;

#[cfg(feature = "csr")]
pub mod csr;

#[cfg(feature = "blocked")]
pub mod blocked;

pub mod einsum;

#[cfg(feature = "csr")]
pub mod any;

#[cfg(feature = "jit")]
pub mod jit;
