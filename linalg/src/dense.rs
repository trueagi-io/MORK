//! Flat row-major dense tensor.
//!
//! [`Dense<T>`] is the simplest [`NDIndex`] implementation: a `Vec<T>` plus
//! a shape vector, with standard row-major (C-order) layout. Use it as
//! input or output to [`crate::einsum`] when you don't need a more
//! specialised storage format.
//!
//! # Example
//!
//! ```
//! use linalg::dense::Dense;
//! use linalg::tensor::NDIndex;
//!
//! let mut a = Dense::<f32>::zeros(vec![2, 3]);
//! a.fill_from(&[1.0, 2.0, 3.0, 4.0, 5.0, 6.0]);
//!
//! assert_eq!(a.get(&[0, 0]), 1.0);
//! assert_eq!(a.get(&[1, 2]), 6.0);
//! ```

use crate::tensor::NDIndex;

/// Row-major dense tensor.
#[derive(Clone, Debug)]
pub struct Dense<T> {
    pub data: Vec<T>,
    pub shape: Vec<usize>,
}

impl<T: Default + Clone> Dense<T> {
    /// Construct a zero-filled tensor of the given shape.
    ///
    /// For a 0-dimensional (scalar) tensor, pass `vec![]` — the storage
    /// holds a single element accessed via `&[]`.
    pub fn zeros(shape: Vec<usize>) -> Self {
        let n: usize = if shape.is_empty() { 1 } else { shape.iter().product() };
        Self { data: vec![T::default(); n], shape }
    }
}

impl<T: Clone> Dense<T> {
    /// Overwrite all elements from a flat slice in row-major order.
    /// Panics if `src.len() != self.data.len()`.
    pub fn fill_from(&mut self, src: &[T]) {
        assert_eq!(
            src.len(),
            self.data.len(),
            "fill_from: length {} != storage {}",
            src.len(),
            self.data.len()
        );
        self.data.clone_from_slice(src);
    }
}

impl<T: Default + Clone> Dense<T> {
    /// Zero all elements without reallocating.
    pub fn clear(&mut self) {
        for v in &mut self.data {
            *v = T::default();
        }
    }
}

impl<T> Dense<T> {
    #[inline]
    fn linear_index(&self, ix: &[usize]) -> usize {
        debug_assert_eq!(ix.len(), self.shape.len(), "rank mismatch");
        let mut idx = 0usize;
        let mut stride = 1usize;
        for (&k, &dim) in ix.iter().rev().zip(self.shape.iter().rev()) {
            debug_assert!(k < dim, "index out of bounds");
            idx += k * stride;
            stride *= dim;
        }
        idx
    }
}

impl<T: Copy + Default> NDIndex<T> for Dense<T> {
    fn ndim(&self) -> usize {
        self.shape.len()
    }
    fn dim(&self, axis: usize) -> usize {
        self.shape[axis]
    }
    fn get(&self, ix: &[usize]) -> T {
        if self.shape.is_empty() {
            self.data[0]
        } else {
            self.data[self.linear_index(ix)]
        }
    }
    fn set(&mut self, ix: &[usize], v: T) {
        if self.shape.is_empty() {
            self.data[0] = v;
        } else {
            let i = self.linear_index(ix);
            self.data[i] = v;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn zeros_and_round_trip() {
        let mut a = Dense::<f32>::zeros(vec![2, 3]);
        a.set(&[0, 0], 1.0);
        a.set(&[0, 1], 2.0);
        a.set(&[1, 2], 6.0);

        assert_eq!(a.get(&[0, 0]), 1.0);
        assert_eq!(a.get(&[0, 1]), 2.0);
        assert_eq!(a.get(&[1, 2]), 6.0);
        assert_eq!(a.get(&[1, 0]), 0.0);
    }

    #[test]
    fn fill_from_row_major() {
        let mut a = Dense::<f32>::zeros(vec![2, 3]);
        a.fill_from(&[1.0, 2.0, 3.0, 4.0, 5.0, 6.0]);
        assert_eq!(a.get(&[0, 2]), 3.0);
        assert_eq!(a.get(&[1, 0]), 4.0);
    }

    #[test]
    fn clear_zeroes() {
        let mut a = Dense::<f32>::zeros(vec![2, 2]);
        a.fill_from(&[1.0, 2.0, 3.0, 4.0]);
        a.clear();
        assert_eq!(a.data, vec![0.0; 4]);
    }

    #[test]
    fn scalar_zero_dim() {
        let mut s = Dense::<f32>::zeros(vec![]);
        assert_eq!(NDIndex::ndim(&s), 0);
        assert_eq!(s.get(&[]), 0.0);
        s.set(&[], 42.0);
        assert_eq!(s.get(&[]), 42.0);
    }
}
