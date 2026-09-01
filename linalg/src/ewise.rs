//! Element-wise in-place binary operations on [`Dense<T>`].
//!
//! These combine two tensors of **identical shape** element-by-element,
//! writing the result back into the left-hand operand (`self`) without
//! allocating. They are the tensor analogue of the scalar compound
//! assignment operators (`+=`, `-=`, `*=`, `/=`, `%=`) plus `pow`.
//!
//! Two spellings are provided:
//!
//! * **Operators** — the standard `std::ops` compound-assignment traits are
//!   implemented for a `&Dense<T>` right-hand side, so you can write the
//!   arithmetic directly:
//!
//!   ```
//!   use linalg::dense::Dense;
//!
//!   let mut a = Dense::<f32>::zeros(vec![2, 2]);
//!   a.fill_from(&[1.0, 2.0, 3.0, 4.0]);
//!   let mut b = Dense::<f32>::zeros(vec![2, 2]);
//!   b.fill_from(&[10.0, 20.0, 30.0, 40.0]);
//!
//!   a += &b;
//!   assert_eq!(a.data, vec![11.0, 22.0, 33.0, 44.0]);
//!   ```
//!
//! * **Named methods** — [`Dense::add_assign_tensor`] and friends, plus the
//!   generic [`Dense::zip_assign`] combinator they are all built on. `pow`
//!   is only available as a method ([`Dense::pow_assign`]) since there is no
//!   compound-assignment operator for it.
//!
//! Every operation panics if the two shapes differ.

use crate::dense::Dense;
use std::ops::{
    Add, AddAssign, Div, DivAssign, Mul, MulAssign, Rem, RemAssign, Sub, SubAssign,
};

impl<T: Copy> Dense<T> {
    /// Combine `self` with `other` element-wise, in place: each element
    /// becomes `f(self_elem, other_elem)`.
    ///
    /// This is the shared primitive behind every element-wise in-place
    /// binary op. Panics if the shapes differ.
    #[inline]
    pub fn zip_assign<F>(&mut self, other: &Dense<T>, mut f: F)
    where
        F: FnMut(T, T) -> T,
    {
        assert_eq!(
            self.shape, other.shape,
            "zip_assign: shape mismatch {:?} vs {:?}",
            self.shape, other.shape
        );
        for (a, &b) in self.data.iter_mut().zip(other.data.iter()) {
            *a = f(*a, b);
        }
    }
}

/// Generate an inherent named method + the matching `std::ops` compound
/// assignment trait impl for one binary operator. `$op` is the infix
/// operator token spliced into the per-element closure.
macro_rules! ewise_binop {
    ($method:ident, $trait:ident, $trait_method:ident, $bound:ident, $op:tt, $doc:literal) => {
        impl<T: Copy + $bound<Output = T>> Dense<T> {
            #[doc = $doc]
            ///
            /// Panics if the two shapes differ.
            #[inline]
            pub fn $method(&mut self, other: &Dense<T>) {
                self.zip_assign(other, |a, b| a $op b);
            }
        }

        impl<T: Copy + $bound<Output = T>> $trait<&Dense<T>> for Dense<T> {
            #[inline]
            fn $trait_method(&mut self, other: &Dense<T>) {
                self.$method(other);
            }
        }
    };
}

ewise_binop!(
    add_assign_tensor,
    AddAssign,
    add_assign,
    Add,
    +,
    "Element-wise `self += other` (in place)."
);
ewise_binop!(
    sub_assign_tensor,
    SubAssign,
    sub_assign,
    Sub,
    -,
    "Element-wise `self -= other` (in place)."
);
ewise_binop!(
    mul_assign_tensor,
    MulAssign,
    mul_assign,
    Mul,
    *,
    "Element-wise `self *= other` (in place)."
);
ewise_binop!(
    div_assign_tensor,
    DivAssign,
    div_assign,
    Div,
    /,
    "Element-wise `self /= other` (in place)."
);
ewise_binop!(
    rem_assign_tensor,
    RemAssign,
    rem_assign,
    Rem,
    %,
    "Element-wise `self %= other` (remainder, in place)."
);

/// Element-wise exponentiation: raise each element to the power of the
/// corresponding element of another tensor.
///
/// Implemented for the floating-point types (`f32`, `f64`) via their
/// `powf` method. There is no compound-assignment operator for `pow`, so
/// this is method-only.
pub trait Pow {
    /// Returns `self` raised to the power `exp`.
    fn pow(self, exp: Self) -> Self;
}

impl Pow for f32 {
    #[inline]
    fn pow(self, exp: Self) -> Self {
        self.powf(exp)
    }
}

impl Pow for f64 {
    #[inline]
    fn pow(self, exp: Self) -> Self {
        self.powf(exp)
    }
}

impl<T: Copy + Pow> Dense<T> {
    /// Element-wise `self = self.pow(other)` (in place): each element is
    /// raised to the power of the corresponding element of `other`.
    ///
    /// Panics if the two shapes differ.
    #[inline]
    pub fn pow_assign(&mut self, other: &Dense<T>) {
        self.zip_assign(other, |a, b| a.pow(b));
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn d(shape: Vec<usize>, vals: &[f32]) -> Dense<f32> {
        let mut t = Dense::<f32>::zeros(shape);
        t.fill_from(vals);
        t
    }

    #[test]
    fn operators_match_named_methods() {
        let base = d(vec![2, 2], &[1.0, 2.0, 3.0, 4.0]);
        let rhs = d(vec![2, 2], &[5.0, 6.0, 7.0, 8.0]);

        let mut a = base.clone();
        a += &rhs;
        let mut b = base.clone();
        b.add_assign_tensor(&rhs);
        assert_eq!(a.data, b.data);
        assert_eq!(a.data, vec![6.0, 8.0, 10.0, 12.0]);
    }

    #[test]
    fn sub_mul_div_rem() {
        let mut a = d(vec![4], &[10.0, 20.0, 30.0, 40.0]);
        a -= &d(vec![4], &[1.0, 2.0, 3.0, 4.0]);
        assert_eq!(a.data, vec![9.0, 18.0, 27.0, 36.0]);

        let mut m = d(vec![4], &[1.0, 2.0, 3.0, 4.0]);
        m *= &d(vec![4], &[2.0, 3.0, 4.0, 5.0]);
        assert_eq!(m.data, vec![2.0, 6.0, 12.0, 20.0]);

        let mut q = d(vec![4], &[10.0, 9.0, 8.0, 12.0]);
        q /= &d(vec![4], &[2.0, 3.0, 4.0, 6.0]);
        assert_eq!(q.data, vec![5.0, 3.0, 2.0, 2.0]);

        let mut r = d(vec![4], &[10.0, 9.0, 8.0, 7.0]);
        r.rem_assign_tensor(&d(vec![4], &[3.0, 3.0, 3.0, 3.0]));
        assert_eq!(r.data, vec![1.0, 0.0, 2.0, 1.0]);
    }

    #[test]
    fn pow_elementwise() {
        let mut a = d(vec![3], &[2.0, 3.0, 4.0]);
        a.pow_assign(&d(vec![3], &[3.0, 2.0, 0.5]));
        assert_eq!(a.data, vec![8.0, 9.0, 2.0]);
    }

    #[test]
    fn works_for_f64_and_integers() {
        // f64 pow
        let mut a = Dense::<f64>::zeros(vec![2]);
        a.fill_from(&[2.0, 9.0]);
        let mut e = Dense::<f64>::zeros(vec![2]);
        e.fill_from(&[10.0, 0.5]);
        a.pow_assign(&e);
        assert_eq!(a.data, vec![1024.0, 3.0]);

        // integer arithmetic ops (no pow — Pow is float-only)
        let mut i = Dense::<i32>::zeros(vec![3]);
        i.fill_from(&[10, 20, 30]);
        let mut j = Dense::<i32>::zeros(vec![3]);
        j.fill_from(&[1, 2, 3]);
        i += &j;
        assert_eq!(i.data, vec![11, 22, 33]);
    }

    #[test]
    #[should_panic(expected = "shape mismatch")]
    fn shape_mismatch_panics() {
        let mut a = d(vec![2, 2], &[1.0, 2.0, 3.0, 4.0]);
        let b = d(vec![4], &[1.0, 2.0, 3.0, 4.0]);
        a += &b;
    }
}
