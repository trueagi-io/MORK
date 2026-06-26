//! In-place scalar (element-wise) transforms for tensors.
//!
//! [`ScalarTransform`] applies a unary math function to every stored element
//! of a tensor, in place. It is implemented for [`Dense`](crate::dense::Dense)
//! and [`Csr`](crate::csr::Csr).
//!
//! An implementor exposes its elements as one or more **contiguous chunks**
//! (via [`for_each_chunk`](ScalarTransform::for_each_chunk)), not a single
//! flat slice — so storage that is not one buffer (e.g. the block-sparse
//! [`Blocked`](crate::blocked::Blocked), strided views, tiled/padded layouts)
//! can participate too. A single-buffer tensor simply yields one chunk; MKL
//! still sees the whole array.
//!
//! For a sparse [`Csr`](crate::csr::Csr) the transform only touches the
//! **stored non-zeros** — structural zeros are left implicit and unchanged.
//! Functions that do not fix zero (e.g. [`cos`](ScalarTransform::cos),
//! [`exp`](ScalarTransform::exp)) therefore do *not* densify the matrix; they
//! map the explicit entries only. This is the right behaviour for activation /
//! reweighting passes and keeps the storage sparse.
//!
//! # The `intel-mkl` feature
//!
//! The actual per-element work is delegated to the [`MathScalar`] trait, which
//! is implemented for `f32` and `f64`. With the default build the slice
//! functions loop over [`std`] math methods. With the `intel-mkl` feature the
//! unary transcendentals and [`powf`](ScalarTransform::powf) are dispatched to
//! Intel MKL's Vector Math Library (VML) batch kernels (`vsSin`, `vdExp`,
//! `vsPowx`, …), which evaluate a whole array at once. The `intel-mkl-src`
//! build dependency provisions and statically links MKL automatically (it
//! downloads a redistributable build on first compile), so the feature needs
//! no system MKL install or link-time configuration.
//!
//! # Example
//!
//! ```
//! use linalg::dense::Dense;
//! use linalg::scalar::ScalarTransform;
//!
//! let mut a = Dense::<f32>::zeros(vec![2, 2]);
//! a.fill_from(&[-1.0, 4.0, 9.0, -16.0]);
//! a.abs();   // |x|
//! a.sqrt();  // √x
//! assert_eq!(a.data, vec![1.0, 2.0, 3.0, 4.0]);
//! ```

// ─────────────────────────────────────────────────────────────────────────
// MKL VML bindings (only when the `intel-mkl` feature is on)
// ─────────────────────────────────────────────────────────────────────────

// Pull in `intel-mkl-src`: its build script downloads and links a
// redistributable MKL, providing the symbols declared below. The `as _`
// import exists only to force the linkage (the crate exposes no items).
#[cfg(feature = "intel-mkl")]
use intel_mkl_src as _;

#[cfg(feature = "intel-mkl")]
mod mkl {
    //! Raw bindings to the subset of Intel MKL's Vector Math Library used
    //! here. Each `v?Fn(n, a, y)` computes `y[i] = fn(a[i])` for `i in 0..n`;
    //! in-place evaluation (`a == y`) is supported by VML. `v?Powx` takes a
    //! scalar exponent. `MKL_INT` is 32-bit under the LP64 interface that the
    //! `intel-mkl` feature selects (`mkl-dynamic-lp64-iomp`).
    unsafe extern "C" {
        pub fn vsAbs(n: i32, a: *const f32, y: *mut f32);
        pub fn vsSin(n: i32, a: *const f32, y: *mut f32);
        pub fn vsCos(n: i32, a: *const f32, y: *mut f32);
        pub fn vsTan(n: i32, a: *const f32, y: *mut f32);
        pub fn vsAsin(n: i32, a: *const f32, y: *mut f32);
        pub fn vsAcos(n: i32, a: *const f32, y: *mut f32);
        pub fn vsAtan(n: i32, a: *const f32, y: *mut f32);
        pub fn vsSqrt(n: i32, a: *const f32, y: *mut f32);
        pub fn vsCbrt(n: i32, a: *const f32, y: *mut f32);
        pub fn vsLn(n: i32, a: *const f32, y: *mut f32);
        pub fn vsExp(n: i32, a: *const f32, y: *mut f32);
        pub fn vsPowx(n: i32, a: *const f32, b: f32, y: *mut f32);

        pub fn vdAbs(n: i32, a: *const f64, y: *mut f64);
        pub fn vdSin(n: i32, a: *const f64, y: *mut f64);
        pub fn vdCos(n: i32, a: *const f64, y: *mut f64);
        pub fn vdTan(n: i32, a: *const f64, y: *mut f64);
        pub fn vdAsin(n: i32, a: *const f64, y: *mut f64);
        pub fn vdAcos(n: i32, a: *const f64, y: *mut f64);
        pub fn vdAtan(n: i32, a: *const f64, y: *mut f64);
        pub fn vdSqrt(n: i32, a: *const f64, y: *mut f64);
        pub fn vdCbrt(n: i32, a: *const f64, y: *mut f64);
        pub fn vdLn(n: i32, a: *const f64, y: *mut f64);
        pub fn vdExp(n: i32, a: *const f64, y: *mut f64);
        pub fn vdPowx(n: i32, a: *const f64, b: f64, y: *mut f64);
    }
}

/// In-place VML unary call, chunked so length never overflows `MKL_INT`.
///
/// # Safety
/// `f` must be a VML `v?Fn(n, a, y)` kernel matching `T`. `a == y` (in place)
/// is permitted by VML.
#[cfg(feature = "intel-mkl")]
#[inline]
unsafe fn vml_unary<T>(xs: &mut [T], f: unsafe extern "C" fn(i32, *const T, *mut T)) {
    let mut off = 0usize;
    while off < xs.len() {
        let n = (xs.len() - off).min(i32::MAX as usize);
        let p = unsafe { xs.as_mut_ptr().add(off) };
        unsafe { f(n as i32, p, p) };
        off += n;
    }
}

/// In-place VML power call (`y[i] = a[i] ** b`), chunked as in [`vml_unary`].
///
/// # Safety
/// `f` must be a `v?Powx` kernel matching `T`.
#[cfg(feature = "intel-mkl")]
#[inline]
unsafe fn vml_powx<T: Copy>(xs: &mut [T], b: T, f: unsafe extern "C" fn(i32, *const T, T, *mut T)) {
    let mut off = 0usize;
    while off < xs.len() {
        let n = (xs.len() - off).min(i32::MAX as usize);
        let p = unsafe { xs.as_mut_ptr().add(off) };
        unsafe { f(n as i32, p, b, p) };
        off += n;
    }
}

// ─────────────────────────────────────────────────────────────────────────
// Per-element backend
// ─────────────────────────────────────────────────────────────────────────

/// Slice-level math backend for a scalar element type.
///
/// Implemented for `f32` and `f64`. Every method rewrites the slice in place.
/// The implementation is selected at compile time: plain [`std`] math by
/// default, Intel MKL VML kernels under the `intel-mkl` feature for the unary
/// transcendentals and [`powf`](MathScalar::powf).
pub trait MathScalar: Copy {
    /// `x ← |x|`
    fn abs(xs: &mut [Self]);
    /// `x ← sin(x)`
    fn sin(xs: &mut [Self]);
    /// `x ← cos(x)`
    fn cos(xs: &mut [Self]);
    /// `x ← tan(x)`
    fn tan(xs: &mut [Self]);
    /// `x ← asin(x)`
    fn asin(xs: &mut [Self]);
    /// `x ← acos(x)`
    fn acos(xs: &mut [Self]);
    /// `x ← atan(x)`
    fn atan(xs: &mut [Self]);
    /// `x ← atan2(x, v)`
    fn atan2(xs: &mut [Self], v: Self);
    /// `x ← √x`
    fn sqrt(xs: &mut [Self]);
    /// `x ← ∛x`
    fn cbrt(xs: &mut [Self]);
    /// `x ← ln(x)`
    fn ln(xs: &mut [Self]);
    /// `x ← eˣ`
    fn exp(xs: &mut [Self]);
    /// `x ← xᵛ` (real exponent)
    fn powf(xs: &mut [Self], v: Self);
    /// `x ← xⁿ` (integer exponent)
    fn powi(xs: &mut [Self], n: i32);
    /// `x ← min(x, v)`
    fn min(xs: &mut [Self], v: Self);
    /// `x ← max(x, v)`
    fn max(xs: &mut [Self], v: Self);
    /// `x ← clamp(x, lo, hi)`
    fn clamp(xs: &mut [Self], lo: Self, hi: Self);
}

/// Expands to an in-place unary map: MKL VML kernel with the feature, a `std`
/// loop without it. `$mkl` is only referenced inside the feature-gated branch,
/// so its path need not resolve when the feature is off.
macro_rules! map_unary {
    ($xs:expr, $mkl:expr, $scalar:expr) => {{
        #[cfg(feature = "intel-mkl")]
        unsafe {
            vml_unary($xs, $mkl)
        }
        #[cfg(not(feature = "intel-mkl"))]
        {
            let f = $scalar;
            for x in $xs.iter_mut() {
                *x = f(*x);
            }
        }
    }};
}

/// Emit a [`MathScalar`] impl for one float type, wiring each unary transform
/// to its VML kernel (used only under `intel-mkl`) and `std` fallback.
macro_rules! impl_math_scalar {
    ($t:ty,
     $abs:expr, $sin:expr, $cos:expr, $tan:expr,
     $asin:expr, $acos:expr, $atan:expr,
     $sqrt:expr, $cbrt:expr, $ln:expr, $exp:expr, $powx:expr) => {
        impl MathScalar for $t {
            #[inline]
            fn abs(xs: &mut [Self]) { map_unary!(xs, $abs, |x: $t| x.abs()); }
            #[inline]
            fn sin(xs: &mut [Self]) { map_unary!(xs, $sin, |x: $t| x.sin()); }
            #[inline]
            fn cos(xs: &mut [Self]) { map_unary!(xs, $cos, |x: $t| x.cos()); }
            #[inline]
            fn tan(xs: &mut [Self]) { map_unary!(xs, $tan, |x: $t| x.tan()); }
            #[inline]
            fn asin(xs: &mut [Self]) { map_unary!(xs, $asin, |x: $t| x.asin()); }
            #[inline]
            fn acos(xs: &mut [Self]) { map_unary!(xs, $acos, |x: $t| x.acos()); }
            #[inline]
            fn atan(xs: &mut [Self]) { map_unary!(xs, $atan, |x: $t| x.atan()); }
            #[inline]
            fn sqrt(xs: &mut [Self]) { map_unary!(xs, $sqrt, |x: $t| x.sqrt()); }
            #[inline]
            fn cbrt(xs: &mut [Self]) { map_unary!(xs, $cbrt, |x: $t| x.cbrt()); }
            #[inline]
            fn ln(xs: &mut [Self]) { map_unary!(xs, $ln, |x: $t| x.ln()); }
            #[inline]
            fn exp(xs: &mut [Self]) { map_unary!(xs, $exp, |x: $t| x.exp()); }

            #[inline]
            fn powf(xs: &mut [Self], v: Self) {
                #[cfg(feature = "intel-mkl")]
                unsafe {
                    vml_powx(xs, v, $powx)
                }
                #[cfg(not(feature = "intel-mkl"))]
                for x in xs.iter_mut() {
                    *x = x.powf(v);
                }
            }

            // `atan2` (needs a second operand) and the comparison/integer
            // transforms have no single-vector-plus-scalar VML kernel, so they
            // stay scalar in both builds — they are cheap anyway.
            #[inline]
            fn atan2(xs: &mut [Self], v: Self) {
                for x in xs.iter_mut() { *x = x.atan2(v); }
            }
            #[inline]
            fn powi(xs: &mut [Self], n: i32) {
                for x in xs.iter_mut() { *x = x.powi(n); }
            }
            #[inline]
            fn min(xs: &mut [Self], v: Self) {
                for x in xs.iter_mut() { *x = x.min(v); }
            }
            #[inline]
            fn max(xs: &mut [Self], v: Self) {
                for x in xs.iter_mut() { *x = x.max(v); }
            }
            #[inline]
            fn clamp(xs: &mut [Self], lo: Self, hi: Self) {
                for x in xs.iter_mut() { *x = x.clamp(lo, hi); }
            }
        }
    };
}

impl_math_scalar!(
    f32,
    mkl::vsAbs, mkl::vsSin, mkl::vsCos, mkl::vsTan,
    mkl::vsAsin, mkl::vsAcos, mkl::vsAtan,
    mkl::vsSqrt, mkl::vsCbrt, mkl::vsLn, mkl::vsExp, mkl::vsPowx
);
impl_math_scalar!(
    f64,
    mkl::vdAbs, mkl::vdSin, mkl::vdCos, mkl::vdTan,
    mkl::vdAsin, mkl::vdAcos, mkl::vdAtan,
    mkl::vdSqrt, mkl::vdCbrt, mkl::vdLn, mkl::vdExp, mkl::vdPowx
);

// ─────────────────────────────────────────────────────────────────────────
// Tensor-facing trait
// ─────────────────────────────────────────────────────────────────────────

/// In-place element-wise math transforms for a tensor of [`MathScalar`].
///
/// Implementors provide one method — [`for_each_chunk`](Self::for_each_chunk),
/// which hands the callback each contiguous run of stored elements — and
/// inherit every transform. Each transform rewrites the elements in place and
/// returns `&mut Self`, so calls chain:
///
/// ```
/// use linalg::dense::Dense;
/// use linalg::scalar::ScalarTransform;
///
/// let mut a = Dense::<f64>::zeros(vec![3]);
/// a.fill_from(&[-2.0, 0.5, 3.0]);
/// a.abs().clamp(0.0, 1.0);   // |x| then clamp to [0, 1]
/// assert_eq!(a.data, vec![1.0, 0.5, 1.0]);
/// ```
pub trait ScalarTransform<T: MathScalar> {
    /// Invoke `f` on every contiguous chunk of stored elements, in order.
    ///
    /// A single-buffer tensor yields exactly one chunk (the whole element
    /// slice); a multi-buffer tensor (e.g. block-sparse) yields one chunk per
    /// stored buffer. For a sparse tensor the chunks cover the stored
    /// non-zeros only — structural zeros are not materialised.
    ///
    /// Each `MathScalar` slice op is dispatched once per chunk, so the MKL
    /// batch kernels still run on whole runs rather than element-by-element.
    fn for_each_chunk(&mut self, f: impl FnMut(&mut [T]));

    /// `x ← |x|`
    #[inline]
    fn abs(&mut self) -> &mut Self { self.for_each_chunk(T::abs); self }
    /// `x ← min(x, v)` — element-wise upper-bounding cap.
    #[inline]
    fn min(&mut self, v: T) -> &mut Self { self.for_each_chunk(|c| T::min(c, v)); self }
    /// `x ← max(x, v)` — element-wise floor (e.g. `max(0.0)` is a ReLU).
    #[inline]
    fn max(&mut self, v: T) -> &mut Self { self.for_each_chunk(|c| T::max(c, v)); self }
    /// `x ← clamp(x, lo, hi)`
    #[inline]
    fn clamp(&mut self, lo: T, hi: T) -> &mut Self { self.for_each_chunk(|c| T::clamp(c, lo, hi)); self }

    /// `x ← sin(x)`
    #[inline]
    fn sin(&mut self) -> &mut Self { self.for_each_chunk(T::sin); self }
    /// `x ← cos(x)`
    #[inline]
    fn cos(&mut self) -> &mut Self { self.for_each_chunk(T::cos); self }
    /// `x ← tan(x)`
    #[inline]
    fn tan(&mut self) -> &mut Self { self.for_each_chunk(T::tan); self }
    /// `x ← asin(x)`
    #[inline]
    fn asin(&mut self) -> &mut Self { self.for_each_chunk(T::asin); self }
    /// `x ← acos(x)`
    #[inline]
    fn acos(&mut self) -> &mut Self { self.for_each_chunk(T::acos); self }
    /// `x ← atan(x)`
    #[inline]
    fn atan(&mut self) -> &mut Self { self.for_each_chunk(T::atan); self }
    /// `x ← atan2(x, v)`
    #[inline]
    fn atan2(&mut self, v: T) -> &mut Self { self.for_each_chunk(|c| T::atan2(c, v)); self }

    /// `x ← √x`
    #[inline]
    fn sqrt(&mut self) -> &mut Self { self.for_each_chunk(T::sqrt); self }
    /// `x ← ∛x`
    #[inline]
    fn cbrt(&mut self) -> &mut Self { self.for_each_chunk(T::cbrt); self }
    /// `x ← ln(x)`
    #[inline]
    fn ln(&mut self) -> &mut Self { self.for_each_chunk(T::ln); self }
    /// `x ← eˣ`
    #[inline]
    fn exp(&mut self) -> &mut Self { self.for_each_chunk(T::exp); self }

    /// `x ← xᵛ` (real exponent)
    #[inline]
    fn powf(&mut self, v: T) -> &mut Self { self.for_each_chunk(|c| T::powf(c, v)); self }
    /// `x ← xⁿ` (integer exponent)
    #[inline]
    fn powi(&mut self, n: i32) -> &mut Self { self.for_each_chunk(|c| T::powi(c, n)); self }
}

#[cfg(feature = "dense")]
impl<T: MathScalar> ScalarTransform<T> for crate::dense::Dense<T> {
    /// One chunk: the whole element buffer.
    #[inline]
    fn for_each_chunk(&mut self, mut f: impl FnMut(&mut [T])) {
        f(&mut self.data);
    }
}

#[cfg(feature = "csr")]
impl<I, T: MathScalar> ScalarTransform<T> for crate::csr::Csr<I, T> {
    /// One chunk: the stored non-zeros. Structural zeros stay implicit.
    #[inline]
    fn for_each_chunk(&mut self, mut f: impl FnMut(&mut [T])) {
        f(&mut self.values);
    }
}

// ─────────────────────────────────────────────────────────────────────────
// Tests
// ─────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    fn approx(a: &[f64], b: &[f64]) {
        assert_eq!(a.len(), b.len(), "length mismatch");
        for (i, (x, y)) in a.iter().zip(b).enumerate() {
            assert!((x - y).abs() < 1e-9, "at {i}: {x} != {y}");
        }
    }

    fn approx32(a: &[f32], b: &[f32]) {
        assert_eq!(a.len(), b.len(), "length mismatch");
        for (i, (x, y)) in a.iter().zip(b).enumerate() {
            assert!((x - y).abs() < 1e-5, "at {i}: {x} != {y}");
        }
    }

    // ── Dense, the full op surface ──

    #[cfg(feature = "dense")]
    mod dense {
        use super::*;
        use crate::dense::Dense;

        fn d(vals: &[f64]) -> Dense<f64> {
            let mut a = Dense::<f64>::zeros(vec![vals.len()]);
            a.fill_from(vals);
            a
        }

        #[test]
        fn abs_min_max_clamp() {
            let mut a = d(&[-3.0, -0.5, 0.5, 4.0]);
            a.abs();
            approx(&a.data, &[3.0, 0.5, 0.5, 4.0]);

            let mut b = d(&[-3.0, -0.5, 0.5, 4.0]);
            b.min(1.0);
            approx(&b.data, &[-3.0, -0.5, 0.5, 1.0]);

            let mut c = d(&[-3.0, -0.5, 0.5, 4.0]);
            c.max(0.0);
            approx(&c.data, &[0.0, 0.0, 0.5, 4.0]);

            let mut e = d(&[-3.0, -0.5, 0.5, 4.0]);
            e.clamp(-1.0, 1.0);
            approx(&e.data, &[-1.0, -0.5, 0.5, 1.0]);
        }

        #[test]
        fn trig() {
            let xs = [0.0, 0.3, -0.7, 1.2];
            let mut s = d(&xs);
            s.sin();
            approx(&s.data, &xs.map(f64::sin));
            let mut c = d(&xs);
            c.cos();
            approx(&c.data, &xs.map(f64::cos));
            let mut t = d(&xs);
            t.tan();
            approx(&t.data, &xs.map(f64::tan));
        }

        #[test]
        fn inverse_trig() {
            let xs = [-0.9, -0.1, 0.4, 0.8];
            let mut a = d(&xs);
            a.asin();
            approx(&a.data, &xs.map(f64::asin));
            let mut b = d(&xs);
            b.acos();
            approx(&b.data, &xs.map(f64::acos));
            let mut c = d(&xs);
            c.atan();
            approx(&c.data, &xs.map(f64::atan));
            let mut e = d(&xs);
            e.atan2(2.0);
            approx(&e.data, &xs.map(|x| x.atan2(2.0)));
        }

        #[test]
        fn roots_log_exp() {
            let xs = [0.25, 1.0, 8.0, 27.0];
            let mut a = d(&xs);
            a.sqrt();
            approx(&a.data, &xs.map(f64::sqrt));
            let mut b = d(&xs);
            b.cbrt();
            approx(&b.data, &xs.map(f64::cbrt));
            let mut c = d(&xs);
            c.ln();
            approx(&c.data, &xs.map(f64::ln));
            let mut e = d(&[-1.0, 0.0, 1.0, 2.0]);
            e.exp();
            approx(&e.data, &[-1.0f64, 0.0, 1.0, 2.0].map(f64::exp));
        }

        #[test]
        fn powers() {
            let xs = [1.0, 2.0, 3.0, 4.0];
            let mut a = d(&xs);
            a.powf(1.5);
            approx(&a.data, &xs.map(|x| x.powf(1.5)));
            let mut b = d(&xs);
            b.powi(3);
            approx(&b.data, &xs.map(|x| x.powi(3)));
        }

        #[test]
        fn chaining_returns_self() {
            let mut a = d(&[-4.0, 9.0, -16.0]);
            a.abs().sqrt();
            approx(&a.data, &[2.0, 3.0, 4.0]);
        }

        #[test]
        fn multidim_shape_preserved() {
            let mut a = Dense::<f64>::zeros(vec![2, 3]);
            a.fill_from(&[1.0, 4.0, 9.0, 16.0, 25.0, 36.0]);
            a.sqrt();
            assert_eq!(a.shape, vec![2, 3]);
            approx(&a.data, &[1.0, 2.0, 3.0, 4.0, 5.0, 6.0]);
        }

        #[test]
        fn f32_path() {
            let mut a = Dense::<f32>::zeros(vec![3]);
            a.fill_from(&[1.0, 4.0, 9.0]);
            a.sqrt();
            approx32(&a.data, &[1.0, 2.0, 3.0]);
        }
    }

    // ── Csr: only the stored non-zeros are touched ──

    #[cfg(feature = "csr")]
    mod csr {
        use super::*;
        use crate::csr::Csr;

        #[test]
        fn transforms_nonzeros_only() {
            // 2×3 with values [4, 9, 16] at (0,1),(0,2),(1,0).
            let mut m = Csr::<u32, f64>::from_parts(
                vec![2, 3],
                vec![0, 2, 3],
                vec![1, 2, 0],
                vec![4.0, 9.0, 16.0],
            );
            m.sqrt();
            approx(&m.values, &[2.0, 3.0, 4.0]);
            // Structure is untouched.
            assert_eq!(m.row_ptr, vec![0, 2, 3]);
            assert_eq!(m.col_idx, vec![1, 2, 0]);
            // An implicit zero stays zero even though √ maps it to 0 and the
            // transform never visited it.
            assert_eq!(m.get(1, 1), 0.0);
        }

        #[test]
        fn cos_does_not_densify() {
            // cos(0) = 1, but absent entries remain absent.
            let mut m = Csr::<u32, f64>::from_parts(
                vec![2, 2],
                vec![0, 1, 2],
                vec![0, 1],
                vec![0.0, std::f64::consts::PI],
            );
            let nnz_before = m.nnz();
            m.cos();
            assert_eq!(m.nnz(), nnz_before, "nnz must not change");
            approx(&m.values, &[1.0, -1.0]);
            // (0,1) and (1,0) were never stored and stay zero.
            assert_eq!(m.get(0, 1), 0.0);
            assert_eq!(m.get(1, 0), 0.0);
        }

        #[test]
        fn abs_and_powi() {
            let mut m =
                Csr::<u32, f64>::from_parts(vec![1, 3], vec![0, 3], vec![0, 1, 2], vec![-2.0, 3.0, -4.0]);
            m.abs().powi(2);
            approx(&m.values, &[4.0, 9.0, 16.0]);
        }
    }
}
