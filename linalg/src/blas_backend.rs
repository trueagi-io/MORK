//! Optional dense BLAS backend.
//!
//! This is the Torch-style escape hatch for large dense `f32` kernels: keep
//! MORK/linalg's sparse and shape-specialized paths, but delegate standard
//! dense GEMM work to a vendor BLAS instead of trying to beat it from scratch.

use std::fmt;

use crate::dense::Dense;

use blas_src as _;

/// Error returned when a BLAS-backed dense operation receives incompatible
/// tensors.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BlasError {
    RankMismatch {
        name: &'static str,
        expected: usize,
        got: usize,
    },
    ShapeMismatch {
        what: &'static str,
        expected: Vec<usize>,
        got: Vec<usize>,
    },
    DimensionTooLarge {
        name: &'static str,
        value: usize,
    },
}

impl fmt::Display for BlasError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BlasError::RankMismatch {
                name,
                expected,
                got,
            } => write!(f, "{name} rank mismatch: got {got}, expected {expected}"),
            BlasError::ShapeMismatch {
                what,
                expected,
                got,
            } => write!(
                f,
                "{what} shape mismatch: got {got:?}, expected {expected:?}"
            ),
            BlasError::DimensionTooLarge { name, value } => {
                write!(f, "{name}={value} exceeds BLAS i32 dimension limit")
            }
        }
    }
}

impl std::error::Error for BlasError {}

fn expect_rank(name: &'static str, shape: &[usize], expected: usize) -> Result<(), BlasError> {
    if shape.len() == expected {
        Ok(())
    } else {
        Err(BlasError::RankMismatch {
            name,
            expected,
            got: shape.len(),
        })
    }
}

fn expect_shape(what: &'static str, got: &[usize], expected: Vec<usize>) -> Result<(), BlasError> {
    if got == expected.as_slice() {
        Ok(())
    } else {
        Err(BlasError::ShapeMismatch {
            what,
            expected,
            got: got.to_vec(),
        })
    }
}

fn as_blas_dim(name: &'static str, value: usize) -> Result<i32, BlasError> {
    i32::try_from(value).map_err(|_| BlasError::DimensionTooLarge { name, value })
}

/// Row-major `out = a * b` for rank-2 dense `f32` matrices.
///
/// The crate stores tensors row-major, while the `blas` crate exposes the
/// Fortran/column-major BLAS API. A row-major buffer for `M x N` is the same
/// byte layout as a column-major buffer for `(M x N)^T`, so this computes
/// `out^T = b^T * a^T` using untransposed column-major operands.
pub fn matmul_f32(a: &Dense<f32>, b: &Dense<f32>, out: &mut Dense<f32>) -> Result<(), BlasError> {
    expect_rank("a", &a.shape, 2)?;
    expect_rank("b", &b.shape, 2)?;
    expect_rank("out", &out.shape, 2)?;

    let m = a.shape[0];
    let k = a.shape[1];
    let n = b.shape[1];
    expect_shape("b", &b.shape, vec![k, n])?;
    expect_shape("out", &out.shape, vec![m, n])?;

    let mi = as_blas_dim("m", m)?;
    let ni = as_blas_dim("n", n)?;
    let ki = as_blas_dim("k", k)?;

    unsafe {
        blas::sgemm(
            b'N',
            b'N',
            ni,
            mi,
            ki,
            1.0,
            &b.data,
            ni,
            &a.data,
            ki,
            0.0,
            &mut out.data,
            ni,
        );
    }
    Ok(())
}

/// Dense attention scores for `bhqd,bhkd->bhqk`.
///
/// `q` has shape `[batch, heads, query, dim]`; `k` has shape
/// `[batch, heads, key, dim]`; `out` has shape `[batch, heads, query, key]`.
/// Each `(batch, head)` slice is a GEMM: `Q(query x dim) * K(key x dim)^T`.
pub fn attention_scores_f32(
    q: &Dense<f32>,
    k: &Dense<f32>,
    out: &mut Dense<f32>,
) -> Result<(), BlasError> {
    expect_rank("q", &q.shape, 4)?;
    expect_rank("k", &k.shape, 4)?;
    expect_rank("out", &out.shape, 4)?;

    let batch = q.shape[0];
    let heads = q.shape[1];
    let query = q.shape[2];
    let dim = q.shape[3];
    expect_shape("k prefix/dim", &k.shape[..2], vec![batch, heads])?;
    if k.shape[3] != dim {
        return Err(BlasError::ShapeMismatch {
            what: "k dim",
            expected: vec![dim],
            got: vec![k.shape[3]],
        });
    }
    let key = k.shape[2];
    expect_shape("out", &out.shape, vec![batch, heads, query, key])?;

    let query_i = as_blas_dim("query", query)?;
    let key_i = as_blas_dim("key", key)?;
    let dim_i = as_blas_dim("dim", dim)?;

    let q_stride = query * dim;
    let k_stride = key * dim;
    let out_stride = query * key;
    for i in 0..batch * heads {
        let q_slice = &q.data[i * q_stride..(i + 1) * q_stride];
        let k_slice = &k.data[i * k_stride..(i + 1) * k_stride];
        let out_slice = &mut out.data[i * out_stride..(i + 1) * out_stride];
        unsafe {
            blas::sgemm(
                b'T', b'N', key_i, query_i, dim_i, 1.0, k_slice, dim_i, q_slice, dim_i, 0.0,
                out_slice, key_i,
            );
        }
    }

    Ok(())
}

/// Dense attention value application for `bhqk,bhkd->bhqd`.
///
/// `scores` has shape `[batch, heads, query, key]`; `v` has shape
/// `[batch, heads, key, dim]`; `out` has shape `[batch, heads, query, dim]`.
/// Each `(batch, head)` slice is a GEMM:
/// `scores(query x key) * V(key x dim)`.
pub fn attention_apply_f32(
    scores: &Dense<f32>,
    v: &Dense<f32>,
    out: &mut Dense<f32>,
) -> Result<(), BlasError> {
    expect_rank("scores", &scores.shape, 4)?;
    expect_rank("v", &v.shape, 4)?;
    expect_rank("out", &out.shape, 4)?;

    let batch = scores.shape[0];
    let heads = scores.shape[1];
    let query = scores.shape[2];
    let key = scores.shape[3];
    expect_shape("v prefix/key", &v.shape[..3], vec![batch, heads, key])?;
    let dim = v.shape[3];
    expect_shape("out", &out.shape, vec![batch, heads, query, dim])?;

    let query_i = as_blas_dim("query", query)?;
    let key_i = as_blas_dim("key", key)?;
    let dim_i = as_blas_dim("dim", dim)?;

    let scores_stride = query * key;
    let v_stride = key * dim;
    let out_stride = query * dim;
    for i in 0..batch * heads {
        let scores_slice = &scores.data[i * scores_stride..(i + 1) * scores_stride];
        let v_slice = &v.data[i * v_stride..(i + 1) * v_stride];
        let out_slice = &mut out.data[i * out_stride..(i + 1) * out_stride];
        unsafe {
            blas::sgemm(
                b'N',
                b'N',
                dim_i,
                query_i,
                key_i,
                1.0,
                v_slice,
                dim_i,
                scores_slice,
                key_i,
                0.0,
                out_slice,
                dim_i,
            );
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tensor::NDIndex;

    #[test]
    fn matmul_matches_expected_rectangular_result() {
        let mut a = Dense::<f32>::zeros(vec![2, 3]);
        a.fill_from(&[1.0, 2.0, 3.0, 4.0, 5.0, 6.0]);
        let mut b = Dense::<f32>::zeros(vec![3, 4]);
        b.fill_from(&[
            7.0, 8.0, 9.0, 10.0, 11.0, 12.0, 13.0, 14.0, 15.0, 16.0, 17.0, 18.0,
        ]);
        let mut out = Dense::<f32>::zeros(vec![2, 4]);

        matmul_f32(&a, &b, &mut out).unwrap();

        assert_eq!(
            out.data,
            vec![74.0, 80.0, 86.0, 92.0, 173.0, 188.0, 203.0, 218.0]
        );
    }

    #[test]
    fn attention_scores_match_manual_dot_products() {
        let mut q = Dense::<f32>::zeros(vec![1, 1, 2, 3]);
        q.fill_from(&[1.0, 2.0, 3.0, 4.0, 5.0, 6.0]);
        let mut k = Dense::<f32>::zeros(vec![1, 1, 2, 3]);
        k.fill_from(&[7.0, 8.0, 9.0, 10.0, 11.0, 12.0]);
        let mut out = Dense::<f32>::zeros(vec![1, 1, 2, 2]);

        attention_scores_f32(&q, &k, &mut out).unwrap();

        assert_eq!(out.get(&[0, 0, 0, 0]), 50.0);
        assert_eq!(out.get(&[0, 0, 0, 1]), 68.0);
        assert_eq!(out.get(&[0, 0, 1, 0]), 122.0);
        assert_eq!(out.get(&[0, 0, 1, 1]), 167.0);
    }

    #[test]
    fn attention_apply_matches_manual_weighted_sum() {
        let mut scores = Dense::<f32>::zeros(vec![1, 1, 2, 2]);
        scores.fill_from(&[0.25, 0.75, 0.5, 0.5]);
        let mut v = Dense::<f32>::zeros(vec![1, 1, 2, 3]);
        v.fill_from(&[10.0, 20.0, 30.0, 14.0, 28.0, 42.0]);
        let mut out = Dense::<f32>::zeros(vec![1, 1, 2, 3]);

        attention_apply_f32(&scores, &v, &mut out).unwrap();

        assert_eq!(out.get(&[0, 0, 0, 0]), 13.0);
        assert_eq!(out.get(&[0, 0, 0, 1]), 26.0);
        assert_eq!(out.get(&[0, 0, 0, 2]), 39.0);
        assert_eq!(out.get(&[0, 0, 1, 0]), 12.0);
        assert_eq!(out.get(&[0, 0, 1, 1]), 24.0);
        assert_eq!(out.get(&[0, 0, 1, 2]), 36.0);
    }
}
