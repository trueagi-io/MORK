//! Block-sparse f32 tensor with AVX2+FMA SIMD kernels for batched
//! attention (`bhqd,bhkd->bhqk`).
//!
//! The last two dimensions of [`Blocked<N>`] are tiled into `N × N`
//! blocks; each block is either present (`Some([f32; N*N])`) or absent
//! (treated as all-zero). [`attention`] does block-by-block dispatch:
//! when both Q and K blocks are present, run the inline SIMD matmul;
//! otherwise skip.
//!
//! Type aliases [`Blocked8`] and [`Blocked16`] are the practical ones —
//! their SIMD paths are enabled when the target supports AVX2+FMA, and
//! fall back to a scalar `C += A·Bᵀ` otherwise.
//!
//! # Example
//!
//! ```no_run
//! use linalg::blocked::{Blocked8, attention};
//! let mut q = Blocked8::with_shape(vec![1, 1, 8, 8]);
//! let mut k = Blocked8::with_shape(vec![1, 1, 8, 8]);
//! let mut out = Blocked8::with_shape(vec![1, 1, 8, 8]);
//! // ... fill q and k with set(&[b, h, i, d], v) ...
//! attention(&q, &k, &mut out);
//! ```

use crate::tensor::NDIndex;

// ─────────────────────────────────────────────────────────────────────────
// SIMD kernels
// ─────────────────────────────────────────────────────────────────────────

#[cfg(all(target_arch = "x86_64", target_feature = "avx2", target_feature = "fma"))]
use std::arch::x86_64::*;

/// 8×8 `C += A·Bᵀ` via AVX2+FMA. One ymm per result row.
#[cfg(all(target_arch = "x86_64", target_feature = "avx2", target_feature = "fma"))]
#[inline(always)]
unsafe fn avx2_matmul_acc_8x8(a: *const f32, b: *const f32, c: *mut f32) {
    unsafe {
        let mut bt = [0.0f32; 64];
        for row in 0..8 {
            for col in 0..8 {
                *bt.get_unchecked_mut(col * 8 + row) = *b.add(row * 8 + col);
            }
        }

        let mut res = [_mm256_setzero_ps(); 8];
        for i in 0..8 {
            res[i] = _mm256_loadu_ps(c.add(i * 8));
        }

        for k in 0..8 {
            let bt_row = _mm256_loadu_ps(bt.as_ptr().add(k * 8));
            for i in 0..8 {
                let a_ik = _mm256_set1_ps(*a.add(i * 8 + k));
                res[i] = _mm256_fmadd_ps(a_ik, bt_row, res[i]);
            }
        }

        for i in 0..8 {
            _mm256_storeu_ps(c.add(i * 8), res[i]);
        }
    }
}

/// 16×16 `C += A·Bᵀ` via AVX2+FMA. Two ymm halves per row, 4-row tiles.
#[cfg(all(target_arch = "x86_64", target_feature = "avx2", target_feature = "fma"))]
#[inline(always)]
unsafe fn avx2_matmul_acc_16x16(a: *const f32, b: *const f32, c: *mut f32) {
    unsafe {
        let mut bt = [0.0f32; 256];
        for row in 0..16 {
            for col in 0..16 {
                *bt.get_unchecked_mut(col * 16 + row) = *b.add(row * 16 + col);
            }
        }

        for tile in 0..4 {
            let base_i = tile * 4;
            let mut res_lo = [_mm256_setzero_ps(); 4];
            let mut res_hi = [_mm256_setzero_ps(); 4];
            for r in 0..4 {
                res_lo[r] = _mm256_loadu_ps(c.add((base_i + r) * 16));
                res_hi[r] = _mm256_loadu_ps(c.add((base_i + r) * 16 + 8));
            }
            for k in 0..16 {
                let bt_lo = _mm256_loadu_ps(bt.as_ptr().add(k * 16));
                let bt_hi = _mm256_loadu_ps(bt.as_ptr().add(k * 16 + 8));
                for r in 0..4 {
                    let a_ik = _mm256_set1_ps(*a.add((base_i + r) * 16 + k));
                    res_lo[r] = _mm256_fmadd_ps(a_ik, bt_lo, res_lo[r]);
                    res_hi[r] = _mm256_fmadd_ps(a_ik, bt_hi, res_hi[r]);
                }
            }
            for r in 0..4 {
                _mm256_storeu_ps(c.add((base_i + r) * 16), res_lo[r]);
                _mm256_storeu_ps(c.add((base_i + r) * 16 + 8), res_hi[r]);
            }
        }
    }
}

/// `N×N` multiply-accumulate `C += A·Bᵀ`. Dispatches to AVX2 when available.
#[inline(always)]
fn block_matmul_acc<const N: usize, const SQ: usize>(
    a: &[f32; SQ],
    b: &[f32; SQ],
    c: &mut [f32; SQ],
) {
    #[cfg(all(target_arch = "x86_64", target_feature = "avx2", target_feature = "fma"))]
    {
        match N {
            8 => {
                unsafe { avx2_matmul_acc_8x8(a.as_ptr(), b.as_ptr(), c.as_mut_ptr()) };
                return;
            }
            16 => {
                unsafe { avx2_matmul_acc_16x16(a.as_ptr(), b.as_ptr(), c.as_mut_ptr()) };
                return;
            }
            _ => {}
        }
    }
    block_matmul_acc_scalar::<N, SQ>(a, b, c);
}

/// Scalar fallback. Transposes B into a stack-local buffer so the inner
/// loop streams contiguously over columns.
#[inline(always)]
fn block_matmul_acc_scalar<const N: usize, const SQ: usize>(
    a: &[f32; SQ],
    b: &[f32; SQ],
    c: &mut [f32; SQ],
) {
    let mut bt = [0.0f32; SQ];
    for row in 0..N {
        for col in 0..N {
            bt[col * N + row] = b[row * N + col];
        }
    }
    for i in 0..N {
        for k in 0..N {
            let a_ik = a[i * N + k];
            for j in 0..N {
                c[i * N + j] = a_ik.mul_add(bt[k * N + j], c[i * N + j]);
            }
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────
// Block-sparse tensor
// ─────────────────────────────────────────────────────────────────────────

#[inline]
fn ceil_div(a: usize, b: usize) -> usize {
    (a + b - 1) / b
}

/// Block-sparse N-D tensor. The trailing two dimensions are tiled into
/// `N × N` blocks; each block is either present or absent.
pub struct Blocked<const N: usize, const SQ: usize> {
    shape: Vec<usize>,
    n_block_rows: usize,
    n_block_cols: usize,
    outer_size: usize,
    blocks: Vec<Option<Box<[f32; SQ]>>>,
}

pub type Blocked8 = Blocked<8, 64>;
pub type Blocked16 = Blocked<16, 256>;

impl<const N: usize, const SQ: usize> Blocked<N, SQ> {
    /// Construct an empty tensor of the given shape — all blocks absent.
    pub fn with_shape(shape: Vec<usize>) -> Self {
        assert!(shape.len() >= 2, "need at least 2 dimensions");
        assert!(SQ == N * N, "SQ must equal N * N");
        let nd = shape.len();
        let n_block_rows = ceil_div(shape[nd - 2], N);
        let n_block_cols = ceil_div(shape[nd - 1], N);
        let outer_size: usize = if nd > 2 { shape[..nd - 2].iter().product() } else { 1 };
        let total_blocks = outer_size * n_block_rows * n_block_cols;
        let mut blocks = Vec::with_capacity(total_blocks);
        blocks.resize_with(total_blocks, || None);
        Self { shape, n_block_rows, n_block_cols, outer_size, blocks }
    }

    /// Count of non-zero scalar entries inside present blocks.
    pub fn nnz(&self) -> usize {
        self.blocks
            .iter()
            .filter_map(|b| b.as_ref())
            .map(|b| b.iter().filter(|&&v| v != 0.0).count())
            .sum()
    }

    fn outer_linear_index(&self, ix: &[usize]) -> usize {
        let nd = self.shape.len();
        if nd <= 2 {
            return 0;
        }
        let mut idx = 0;
        let mut stride = 1;
        for i in (0..nd - 2).rev() {
            idx += ix[i] * stride;
            stride *= self.shape[i];
        }
        idx
    }

    fn block_coords(&self, ix: &[usize]) -> (usize, usize) {
        let nd = self.shape.len();
        let outer = self.outer_linear_index(ix);
        let block_row = ix[nd - 2] / N;
        let block_col = ix[nd - 1] / N;
        let block_idx = outer * (self.n_block_rows * self.n_block_cols)
            + block_row * self.n_block_cols
            + block_col;
        let local_row = ix[nd - 2] % N;
        let local_col = ix[nd - 1] % N;
        (block_idx, local_row * N + local_col)
    }
}

impl<const N: usize, const SQ: usize> NDIndex<f32> for Blocked<N, SQ> {
    fn ndim(&self) -> usize {
        self.shape.len()
    }
    fn dim(&self, axis: usize) -> usize {
        self.shape[axis]
    }
    fn get(&self, ix: &[usize]) -> f32 {
        if self.blocks.is_empty() {
            return 0.0;
        }
        let (block_idx, local_idx) = self.block_coords(ix);
        self.blocks[block_idx].as_ref().map_or(0.0, |b| b[local_idx])
    }
    fn set(&mut self, ix: &[usize], v: f32) {
        let (block_idx, local_idx) = self.block_coords(ix);
        let block = self.blocks[block_idx].get_or_insert_with(|| Box::new([0.0; SQ]));
        block[local_idx] = v;
    }
    fn get_opt(&self, ix: &[usize]) -> Option<f32> {
        if self.blocks.is_empty() {
            return None;
        }
        let (block_idx, local_idx) = self.block_coords(ix);
        self.blocks[block_idx].as_ref().and_then(|b| {
            let v = b[local_idx];
            if v != 0.0 { Some(v) } else { None }
        })
    }
}

// ─────────────────────────────────────────────────────────────────────────
// Attention
// ─────────────────────────────────────────────────────────────────────────

/// Batched attention scores: `bhqd,bhkd → bhqk`.
///
/// `q` and `k` must share the trailing `d` block count and the outer
/// `b × h` shape. Each output block accumulates `Q × Kᵀ` over the
/// inner-dimension blocks via the inline SIMD kernel. Output blocks are
/// allocated lazily — pairs where at least one of Q's or K's blocks is
/// absent contribute nothing.
///
/// Returns the count of scalar fused-multiply-adds executed (mostly
/// useful for benches).
#[allow(non_snake_case)]
pub fn attention<const N: usize, const SQ: usize>(
    q: &Blocked<N, SQ>,
    k: &Blocked<N, SQ>,
    out: &mut Blocked<N, SQ>,
) -> usize {
    let q_brows = q.n_block_rows;
    let d_blocks = q.n_block_cols;
    let k_brows = k.n_block_rows;

    assert_eq!(d_blocks, k.n_block_cols, "inner d block count mismatch");
    assert_eq!(out.n_block_rows, q_brows, "output q-block count mismatch");
    assert_eq!(out.n_block_cols, k_brows, "output k-block count mismatch");
    assert_eq!(q.outer_size, k.outer_size, "outer dim mismatch");
    assert_eq!(q.outer_size, out.outer_size, "outer dim mismatch");

    let q_per_outer = q_brows * d_blocks;
    let k_per_outer = k_brows * k.n_block_cols;
    let o_per_outer = out.n_block_rows * out.n_block_cols;

    let mut count = 0usize;

    for outer in 0..q.outer_size {
        let q_base = outer * q_per_outer;
        let k_base = outer * k_per_outer;
        let o_base = outer * o_per_outer;

        for qi in 0..q_brows {
            for ki in 0..k_brows {
                let mut acc = [0.0f32; SQ];
                let mut hits = 0usize;
                for di in 0..d_blocks {
                    let q_idx = q_base + qi * d_blocks + di;
                    let k_idx = k_base + ki * k.n_block_cols + di;
                    if let (Some(q_blk), Some(k_blk)) = (&q.blocks[q_idx], &k.blocks[k_idx]) {
                        block_matmul_acc::<N, SQ>(q_blk, k_blk, &mut acc);
                        hits += 1;
                    }
                }
                if hits > 0 {
                    let o_idx = o_base + qi * out.n_block_cols + ki;
                    out.blocks[o_idx] = Some(Box::new(acc));
                    count += hits * N * N * N;
                }
            }
        }
    }
    count
}

// ─────────────────────────────────────────────────────────────────────────
// Tests
// ─────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    fn naive_attention<const N: usize, const SQ: usize>(
        q: &Blocked<N, SQ>,
        k: &Blocked<N, SQ>,
        out: &mut Blocked<N, SQ>,
    ) {
        let shape = q.shape.clone();
        let nd = shape.len();
        let (b, h, q_len, d) = (shape[0], shape[1], shape[2], shape[3]);
        let k_len = k.shape[2];
        assert_eq!(nd, 4);
        for bi in 0..b {
            for hi in 0..h {
                for qi in 0..q_len {
                    for ki in 0..k_len {
                        let mut sum = 0.0f32;
                        for di in 0..d {
                            sum += q.get(&[bi, hi, qi, di]) * k.get(&[bi, hi, ki, di]);
                        }
                        if sum != 0.0 {
                            out.set(&[bi, hi, qi, ki], sum);
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn round_trip_get_set() {
        let mut t = Blocked8::with_shape(vec![1, 1, 16, 16]);
        t.set(&[0, 0, 3, 5], 1.5);
        t.set(&[0, 0, 12, 9], -2.0);
        assert_eq!(t.get(&[0, 0, 3, 5]), 1.5);
        assert_eq!(t.get(&[0, 0, 12, 9]), -2.0);
        assert_eq!(t.get(&[0, 0, 0, 0]), 0.0);
    }

    #[test]
    fn attention_correctness_full_block() {
        let (b, h, ql, kl, d) = (1, 1, 8, 8, 8);
        let mut q = Blocked8::with_shape(vec![b, h, ql, d]);
        let mut k = Blocked8::with_shape(vec![b, h, kl, d]);
        let mut c = 0.0f32;
        for qi in 0..ql {
            for di in 0..d {
                c += 0.01;
                q.set(&[0, 0, qi, di], c);
            }
        }
        let mut c = 0.0f32;
        for ki in 0..kl {
            for di in 0..d {
                c += 0.01;
                k.set(&[0, 0, ki, di], -c);
            }
        }

        let mut out_blocked = Blocked8::with_shape(vec![b, h, ql, kl]);
        let mut out_naive = Blocked8::with_shape(vec![b, h, ql, kl]);
        attention(&q, &k, &mut out_blocked);
        naive_attention(&q, &k, &mut out_naive);

        for qi in 0..ql {
            for ki in 0..kl {
                let a = out_blocked.get(&[0, 0, qi, ki]);
                let b = out_naive.get(&[0, 0, qi, ki]);
                let denom = a.abs().max(b.abs()).max(1e-6);
                assert!((a - b).abs() / denom < 1e-3, "mismatch at ({qi},{ki}): {a} vs {b}");
            }
        }
    }

    #[test]
    fn attention_skips_absent_blocks() {
        // 16x16 q,k,d — 2x2 grid of blocks. Only fill the (0,0) block of Q
        // and the (0,0) block of K. Outputs in block-(0,0) of out should be
        // non-zero; everything else should be zero (and ideally not allocated).
        let mut q = Blocked8::with_shape(vec![1, 1, 16, 16]);
        let mut k = Blocked8::with_shape(vec![1, 1, 16, 16]);
        for qi in 0..8 {
            for di in 0..8 {
                q.set(&[0, 0, qi, di], 1.0);
                k.set(&[0, 0, qi, di], 1.0);
            }
        }
        let mut out = Blocked8::with_shape(vec![1, 1, 16, 16]);
        attention(&q, &k, &mut out);

        // Block (0,0): every output is sum of 8 products of 1.0 = 8.0
        assert_eq!(out.get(&[0, 0, 0, 0]), 8.0);
        assert_eq!(out.get(&[0, 0, 7, 7]), 8.0);
        // Block (1,1) outputs should be zero
        assert_eq!(out.get(&[0, 0, 12, 12]), 0.0);
    }
}
