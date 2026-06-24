//! Density-crossover benchmarks: sparse representations vs dense BLAS.
//!
//! Ported in spirit from the sparse-linear-algebra-tests crossover studies
//! (`tipover_attention_bob` / `bench_chunked_vs_blas` in its `main.rs`,
//! plotted as `crossover_threshold.png`): sweep density on a log grid
//! (4 steps per decade, 0.01% … 100%) and find where the sparse
//! implementation stops beating dense BLAS, which does the same flops
//! regardless of how many entries are zero.
//!
//!   1. SpGEMM — `Csr<u32, f32>::matmul` / `matmul_par` vs `sgemm`
//!      (n×n × n×n, both operands at density d).
//!   2. Attention — `Blocked8` / `Blocked16` `bhqd,bhkd→bhqk` vs OpenBLAS
//!      `cblas_sgemm_batch_strided` on GPT-shaped tensors.
//!
//! OpenBLAS is pinned to 1 thread for a fair single-core comparison;
//! `csr_par_us` is the rayon-parallel SpGEMM, reported for reference.
//! Each sweep stops once the sparse side is 4× slower than BLAS.
//!
//! Run with:
//!   cargo bench -p linalg --bench crossover --features blas > crossover.log
//! Plot with:
//!   uv run linalg/plot_crossover.py crossover.log
//!
//! Environment:
//!   CROSSOVER_LARGE=1  add n ∈ {2048, 4096} and the GPT-2 Large/XL configs

use std::time::Instant;

use linalg::blocked::{Blocked8, Blocked16, attention};
use linalg::csr::Csr;
use linalg::tensor::NDIndex;

extern crate blas_src;

unsafe extern "C" {
    /// Pin the OpenBLAS pool at runtime — the OPENBLAS_NUM_THREADS env var
    /// is only read in the library's load-time constructor, so setting it
    /// from main() is too late.
    fn openblas_set_num_threads(num: i32);
}

// (batch_size, sequence_length, n_heads, embedding_dim) — original GPT_CONFIGS
const GPT_CONFIGS: [(usize, usize, usize, usize); 5] = [
    (32, 512, 12, 384),  // shakespeare-char
    (8, 1024, 12, 768),  // GPT-2 117M (Small)
    (8, 1024, 16, 1024), // GPT-2 345M (Medium)
    (8, 1024, 20, 1280), // GPT-2 762M (Large)
    (8, 1024, 25, 1600), // GPT-2 1542M (XL)
];

// ─── helpers ────────────────────────────────────────────────────────────

fn xorshift(seed: u64) -> impl FnMut() -> u64 {
    let mut x = seed.max(1);
    move || {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        x
    }
}

/// Adaptive timer: the first call doubles as warmup/estimate; slow cases
/// (≥250 ms) report that single run, fast cases average enough iterations
/// to fill ~250 ms (capped at 50).
fn time_us<F: FnMut()>(mut f: F) -> f64 {
    let t0 = Instant::now();
    f();
    let once = t0.elapsed().as_secs_f64();
    if once >= 0.25 {
        return once * 1e6;
    }
    let iters = ((0.25 / once.max(1e-9)) as usize).clamp(1, 50);
    let t0 = Instant::now();
    for _ in 0..iters {
        f();
    }
    t0.elapsed().as_secs_f64() * 1e6 / iters as f64
}

fn fmt_us(t: f64) -> String {
    if t.is_nan() {
        String::new()
    } else {
        format!("{t:.0}")
    }
}

fn fmt_ratio(t: f64) -> String {
    if t.is_nan() {
        String::new()
    } else {
        format!("{t:.3}")
    }
}

/// Log-log interpolate the density where the sparse/BLAS time ratio
/// crosses 1.0. `points` are (density, ratio) in sweep order.
fn crossover(points: &[(f64, f64)]) -> Option<f64> {
    for w in points.windows(2) {
        let (d0, r0) = w[0];
        let (d1, r1) = w[1];
        if r0 <= 1.0 && r1 > 1.0 && r0 > 0.0 {
            let t = (-r0.ln()) / (r1.ln() - r0.ln());
            return Some((d0.ln() + t * (d1.ln() - d0.ln())).exp());
        }
    }
    None
}

fn report_crossover(what: &str, points: &[(f64, f64)]) {
    match crossover(points) {
        Some(d) => println!("  → {what} crossover ≈ {:.3}% density", d * 100.0),
        None => println!("  → {what} crossover not bracketed by sweep"),
    }
}

// ─── 1. SpGEMM vs sgemm ─────────────────────────────────────────────────

/// Row-major C = A·B via column-major (A·B)ᵀ = Bᵀ·Aᵀ.
fn blas_matmul(a: &[f32], b: &[f32], c: &mut [f32], n: usize) {
    let ni = n as i32;
    unsafe {
        blas::sgemm(b'N', b'N', ni, ni, ni, 1.0, b, ni, a, ni, 0.0, c, ni);
    }
}

/// Random n×n matrix at `density`, as matching CSR and dense buffers.
fn gen_sparse_dense(n: usize, density: f64, seed: u64) -> (Csr<u32, f32>, Vec<f32>) {
    let mut rng = xorshift(seed);
    let mut dense = vec![0f32; n * n];
    let mut trips: Vec<(u32, u32, f32)> = Vec::new();
    for r in 0..n {
        for c in 0..n {
            if (rng() as f64 / u64::MAX as f64) < density {
                let v = (0.1 + 0.9 * (rng() as f64 / u64::MAX as f64)) as f32;
                dense[r * n + c] = v;
                trips.push((r as u32, c as u32, v));
            }
        }
    }
    (Csr::from_coo(n as u32, &mut trips), dense)
}

fn validate_matmul(r: &Csr<u32, f32>, c: &[f32], n: usize) {
    let mut max_rel = 0f32;
    for row in 0..n as u32 {
        for (col, v) in r.row(row) {
            let d = c[row as usize * n + col as usize];
            let denom = v.abs().max(d.abs()).max(1e-6);
            max_rel = max_rel.max((v - d).abs() / denom);
        }
    }
    assert!(
        max_rel < 1e-3,
        "SpGEMM vs sgemm mismatch: max_rel = {max_rel}"
    );
}

#[cfg(feature = "rayon")]
fn csr_matmul_par_us(a: &Csr<u32, f32>, b: &Csr<u32, f32>) -> f64 {
    time_us(|| {
        std::hint::black_box(a.matmul_par(b));
    })
}

#[cfg(not(feature = "rayon"))]
fn csr_matmul_par_us(_a: &Csr<u32, f32>, _b: &Csr<u32, f32>) -> f64 {
    f64::NAN
}

fn section_matmul(large: bool) {
    println!("\n=== 1. SpGEMM (Csr<u32,f32>) vs BLAS sgemm — density sweep ===");
    println!("n,density,nnz,csr_us,csr_par_us,blas_us,seq_ratio,par_ratio");

    let ns: &[usize] = if large {
        &[256, 512, 1024, 2048, 4096]
    } else {
        &[256, 512, 1024]
    };

    for &n in ns {
        let mut seq_pts: Vec<(f64, f64)> = Vec::new();
        let mut par_pts: Vec<(f64, f64)> = Vec::new();
        let mut validated = false;
        let mut seq_done = false;

        for ii in 0..=16u64 {
            let density = 1e-4 * 10f64.powf(ii as f64 / 4.0);
            let (a, ad) = gen_sparse_dense(n, density, 42 + ii);
            let (b, bd) = gen_sparse_dense(n, density, 999 + ii);

            let mut c = vec![0f32; n * n];
            let blas_us = time_us(|| {
                blas_matmul(&ad, &bd, &mut c, n);
                std::hint::black_box(&c);
            });

            if !validated && a.nnz() > 50 {
                validate_matmul(&a.matmul(&b), &c, n);
                validated = true;
            }

            let seq_us = if seq_done {
                f64::NAN
            } else {
                time_us(|| {
                    std::hint::black_box(a.matmul(&b));
                })
            };
            let par_us = csr_matmul_par_us(&a, &b);

            let seq_ratio = seq_us / blas_us;
            let par_ratio = par_us / blas_us;
            if !seq_ratio.is_nan() {
                seq_pts.push((density, seq_ratio));
            }
            if !par_ratio.is_nan() {
                par_pts.push((density, par_ratio));
            }
            println!(
                "{n},{density:.4},{},{},{},{blas_us:.0},{},{}",
                a.nnz(),
                fmt_us(seq_us),
                fmt_us(par_us),
                fmt_ratio(seq_ratio),
                fmt_ratio(par_ratio),
            );

            if seq_ratio > 4.0 {
                seq_done = true;
            }
            let par_done = par_ratio.is_nan() || par_ratio > 4.0;
            if seq_done && par_done {
                println!("  (stopping sweep at n={n}: sparse > 4× BLAS)");
                break;
            }
        }

        report_crossover(&format!("n={n} csr"), &seq_pts);
        report_crossover(&format!("n={n} csr_par"), &par_pts);
    }
}

// ─── 2. Blocked attention vs BLAS batched attention ─────────────────────

/// Dense `bhqd,bhkd→bhqk`: one (heads×dim)·(heads×dim)ᵀ GEMM per
/// (batch, seq) pair. Row-major `out = Q·Kᵀ` is computed as column-major
/// `outᵀ = K·Qᵀ`: the row-major buffers read as column-major are exactly
/// Qᵀ and Kᵀ, so op(A) = (Kᵀ)ᵀ with transA='T' and op(B) = Qᵀ untransposed.
fn blas_attention(q: &[f32], k: &[f32], out: &mut [f32], batches: usize, heads: usize, dim: usize) {
    let hd = heads * dim;
    let hh = heads * heads;
    for i in 0..batches {
        let q_slice = &q[i * hd..(i + 1) * hd];
        let k_slice = &k[i * hd..(i + 1) * hd];
        let out_slice = &mut out[i * hh..(i + 1) * hh];
        unsafe {
            blas::sgemm(
                b'T',
                b'N',
                heads as i32,
                heads as i32,
                dim as i32,
                1.0,
                k_slice,
                dim as i32,
                q_slice,
                dim as i32,
                0.0,
                out_slice,
                heads as i32,
            );
        }
    }
}

/// One [batch, seq, heads, dim] tensor at `density`, with identical
/// contents in Blocked8, Blocked16, and a dense row-major buffer.
fn fill_attention(
    batch: usize,
    seq: usize,
    heads: usize,
    dim: usize,
    density: f64,
    seed: u64,
) -> (Blocked8, Blocked16, Vec<f32>) {
    let shape = vec![batch, seq, heads, dim];
    let mut b8 = Blocked8::with_shape(shape.clone());
    let mut b16 = Blocked16::with_shape(shape);
    let mut dense = vec![0f32; batch * seq * heads * dim];
    let mut rng = xorshift(seed);
    let mut i = 0usize;
    for b in 0..batch {
        for s in 0..seq {
            for h in 0..heads {
                for d in 0..dim {
                    if (rng() as f64 / u64::MAX as f64) < density {
                        let v = (0.1 + 0.9 * (rng() as f64 / u64::MAX as f64)) as f32;
                        dense[i] = v;
                        b8.set(&[b, s, h, d], v);
                        b16.set(&[b, s, h, d], v);
                    }
                    i += 1;
                }
            }
        }
    }
    (b8, b16, dense)
}

/// Full-density cross-check of both blocked kernels against BLAS.
fn validate_attention(batch: usize, seq: usize, heads: usize, dim: usize) {
    let (q8, q16, qd) = fill_attention(batch, seq, heads, dim, 1.0, 1);
    let (k8, k16, kd) = fill_attention(batch, seq, heads, dim, 1.0, 2);

    let mut out_d = vec![0f32; batch * seq * heads * heads];
    blas_attention(&qd, &kd, &mut out_d, batch * seq, heads, dim);

    let mut out8 = Blocked8::with_shape(vec![batch, seq, heads, heads]);
    attention(&q8, &k8, &mut out8);
    let mut out16 = Blocked16::with_shape(vec![batch, seq, heads, heads]);
    attention(&q16, &k16, &mut out16);

    let mut max_rel = 0f32;
    let mut i = 0usize;
    for b in 0..batch {
        for s in 0..seq {
            for hq in 0..heads {
                for hk in 0..heads {
                    let dv = out_d[i];
                    let denom = dv.abs().max(1.0);
                    let ix = [b, s, hq, hk];
                    max_rel = max_rel.max((dv - out8.get(&ix)).abs() / denom);
                    max_rel = max_rel.max((dv - out16.get(&ix)).abs() / denom);
                    i += 1;
                }
            }
        }
    }
    assert!(
        max_rel < 1e-3,
        "blocked vs BLAS attention mismatch: max_rel = {max_rel}"
    );
}

fn section_attention(large: bool) {
    println!("\n=== 2. Blocked attention vs BLAS batched attention — density sweep ===");
    println!("config,density,q_nz,blas_us,b8_us,b16_us,b8_ratio,b16_ratio");

    let nconf = if large { GPT_CONFIGS.len() } else { 3 };

    for &(batch, seq, heads, edim) in &GPT_CONFIGS[..nconf] {
        let dim = edim / heads;
        let tag = format!("b{batch}_s{seq}_h{heads}_d{dim}");

        validate_attention(batch, seq, heads, dim);
        println!("  [{tag}] full-density correctness vs BLAS ok");

        let mut p8: Vec<(f64, f64)> = Vec::new();
        let mut p16: Vec<(f64, f64)> = Vec::new();

        for ii in 0..=16u64 {
            let density = 1e-4 * 10f64.powf(ii as f64 / 4.0);
            let (q8, q16, qd) = fill_attention(batch, seq, heads, dim, density, 11 + ii);
            let (k8, k16, kd) = fill_attention(batch, seq, heads, dim, density, 77 + ii);
            let q_nz = qd.iter().filter(|&&v| v != 0.0).count();

            let mut out_d = vec![0f32; batch * seq * heads * heads];
            let blas_us = time_us(|| {
                blas_attention(&qd, &kd, &mut out_d, batch * seq, heads, dim);
                std::hint::black_box(&out_d);
            });
            let b8_us = time_us(|| {
                let mut out = Blocked8::with_shape(vec![batch, seq, heads, heads]);
                attention(&q8, &k8, &mut out);
                std::hint::black_box(&out);
            });
            let b16_us = time_us(|| {
                let mut out = Blocked16::with_shape(vec![batch, seq, heads, heads]);
                attention(&q16, &k16, &mut out);
                std::hint::black_box(&out);
            });

            let r8 = b8_us / blas_us;
            let r16 = b16_us / blas_us;
            p8.push((density, r8));
            p16.push((density, r16));
            println!(
                "{tag},{density:.4},{q_nz},{blas_us:.0},{b8_us:.0},{b16_us:.0},{r8:.3},{r16:.3}"
            );

            if r8 > 4.0 && r16 > 4.0 {
                println!("  (stopping sweep for {tag}: both > 4× BLAS)");
                break;
            }
        }

        report_crossover(&format!("{tag} Blocked8"), &p8);
        report_crossover(&format!("{tag} Blocked16"), &p16);
    }
}

// ─── main ───────────────────────────────────────────────────────────────

fn main() {
    // Single-threaded BLAS for a fair single-core comparison.
    unsafe {
        openblas_set_num_threads(1);
    }
    let large = std::env::var("CROSSOVER_LARGE").is_ok_and(|v| !v.is_empty() && v != "0");

    println!("=== linalg crossover bench: sparse vs BLAS (OpenBLAS, 1 thread) ===");
    println!("(times in µs; ratios are sparse/BLAS — crossover is where ratio hits 1.0)");
    if large {
        println!("(CROSSOVER_LARGE set: including big configurations)");
    }

    section_matmul(large);
    section_attention(large);

    println!("\n=== done ===");
}
