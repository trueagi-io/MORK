//! Performance benchmarks for the linalg crate.
//!
//! Custom Instant-based timing — no criterion dependency, output styled
//! after the original einsum-dyn bench so numbers can be compared visually
//! against the upstream repo's bench_* test functions.
//!
//! Run with `cargo bench` (or `cargo run --release --bench perf`).
//!
//! Sections:
//!   1. Dense matmul via einsum     — homogenous vs dyn
//!   2. CSR × CSR matmul            — native vs einsum-homogenous vs einsum-dyn
//!   3. CSR × CSR matmul_par scaling
//!   4. CSR × Dense via einsum_dyn  — mixed-type composition
//!   5. Blocked attention           — Blocked8, Blocked16 at full and 10% block density

use std::time::Instant;

#[cfg(feature = "jit")]
use linalg::jit::{EinsumF32Plan, JitInput};
use linalg::{
    any::Tensor,
    blocked::{Blocked, Blocked8, Blocked16, attention},
    csr::Csr,
    dense::Dense,
    einsum::{einsum, einsum_homogenous},
    tensor::NDIndex,
};

// ─── helpers ────────────────────────────────────────────────────────────

fn bench<F: FnMut()>(name: &str, iters: u32, mut f: F) -> f64 {
    for _ in 0..3 {
        f();
    } // warmup
    let start = Instant::now();
    for _ in 0..iters {
        f();
    }
    let elapsed = start.elapsed();
    let per_iter_us = elapsed.as_nanos() as f64 / iters as f64 / 1000.0;
    println!("  {name:42} {per_iter_us:12.2} µs/iter  ({iters} iters)");
    per_iter_us
}

fn xorshift(seed: u64) -> impl FnMut() -> u64 {
    let mut x = seed.max(1);
    move || {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        x
    }
}

fn fill_rand_f32(t: &mut Dense<f32>, seed: u64) {
    let mut rng = xorshift(seed);
    for v in t.data.iter_mut() {
        *v = (rng() as f64 / u64::MAX as f64) as f32;
    }
}

/// 3D Moore-neighbourhood torus, side `s`, then random thin to roughly
/// `target_epn` edges per node. Mirrors the original bench_matmul setup.
fn lattice_csr(s: usize, target_epn: f64, seed: u64) -> Csr<u32, u32> {
    let nu = s * s * s;
    let mut triplets: Vec<(u32, u32, u32)> = Vec::new();
    for node in 0..nu {
        let (x, y, z) = (node / (s * s), (node / s) % s, node % s);
        for dx in -1i32..=1 {
            for dy in -1i32..=1 {
                for dz in -1i32..=1 {
                    if dx == 0 && dy == 0 && dz == 0 {
                        continue;
                    }
                    let nx = (x as i32 + dx).rem_euclid(s as i32) as usize;
                    let ny = (y as i32 + dy).rem_euclid(s as i32) as usize;
                    let nz = (z as i32 + dz).rem_euclid(s as i32) as usize;
                    let neighbour = nx * s * s + ny * s + nz;
                    triplets.push((node as u32, neighbour as u32, 1));
                }
            }
        }
    }

    // Thin to target edges-per-node (each node has 26 full Moore neighbours).
    let full_epn = 26.0;
    let keep_p = (target_epn / full_epn).clamp(0.0, 1.0);
    let mut rng = xorshift(seed);
    triplets.retain(|_| {
        let p = rng() as f64 / u64::MAX as f64;
        p < keep_p
    });

    Csr::from_coo(nu as u32, &mut triplets)
}

/// Empty dense feature matrix.
fn dense_filled(shape: Vec<usize>, seed: u64) -> Dense<f32> {
    let mut t = Dense::<f32>::zeros(shape);
    fill_rand_f32(&mut t, seed);
    t
}

fn fill_blocked<const N: usize, const SQ: usize>(
    t: &mut Blocked<N, SQ>,
    shape: &[usize],
    density: f32,
    seed: u64,
) {
    // Pre-write into every position with probability `density`. Coarse
    // but consistent across runs.
    let total: usize = shape.iter().product();
    let mut rng = xorshift(seed);
    let mut ix = vec![0usize; shape.len()];
    for _ in 0..total {
        let p = rng() as f64 / u64::MAX as f64;
        if p < density as f64 {
            let v = (rng() as f64 / u64::MAX as f64) as f32;
            t.set(&ix, v);
        }
        // odometer
        for d in (0..shape.len()).rev() {
            ix[d] += 1;
            if ix[d] < shape[d] {
                break;
            }
            ix[d] = 0;
        }
    }
}

// ─── 1. Dense matmul via einsum ─────────────────────────────────────────

fn section_dense_matmul() {
    println!("\n=== 1. Dense matmul via einsum (homogenous vs dyn) ===");
    for &n in &[16usize, 64, 128, 256] {
        println!("\n--- {n}×{n} ---");
        let a = dense_filled(vec![n, n], 42);
        let b = dense_filled(vec![n, n], 99);
        let iters: u32 = match n {
            16 => 5000,
            64 => 500,
            128 => 100,
            256 => 20,
            _ => 5,
        };

        let homo = bench("einsum_homogenous (concrete Dense)", iters, || {
            let mut c = Dense::<f32>::zeros(vec![n, n]);
            einsum_homogenous::<f32, _, _>("ab,bc->ac", &[&a, &b], &mut [&mut c]).unwrap();
            std::hint::black_box(&c);
        });
        let dyn_t = bench("einsum (&dyn NDIndex)", iters, || {
            let mut c = Dense::<f32>::zeros(vec![n, n]);
            einsum::<f32>(
                "ab,bc->ac",
                &[&a as &dyn NDIndex<f32>, &b],
                &mut [&mut c as &mut dyn NDIndex<f32>],
            )
            .unwrap();
            std::hint::black_box(&c);
        });
        let enum_t = bench("einsum_homogenous (Tensor enum)", iters, || {
            let mut c = Dense::<f32>::zeros(vec![n, n]);
            einsum_homogenous::<f32, Tensor<f32>, Tensor<f32>>(
                "ab,bc->ac",
                &[&Tensor::Dense(&a), &Tensor::Dense(&b)],
                &mut [&mut Tensor::DenseMut(&mut c)],
            )
            .unwrap();
            std::hint::black_box(&c);
        });
        println!("  ratio (dyn  / homo): {:.2}×", dyn_t / homo);
        println!("  ratio (enum / homo): {:.2}×", enum_t / homo);
        #[cfg(feature = "jit")]
        {
            let plan = EinsumF32Plan::compile(
                "ab,bc->ac",
                &[JitInput::Dense(&a), JitInput::Dense(&b)],
                &[vec![n, n]],
            )
            .unwrap();
            let plan_name = format!("EinsumF32Plan ({:?})", plan.backend());
            let plan_t = bench(&plan_name, iters, || {
                let mut c = Dense::<f32>::zeros(vec![n, n]);
                plan.run(&[JitInput::Dense(&a), JitInput::Dense(&b)], &mut [&mut c]);
                std::hint::black_box(&c);
            });
            println!("  ratio (plan / homo): {:.4}×", plan_t / homo);
        }
    }
}

// ─── 2. CSR × CSR matmul ────────────────────────────────────────────────

fn section_csr_matmul() {
    println!("\n=== 2. CSR × CSR matmul (native vs einsum) ===");
    // 3D torus, sides s in {5, 10, 20}, e/n = 3
    for &s in &[5usize, 10, 20] {
        let a = lattice_csr(s, 3.0, 42);
        let n = (s * s * s) as u32;
        println!("\n--- side={s} (n={n}, nnz={}) ---", a.nnz());
        let iters: u32 = if s == 5 {
            2000
        } else if s == 10 {
            200
        } else {
            30
        };

        let nat = bench("Csr::matmul (native)", iters, || {
            let r = a.matmul(&a);
            std::hint::black_box(&r);
        });
        let homo = bench("einsum_homogenous (Csr inputs)", iters, || {
            let mut out = Dense::<u32>::zeros(vec![n as usize, n as usize]);
            einsum_homogenous::<u32, _, _>("ab,bc->ac", &[&a, &a], &mut [&mut out]).unwrap();
            std::hint::black_box(&out);
        });
        let dyn_t = bench("einsum (&dyn NDIndex)", iters, || {
            let mut out = Dense::<u32>::zeros(vec![n as usize, n as usize]);
            einsum::<u32>(
                "ab,bc->ac",
                &[&a as &dyn NDIndex<u32>, &a],
                &mut [&mut out as &mut dyn NDIndex<u32>],
            )
            .unwrap();
            std::hint::black_box(&out);
        });
        let enum_t = bench("einsum_homogenous (Tensor enum)", iters, || {
            let mut out = Dense::<u32>::zeros(vec![n as usize, n as usize]);
            einsum_homogenous::<u32, Tensor<u32>, Tensor<u32>>(
                "ab,bc->ac",
                &[&Tensor::Csr(&a), &Tensor::Csr(&a)],
                &mut [&mut Tensor::DenseMut(&mut out)],
            )
            .unwrap();
            std::hint::black_box(&out);
        });
        println!("  einsum_homogenous / native: {:.2}×", homo / nat);
        println!("  einsum_dyn        / native: {:.2}×", dyn_t / nat);
        println!("  einsum_enum       / native: {:.2}×", enum_t / nat);
    }
}

// ─── 3. CSR matmul_par scaling ──────────────────────────────────────────

fn section_csr_par() {
    println!("\n=== 3. CSR matmul: sequential vs rayon parallel ===");
    for &s in &[10usize, 20, 30] {
        let a = lattice_csr(s, 3.0, 42);
        let n = (s * s * s) as u32;
        println!("\n--- side={s} (n={n}, nnz={}) ---", a.nnz());
        let iters: u32 = if s == 10 {
            100
        } else if s == 20 {
            20
        } else {
            5
        };

        let seq = bench("Csr::matmul", iters, || {
            let r = a.matmul(&a);
            std::hint::black_box(&r);
        });
        let par = bench("Csr::matmul_par", iters, || {
            let r = a.matmul_par(&a);
            std::hint::black_box(&r);
        });
        println!("  speedup (seq / par): {:.2}×", seq / par);
    }
}

// ─── 4. CSR × Dense via einsum_dyn (mixed types) ────────────────────────

fn section_csr_times_dense() {
    println!("\n=== 4. CSR × Dense via einsum (mixed types: dyn vs enum) ===");
    for &(s, d) in &[(10usize, 8), (20, 16), (20, 64)] {
        let a = lattice_csr(s, 3.0, 42);
        let n = (s * s * s) as usize;
        let x = dense_filled(vec![n, d], 77);

        // Reconstruct the CSR in f32 once; reuse across both benches.
        let mut trips: Vec<(u32, u32, f32)> = Vec::with_capacity(a.nnz());
        for r in 0..a.n() {
            for (c, v) in a.row(r) {
                trips.push((r, c, v as f32));
            }
        }
        let af = Csr::<u32, f32>::from_coo(a.n(), &mut trips);

        println!("\n--- CSR({n}×{n}, nnz={}) × Dense({n}×{d}) ---", a.nnz());
        let iters: u32 = if s == 10 { 200 } else { 20 };

        let dyn_t = bench("einsum (&dyn NDIndex)", iters, || {
            let mut y = Dense::<f32>::zeros(vec![n, d]);
            einsum::<f32>(
                "ab,bc->ac",
                &[&af as &dyn NDIndex<f32>, &x],
                &mut [&mut y as &mut dyn NDIndex<f32>],
            )
            .unwrap();
            std::hint::black_box(&y);
        });
        let enum_t = bench("einsum_homogenous (Tensor enum)", iters, || {
            let mut y = Dense::<f32>::zeros(vec![n, d]);
            einsum_homogenous::<f32, Tensor<f32>, Tensor<f32>>(
                "ab,bc->ac",
                &[&Tensor::Csr(&af), &Tensor::Dense(&x)],
                &mut [&mut Tensor::DenseMut(&mut y)],
            )
            .unwrap();
            std::hint::black_box(&y);
        });
        println!("  ratio (enum / dyn): {:.2}×", enum_t / dyn_t);
        #[cfg(feature = "jit")]
        {
            let plan = EinsumF32Plan::compile(
                "ab,bc->ac",
                &[JitInput::Csr(&af), JitInput::Dense(&x)],
                &[vec![n, d]],
            )
            .unwrap();
            let plan_name = format!("EinsumF32Plan ({:?})", plan.backend());
            let plan_t = bench(&plan_name, iters, || {
                let mut y = Dense::<f32>::zeros(vec![n, d]);
                plan.run(&[JitInput::Csr(&af), JitInput::Dense(&x)], &mut [&mut y]);
                std::hint::black_box(&y);
            });
            println!("  ratio (plan / dyn): {:.4}×", plan_t / dyn_t);
            println!("  ratio (plan / enum): {:.4}×", plan_t / enum_t);
        }
    }
}

// ─── 5. Blocked attention ───────────────────────────────────────────────

fn section_blocked_attention() {
    println!("\n=== 5. Blocked attention (bhqd,bhkd→bhqk) ===");
    for &(b, h, q, k, d) in &[(2usize, 4, 64, 64, 64), (2, 8, 128, 128, 64)] {
        println!("\n--- shape b={b} h={h} q={q} k={k} d={d} ---");
        let iters: u32 = if q <= 64 { 100 } else { 20 };

        // Blocked8 — fully filled
        {
            let mut qm = Blocked8::with_shape(vec![b, h, q, d]);
            let mut km = Blocked8::with_shape(vec![b, h, k, d]);
            fill_blocked(&mut qm, &[b, h, q, d], 1.0, 42);
            fill_blocked(&mut km, &[b, h, k, d], 1.0, 99);
            bench("Blocked8 attention (100% blocks)", iters, || {
                let mut out = Blocked8::with_shape(vec![b, h, q, k]);
                attention(&qm, &km, &mut out);
                std::hint::black_box(&out);
            });
        }
        // Blocked16 — fully filled
        {
            let mut qm = Blocked16::with_shape(vec![b, h, q, d]);
            let mut km = Blocked16::with_shape(vec![b, h, k, d]);
            fill_blocked(&mut qm, &[b, h, q, d], 1.0, 42);
            fill_blocked(&mut km, &[b, h, k, d], 1.0, 99);
            bench("Blocked16 attention (100% blocks)", iters, || {
                let mut out = Blocked16::with_shape(vec![b, h, q, k]);
                attention(&qm, &km, &mut out);
                std::hint::black_box(&out);
            });
        }
        // Blocked16 — sparse (10% of scalar positions filled, blocks may still be present)
        {
            let mut qm = Blocked16::with_shape(vec![b, h, q, d]);
            let mut km = Blocked16::with_shape(vec![b, h, k, d]);
            fill_blocked(&mut qm, &[b, h, q, d], 0.10, 42);
            fill_blocked(&mut km, &[b, h, k, d], 0.10, 99);
            bench("Blocked16 attention (~10% scalar density)", iters, || {
                let mut out = Blocked16::with_shape(vec![b, h, q, k]);
                attention(&qm, &km, &mut out);
                std::hint::black_box(&out);
            });
        }
    }
}

// ─── main ───────────────────────────────────────────────────────────────

fn main() {
    println!("=== linalg perf bench ===");
    println!("(times in µs/iter, after 3-iter warmup)");

    section_dense_matmul();
    section_csr_matmul();
    section_csr_par();
    section_csr_times_dense();
    section_blocked_attention();

    println!("\n=== done ===");
}
