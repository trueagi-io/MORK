//! Throughput benchmarks for the in-place scalar tensor transforms in
//! [`linalg::scalar`].
//!
//! Measures the full op surface — abs/min/max/clamp, the trig and inverse-trig
//! family, sqrt/cbrt/ln/exp, powf/powi — on a large `Dense` array, for `f32`
//! and `f64`. Reports net per-element throughput (Melem/s) and the implied
//! memory bandwidth (GB/s, counting one read + one write per element).
//!
//! Each op runs in place, so the buffer is refreshed from a pristine source
//! every iteration; that `copy_from_slice` cost is measured separately and
//! subtracted, isolating the math from the refresh.
//!
//! Custom `Instant` timing, matching `benches/perf.rs` (no criterion).
//!
//! Run the default std-math path:
//!     cargo bench -p linalg --bench scalar
//! Run the Intel MKL VML path (needs `mkl_rt` on the link/run path):
//!     cargo bench -p linalg --bench scalar --features intel-mkl
//!
//! Env overrides: `SCALAR_N` (element count, default 1<<22),
//! `SCALAR_ITERS` (timed iterations, default 50).

use std::time::Instant;

use linalg::dense::Dense;
use linalg::scalar::{MathScalar, ScalarTransform};

/// Which backend was compiled in — selected by the `intel-mkl` feature.
fn backend() -> &'static str {
    if cfg!(feature = "intel-mkl") {
        "Intel MKL VML"
    } else {
        "std math"
    }
}

fn env_usize(key: &str, default: usize) -> usize {
    std::env::var(key).ok().and_then(|s| s.parse().ok()).unwrap_or(default)
}

/// Float element usable as benchmark input.
trait Elem: Copy {
    const BYTES: usize;
    fn from_f64(x: f64) -> Self;
}
impl Elem for f32 {
    const BYTES: usize = 4;
    fn from_f64(x: f64) -> Self {
        x as f32
    }
}
impl Elem for f64 {
    const BYTES: usize = 8;
    fn from_f64(x: f64) -> Self {
        x
    }
}

/// Inputs in `(0, 1)` — a domain valid for every op (asin/acos need `[-1,1]`,
/// sqrt/ln need `≥ 0`, powf needs a non-negative base).
fn sample(i: usize) -> f64 {
    ((i % 1000) as f64 + 0.5) / 1000.0
}

/// Warm up, then time `iters` calls of `f`, returning total seconds.
fn time(iters: usize, mut f: impl FnMut()) -> f64 {
    for _ in 0..3 {
        f();
    }
    let start = Instant::now();
    for _ in 0..iters {
        f();
    }
    start.elapsed().as_secs_f64()
}

fn run<E: Elem + MathScalar>(label: &str, n: usize, iters: usize) {
    let src: Vec<E> = (0..n).map(|i| E::from_f64(sample(i))).collect();
    let mut work = Dense::<E> { data: src.clone(), shape: vec![n] };

    // Buffer-refresh baseline: the per-iter cost we subtract from every op.
    let copy_secs = time(iters, || {
        work.data.copy_from_slice(&src);
        std::hint::black_box(&work.data);
    });
    let total_elems = n as f64 * iters as f64;

    println!(
        "  [{label}]  refresh baseline {:8.2} µs/iter  ({:.1} GB/s copy)",
        copy_secs / iters as f64 * 1e6,
        total_elems * E::BYTES as f64 / copy_secs / 1e9,
    );
    println!(
        "    {:8} {:>12} {:>14} {:>11}",
        "op", "net µs/iter", "Melem/s", "GB/s"
    );

    let mut bench = |name: &str, op: &mut dyn FnMut(&mut Dense<E>)| {
        let total = time(iters, || {
            work.data.copy_from_slice(&src);
            op(&mut work);
            std::hint::black_box(&work.data);
        });
        let op_secs = (total - copy_secs).max(1e-12);
        let melem = total_elems / op_secs / 1e6;
        let gbps = total_elems * 2.0 * E::BYTES as f64 / op_secs / 1e9;
        println!(
            "    {name:8} {:12.2} {melem:14.1} {gbps:11.2}",
            op_secs / iters as f64 * 1e6
        );
    };

    let half = E::from_f64(0.5);
    let lo = E::from_f64(0.2);
    let hi = E::from_f64(0.8);
    let two = E::from_f64(2.0);
    let exp_f = E::from_f64(2.5);

    bench("abs", &mut |d| { d.abs(); });
    bench("min", &mut |d| { d.min(half); });
    bench("max", &mut |d| { d.max(half); });
    bench("clamp", &mut |d| { d.clamp(lo, hi); });
    bench("sin", &mut |d| { d.sin(); });
    bench("cos", &mut |d| { d.cos(); });
    bench("tan", &mut |d| { d.tan(); });
    bench("asin", &mut |d| { d.asin(); });
    bench("acos", &mut |d| { d.acos(); });
    bench("atan", &mut |d| { d.atan(); });
    bench("atan2", &mut |d| { d.atan2(two); });
    bench("sqrt", &mut |d| { d.sqrt(); });
    bench("cbrt", &mut |d| { d.cbrt(); });
    bench("ln", &mut |d| { d.ln(); });
    bench("exp", &mut |d| { d.exp(); });
    bench("powf", &mut |d| { d.powf(exp_f); });
    bench("powi", &mut |d| { d.powi(3); });
    println!();
}

fn main() {
    let n = env_usize("SCALAR_N", 1 << 22);
    let iters = env_usize("SCALAR_ITERS", 50);

    println!("scalar transform throughput");
    println!("  backend: {}", backend());
    println!("  N = {n} elements, {iters} timed iters\n");

    run::<f32>("f32", n, iters);
    run::<f64>("f64", n, iters);
}
