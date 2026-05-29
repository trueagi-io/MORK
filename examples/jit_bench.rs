//! Quick comparison: JIT einsum vs the interpreted VM, dense f32.
//!
//! Run with: `cargo run --release --features jit --example jit_bench`

use std::time::Instant;

use linalg::dense::Dense;
use linalg::einsum::einsum_homogenous;
use linalg::jit::DenseF32Jit;

fn fill_rand(t: &mut Dense<f32>, mut state: u64) {
    for v in t.data.iter_mut() {
        state = state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        *v = ((state >> 33) as f32 / u32::MAX as f32) * 2.0 - 1.0;
    }
}

fn time<F: FnMut()>(iters: u32, mut f: F) -> f64 {
    for _ in 0..3 {
        f();
    }
    let start = Instant::now();
    for _ in 0..iters {
        f();
    }
    start.elapsed().as_nanos() as f64 / iters as f64 / 1000.0
}

fn bench_matmul(n: usize, iters: u32) {
    let mut a = Dense::<f32>::zeros(vec![n, n]);
    let mut b = Dense::<f32>::zeros(vec![n, n]);
    fill_rand(&mut a, 1);
    fill_rand(&mut b, 2);

    let jit =
        DenseF32Jit::compile("ab,bc->ac", &[vec![n, n], vec![n, n]], &[vec![n, n]]).unwrap();

    let vm_us = time(iters, || {
        let mut c = Dense::<f32>::zeros(vec![n, n]);
        einsum_homogenous::<f32, _, _>("ab,bc->ac", &[&a, &b], &mut [&mut c]).unwrap();
    });
    let jit_us = time(iters, || {
        let mut c = Dense::<f32>::zeros(vec![n, n]);
        jit.run(&[&a, &b], &mut [&mut c]);
    });

    println!(
        "  matmul {n:>4}x{n:<4}  VM {vm_us:>11.2} µs   JIT {jit_us:>10.2} µs   {:>6.1}× faster",
        vm_us / jit_us
    );
}

fn main() {
    println!("dense f32 einsum: interpreted VM vs cranelift JIT (compile-once, run-many)\n");
    bench_matmul(16, 20000);
    bench_matmul(32, 5000);
    bench_matmul(64, 1000);
    bench_matmul(128, 200);
    bench_matmul(256, 40);

    // Show one-time JIT compile cost separately.
    let start = Instant::now();
    let _ = DenseF32Jit::compile("ab,bc->ac", &[vec![256, 256], vec![256, 256]], &[vec![256, 256]])
        .unwrap();
    println!("\n  one-time JIT compile (256x256 matmul): {:.1} µs", start.elapsed().as_nanos() as f64 / 1000.0);
}
