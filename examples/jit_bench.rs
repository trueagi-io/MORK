//! Quick comparison: JIT einsum vs the interpreted VM, dense f32.
//!
//! Run with: `cargo run --release --features jit --example jit_bench`

use std::time::Instant;

use linalg::csr::Csr;
use linalg::dense::Dense;
use linalg::einsum::{einsum, einsum_homogenous};
use linalg::jit::{EinsumF32Jit, JitInput};
use linalg::tensor::NDIndex;

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

    let jit = EinsumF32Jit::compile(
        "ab,bc->ac",
        &[JitInput::Dense(&a), JitInput::Dense(&b)],
        &[vec![n, n]],
    )
    .unwrap();

    let vm_us = time(iters, || {
        let mut c = Dense::<f32>::zeros(vec![n, n]);
        einsum_homogenous::<f32, _, _>("ab,bc->ac", &[&a, &b], &mut [&mut c]).unwrap();
    });
    let jit_us = time(iters, || {
        let mut c = Dense::<f32>::zeros(vec![n, n]);
        jit.run(&[JitInput::Dense(&a), JitInput::Dense(&b)], &mut [&mut c]);
    });

    println!(
        "  matmul {n:>4}x{n:<4}  VM {vm_us:>11.2} µs   JIT {jit_us:>10.2} µs   {:>6.1}× faster",
        vm_us / jit_us
    );
}

/// Random sparse n×n CSR with ~`per_row` non-zeros per row.
fn rand_csr(n: usize, per_row: usize, mut state: u64) -> Csr<u32, f32> {
    let mut triples: Vec<(u32, u32, f32)> = Vec::new();
    for r in 0..n {
        for _ in 0..per_row {
            state = state
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            let c = (state >> 33) as usize % n;
            let v = ((state >> 17) as f32 / u32::MAX as f32) * 2.0 - 1.0;
            triples.push((r as u32, c as u32, v));
        }
    }
    Csr::<u32, f32>::from_coo(n as u32, &mut triples)
}

fn bench_csr_dense(n: usize, per_row: usize, cols: usize, iters: u32) {
    let a = rand_csr(n, per_row, 7);
    let mut x = Dense::<f32>::zeros(vec![n, cols]);
    fill_rand(&mut x, 9);

    let jit = EinsumF32Jit::compile(
        "ab,bc->ac",
        &[JitInput::Csr(&a), JitInput::Dense(&x)],
        &[vec![n, cols]],
    )
    .unwrap();

    let vm_us = time(iters, || {
        let mut y = Dense::<f32>::zeros(vec![n, cols]);
        einsum::<f32>(
            "ab,bc->ac",
            &[&a as &dyn NDIndex<f32>, &x],
            &mut [&mut y as &mut dyn NDIndex<f32>],
        )
        .unwrap();
    });
    let jit_us = time(iters, || {
        let mut y = Dense::<f32>::zeros(vec![n, cols]);
        jit.run(&[JitInput::Csr(&a), JitInput::Dense(&x)], &mut [&mut y]);
    });
    println!(
        "  CSR({n}x{n}, {per_row}/row) x Dense({n}x{cols})   VM {vm_us:>10.2} µs   JIT {jit_us:>9.2} µs   {:>6.1}× faster",
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

    println!("\nsparse: CSR x Dense (native sparse row iteration) vs the VM\n");
    bench_csr_dense(256, 8, 32, 2000);
    bench_csr_dense(1024, 16, 32, 200);
    bench_csr_dense(4096, 16, 64, 30);

    // Show one-time JIT compile cost separately.
    let big_a = Dense::<f32>::zeros(vec![256, 256]);
    let big_b = Dense::<f32>::zeros(vec![256, 256]);
    let start = Instant::now();
    let _ = EinsumF32Jit::compile(
        "ab,bc->ac",
        &[JitInput::Dense(&big_a), JitInput::Dense(&big_b)],
        &[vec![256, 256]],
    )
    .unwrap();
    println!(
        "\n  one-time JIT compile (256x256 matmul): {:.1} µs",
        start.elapsed().as_nanos() as f64 / 1000.0
    );
}
