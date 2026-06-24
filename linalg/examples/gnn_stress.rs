//! Stress test: graph-neural-network style sparse propagation.
//!
//! Run with:
//! `cargo run --release --features jit --example gnn_stress`

use std::time::Instant;

use linalg::csr::Csr;
use linalg::dense::Dense;
use linalg::einsum::einsum;
use linalg::jit::{EinsumF32Jit, JitInput};
use linalg::tensor::NDIndex;

fn fill_rand(t: &mut Dense<f32>, mut state: u64) {
    for v in t.data.iter_mut() {
        state = state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        *v = ((state >> 32) as f32 / u32::MAX as f32) * 2.0 - 1.0;
    }
}

fn rand_graph(n: usize, per_row: usize, mut state: u64) -> Csr<u32, f32> {
    let mut triples = Vec::with_capacity(n * per_row);
    let scale = 1.0 / per_row as f32;
    for r in 0..n {
        for _ in 0..per_row {
            state = state
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            let c = (state >> 33) as usize % n;
            triples.push((r as u32, c as u32, scale));
        }
    }
    Csr::<u32, f32>::from_coo(n as u32, &mut triples)
}

fn max_abs_diff(a: &Dense<f32>, b: &Dense<f32>) -> f32 {
    a.data
        .iter()
        .zip(b.data.iter())
        .map(|(x, y)| (x - y).abs())
        .fold(0.0, f32::max)
}

fn run_vm(a: &Csr<u32, f32>, x: &Dense<f32>, y: &mut Dense<f32>) -> f64 {
    y.clear();
    let start = Instant::now();
    einsum::<f32>(
        "ab,bc->ac",
        &[a as &dyn NDIndex<f32>, x as &dyn NDIndex<f32>],
        &mut [y as &mut dyn NDIndex<f32>],
    )
    .unwrap();
    start.elapsed().as_secs_f64()
}

fn run_jit(jit: &EinsumF32Jit, a: &Csr<u32, f32>, x: &Dense<f32>, y: &mut Dense<f32>) -> f64 {
    y.clear();
    let start = Instant::now();
    jit.run(&[JitInput::Csr(a), JitInput::Dense(x)], &mut [y]);
    start.elapsed().as_secs_f64()
}

fn main() {
    const N: usize = 65_536;
    const PER_ROW: usize = 16;
    const FEATURES: usize = 64;
    const LAYERS: usize = 4;

    println!("GNN-style sparse propagation: A({N}x{N}, {PER_ROW}/row) · X({N}x{FEATURES})");

    let build_start = Instant::now();
    let a = rand_graph(N, PER_ROW, 1);
    let mut x = Dense::<f32>::zeros(vec![N, FEATURES]);
    fill_rand(&mut x, 2);
    println!(
        "  graph nnz={} build+feature-init {:.3}s",
        a.nnz(),
        build_start.elapsed().as_secs_f64()
    );

    let compile_start = Instant::now();
    let jit = EinsumF32Jit::compile(
        "ab,bc->ac",
        &[JitInput::Csr(&a), JitInput::Dense(&x)],
        &[vec![N, FEATURES]],
    )
    .unwrap();
    println!(
        "  one-time JIT compile {:.3} ms",
        compile_start.elapsed().as_secs_f64() * 1_000.0
    );

    let mut vm_out = Dense::<f32>::zeros(vec![N, FEATURES]);
    let mut jit_out = Dense::<f32>::zeros(vec![N, FEATURES]);

    let vm_s = run_vm(&a, &x, &mut vm_out);
    let jit_s = run_jit(&jit, &a, &x, &mut jit_out);
    let diff = max_abs_diff(&vm_out, &jit_out);
    let flops = 2.0 * a.nnz() as f64 * FEATURES as f64;

    println!(
        "  one layer VM {:8.3} ms  JIT {:8.3} ms  {:5.1}x faster  max_abs_diff {:.3e}",
        vm_s * 1_000.0,
        jit_s * 1_000.0,
        vm_s / jit_s,
        diff
    );
    println!(
        "  JIT effective throughput {:.2} GFLOP/s",
        flops / jit_s / 1.0e9
    );

    let mut ping = x;
    let mut pong = Dense::<f32>::zeros(vec![N, FEATURES]);
    let layers_start = Instant::now();
    for _ in 0..LAYERS {
        run_jit(&jit, &a, &ping, &mut pong);
        std::mem::swap(&mut ping, &mut pong);
    }
    let layers_s = layers_start.elapsed().as_secs_f64();
    println!(
        "  {LAYERS} JIT layers {:8.3} ms  {:.2} billion edge-feature updates/s",
        layers_s * 1_000.0,
        (a.nnz() as f64 * FEATURES as f64 * LAYERS as f64) / layers_s / 1.0e9
    );
}
