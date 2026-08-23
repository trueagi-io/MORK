//! Million-node graph propagation with the sparse einsum JIT.
//!
//! Run with:
//! `cargo run --release --features jit --example gnn_million`

use std::time::Instant;

use linalg::csr::Csr;
use linalg::dense::Dense;
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

fn manual_row_feature(a: &Csr<u32, f32>, x: &Dense<f32>, row: usize, feature: usize) -> f32 {
    let mut acc = 0.0;
    for (col, value) in a.row(row as u32) {
        acc += value * x.get(&[col as usize, feature]);
    }
    acc
}

fn main() {
    const N: usize = 1_048_576;
    const PER_ROW: usize = 16;
    const FEATURES: usize = 32;
    const LAYERS: usize = 4;

    println!("million-node sparse propagation: A({N}x{N}, {PER_ROW}/row) · X({N}x{FEATURES})");

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

    let mut y = Dense::<f32>::zeros(vec![N, FEATURES]);
    let start = Instant::now();
    jit.run(&[JitInput::Csr(&a), JitInput::Dense(&x)], &mut [&mut y]);
    let one_layer_s = start.elapsed().as_secs_f64();

    let row = 123_456;
    let feature = 17;
    let expected = manual_row_feature(&a, &x, row, feature);
    let got = y.get(&[row, feature]);
    println!(
        "  one layer JIT {:8.3} ms  spot_check row={row} feature={feature} diff={:.3e}",
        one_layer_s * 1_000.0,
        (expected - got).abs()
    );

    let mut ping = x;
    let mut pong = y;
    let start = Instant::now();
    for _ in 1..LAYERS {
        pong.clear();
        jit.run(
            &[JitInput::Csr(&a), JitInput::Dense(&ping)],
            &mut [&mut pong],
        );
        std::mem::swap(&mut ping, &mut pong);
    }
    let remaining_s = start.elapsed().as_secs_f64();
    let total_s = one_layer_s + remaining_s;
    let edge_feature_updates = a.nnz() as f64 * FEATURES as f64 * LAYERS as f64;
    let flops = 2.0 * edge_feature_updates;

    println!(
        "  {LAYERS} layers total {:8.3} ms  {:.2} billion edge-feature updates/s  {:.2} GFLOP/s",
        total_s * 1_000.0,
        edge_feature_updates / total_s / 1.0e9,
        flops / total_s / 1.0e9
    );
}
