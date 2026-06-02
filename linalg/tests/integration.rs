//! Cross-module integration tests: einsum composing CSR, Dense, and Blocked.
//!
//! These tests need both `csr` and `dense` features.

#![cfg(all(feature = "csr", feature = "dense"))]

use linalg::csr::Csr;
use linalg::dense::Dense;
use linalg::einsum::{compile, einsum, einsum_homogenous};
use linalg::tensor::NDIndex;

/// Naive reference matmul for CSR × CSR.
fn naive_csr_matmul(a: &Csr<u32, u32>, b: &Csr<u32, u32>, n: usize) -> Vec<Vec<u32>> {
    let mut c = vec![vec![0u32; n]; n];
    for i in 0..n {
        for k in 0..n {
            let a_ik = a.get(i as u32, k as u32);
            if a_ik == 0 { continue; }
            for j in 0..n {
                c[i][j] += a_ik * b.get(k as u32, j as u32);
            }
        }
    }
    c
}

#[test]
fn csr_x_csr_via_einsum_matches_native_matmul() {
    let a = Csr::<u32, u32>::from_edges(6, &[
        (0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (0, 3), (5, 0), (1, 4),
    ]);
    let native = a.matmul(&a);

    // Run the same multiply through einsum into a dense output.
    let mut out = Dense::<u32>::zeros(vec![6, 6]);
    einsum_homogenous::<u32, _, _>("ab,bc->ac", &[&a, &a], &mut [&mut out]).unwrap();

    for i in 0..6 {
        for j in 0..6 {
            assert_eq!(
                out.get(&[i, j]),
                native.get(i as u32, j as u32),
                "mismatch at ({i},{j})"
            );
        }
    }
}

#[test]
fn csr_x_dense_mixed_via_einsum_dyn() {
    // 3-node triangle adjacency × 3×2 dense feature matrix.
    let a = Csr::<u32, f32>::from_coo(3, &mut vec![
        (0, 1, 1.0),
        (1, 2, 1.0),
        (2, 0, 1.0),
    ]);
    let mut x = Dense::<f32>::zeros(vec![3, 2]);
    x.fill_from(&[1., 2., 3., 4., 5., 6.]);

    let mut y = Dense::<f32>::zeros(vec![3, 2]);
    einsum::<f32>(
        "ab,bc->ac",
        &[&a as &dyn NDIndex<f32>, &x],
        &mut [&mut y as &mut dyn NDIndex<f32>],
    )
    .unwrap();

    // Row i of y = row (i+1 mod 3) of x because the triangle sends i → i+1.
    assert_eq!(y.get(&[0, 0]), 3.0);
    assert_eq!(y.get(&[0, 1]), 4.0);
    assert_eq!(y.get(&[1, 0]), 5.0);
    assert_eq!(y.get(&[1, 1]), 6.0);
    assert_eq!(y.get(&[2, 0]), 1.0);
    assert_eq!(y.get(&[2, 1]), 2.0);
}

#[test]
fn compiled_program_reused_across_executions() {
    let a = Csr::<u32, u32>::from_edges(4, &[(0, 1), (1, 2), (2, 3), (3, 0)]);

    // Compile once.
    let prog = compile::<u32, dyn NDIndex<u32>>(
        "ab,bc->ac",
        &[&a as &dyn NDIndex<u32>, &a as &dyn NDIndex<u32>],
    )
    .unwrap();

    let plan = format!("{prog}");
    assert!(plan.contains("SPARSE"), "VM should pick sparse loops:\n{plan}");

    // Execute three times into fresh outputs.
    for _ in 0..3 {
        let mut out = Dense::<u32>::zeros(vec![4, 4]);
        prog.exec(
            &[&a as &dyn NDIndex<u32>, &a as &dyn NDIndex<u32>],
            &mut [&mut out as &mut dyn NDIndex<u32>],
        );
        // A² of a 4-cycle: each node reaches the one two steps ahead.
        assert_eq!(out.get(&[0, 2]), 1);
        assert_eq!(out.get(&[1, 3]), 1);
        assert_eq!(out.get(&[2, 0]), 1);
        assert_eq!(out.get(&[3, 1]), 1);
    }
}

#[test]
fn dense_einsum_matches_hand_computation_for_random_matrices() {
    // Two small random matrices via deterministic counters — no rand
    // dependency in tests.
    let mut a = Dense::<i64>::zeros(vec![5, 7]);
    for i in 0..5 {
        for j in 0..7 {
            a.set(&[i, j], (i as i64 + 1) * (j as i64 + 1) - 10);
        }
    }
    let mut b = Dense::<i64>::zeros(vec![7, 3]);
    for i in 0..7 {
        for j in 0..3 {
            b.set(&[i, j], (i as i64) - 2 * (j as i64));
        }
    }
    let mut c = Dense::<i64>::zeros(vec![5, 3]);
    einsum_homogenous::<i64, _, _>("ab,bc->ac", &[&a, &b], &mut [&mut c]).unwrap();

    for i in 0..5 {
        for j in 0..3 {
            let mut expected = 0i64;
            for k in 0..7 {
                expected += a.get(&[i, k]) * b.get(&[k, j]);
            }
            assert_eq!(c.get(&[i, j]), expected, "({i},{j})");
        }
    }
}
