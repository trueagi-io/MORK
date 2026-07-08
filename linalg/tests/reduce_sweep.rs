//! Differential sweep over the generalized-reduction (semiring) einsum.
//!
//! Bounded companion to `einsum_sweep.rs`: enumerates specs over alphabet
//! `{a, b, c}` (dims 2, 3, 4), inputs of length 1–3 with within-input
//! repeats, 1–2 inputs, single output of distinct free labels (including
//! scalar), and every dense/CSR-sparse variant per `≥ 2D` input — crossed
//! with a set of (Reduce, Combine) operator pairs.
//!
//! Each case compares the VM (`einsum_reduce`, dyn dispatch) — and, where
//! supported, the JIT (`einsum_jit_reduce`) — element-wise against a naive
//! nested-loop semiring reference. Values are small integers so f32
//! arithmetic is exact and results must be bit-equal.
//!
//! Runs in seconds (rayon-parallel); not `#[ignore]`d.

#![cfg(all(feature = "rayon", feature = "csr", feature = "dense"))]

use std::sync::atomic::{AtomicUsize, Ordering};

use rayon::prelude::*;

use linalg::csr::Csr;
use linalg::dense::Dense;
use linalg::einsum::{einsum_reduce, Combine, Reduce};
use linalg::tensor::NDIndex;

const DIM_OF: [usize; 3] = [2, 3, 4]; // a, b, c

/// Operator pairs exercised for every spec. (Sum, Mul) anchors against the
/// classic einsum path; the rest exercise the generalized fold, including
/// non-annihilating combos where structural zeros must still compete.
const OPS: [(Reduce, Combine); 7] = [
    (Reduce::Sum, Combine::Mul),
    (Reduce::Prod, Combine::Mul),
    (Reduce::Max, Combine::Mul),
    (Reduce::Min, Combine::Mul),
    (Reduce::Max, Combine::Add),
    (Reduce::Min, Combine::Add),
    (Reduce::Sum, Combine::Add),
];

fn spec_str(inputs: &[Vec<u8>], out: &[u8]) -> String {
    let pat = |p: &[u8]| p.iter().map(|&s| (b'a' + s) as char).collect::<String>();
    let lhs: Vec<String> = inputs.iter().map(|p| pat(p)).collect();
    format!("{}->{}", lhs.join(","), pat(out))
}

/// All ordered strings of length 1–3 over the alphabet, repeats allowed.
fn all_patterns() -> Vec<Vec<u8>> {
    let mut v = Vec::new();
    for len in 1..=3u32 {
        for code in 0..3usize.pow(len) {
            let mut pat = Vec::with_capacity(len as usize);
            let mut c = code;
            for _ in 0..len {
                pat.push((c % 3) as u8);
                c /= 3;
            }
            v.push(pat);
        }
    }
    v
}

fn union_slots(patterns: &[Vec<u8>]) -> Vec<u8> {
    let mut seen = [false; 3];
    let mut out = Vec::new();
    for p in patterns {
        for &s in p {
            if !seen[s as usize] {
                seen[s as usize] = true;
                out.push(s);
            }
        }
    }
    out
}

fn permute_distinct(pool: &[u8], remaining: usize, cur: &mut Vec<u8>, out: &mut Vec<Vec<u8>>) {
    if remaining == 0 {
        out.push(cur.clone());
        return;
    }
    for &v in pool {
        if !cur.contains(&v) {
            cur.push(v);
            permute_distinct(pool, remaining - 1, cur, out);
            cur.pop();
        }
    }
}

fn output_arrangements(union: &[u8]) -> Vec<Vec<u8>> {
    let mut out = vec![Vec::new()];
    for size in 1..=union.len() {
        permute_distinct(union, size, &mut Vec::new(), &mut out);
    }
    out
}

/// Deterministic small integers in `-2..=2`, with zeros so sparse structure
/// is non-trivial and signs so max/min disagree with sum.
fn fill_input(shape: &[usize], seed: u64) -> Vec<f32> {
    let n: usize = if shape.is_empty() { 1 } else { shape.iter().product() };
    let mut state = seed.wrapping_mul(0x9E37_79B9_7F4A_7C15).wrapping_add(0xDEAD_BEEF);
    let mut data = Vec::with_capacity(n);
    for _ in 0..n {
        state = state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        data.push(((state >> 33) % 5) as i32 as f32 - 2.0);
    }
    data
}

fn dense_to_csr(shape: Vec<usize>, data: &[f32]) -> Csr<u32, f32> {
    let cols = *shape.last().unwrap();
    let rows: usize = shape[..shape.len() - 1].iter().product();
    let mut row_ptr = vec![0usize; rows + 1];
    let mut col_idx = Vec::new();
    let mut values = Vec::new();
    for r in 0..rows {
        for c in 0..cols {
            let v = data[r * cols + c];
            if v != 0.0 {
                col_idx.push(c as u32);
                values.push(v);
            }
        }
        row_ptr[r + 1] = col_idx.len();
    }
    Csr::<u32, f32>::from_parts(shape, row_ptr, col_idx, values)
}

/// Naive semiring reference over the full Cartesian index space.
fn naive_reduce(
    input_patterns: &[Vec<u8>],
    input_shapes: &[Vec<usize>],
    input_data: &[Vec<f32>],
    out_pattern: &[u8],
    out_shape: &[usize],
    reduce: Reduce,
    combine: Combine,
) -> Vec<f32> {
    let out_len: usize = if out_shape.is_empty() { 1 } else { out_shape.iter().product() };
    let mut out = vec![reduce.identity::<f32>(); out_len];

    let slots = union_slots(input_patterns);
    let dims: Vec<usize> = slots.iter().map(|&s| DIM_OF[s as usize]).collect();
    let n = slots.len();
    let mut vals = [0usize; 3];
    let mut idx = vec![0usize; n];
    if dims.iter().any(|&d| d == 0) {
        return out;
    }
    loop {
        for (k, &s) in slots.iter().enumerate() {
            vals[s as usize] = idx[k];
        }
        let mut contrib: Option<f32> = None;
        for (i, pat) in input_patterns.iter().enumerate() {
            let shape = &input_shapes[i];
            let mut a = 0usize;
            for (k, &s) in pat.iter().enumerate() {
                a = a * shape[k] + vals[s as usize];
            }
            let v = input_data[i][a];
            contrib = Some(match contrib {
                Some(p) => combine.apply(p, v),
                None => v,
            });
        }
        let mut oa = 0usize;
        for (k, &s) in out_pattern.iter().enumerate() {
            oa = oa * out_shape[k] + vals[s as usize];
        }
        out[oa] = reduce.apply(out[oa], contrib.unwrap());

        let mut k = n;
        let stop = loop {
            if k == 0 {
                break true;
            }
            k -= 1;
            idx[k] += 1;
            if idx[k] < dims[k] {
                break false;
            }
            idx[k] = 0;
        };
        if stop {
            break;
        }
    }
    out
}

fn check_case(
    input_patterns: &[Vec<u8>],
    out_pattern: &[u8],
    sparse_mask: &[bool],
    reduce: Reduce,
    combine: Combine,
) {
    let in_shapes: Vec<Vec<usize>> = input_patterns
        .iter()
        .map(|p| p.iter().map(|&s| DIM_OF[s as usize]).collect())
        .collect();
    let out_shape: Vec<usize> = out_pattern.iter().map(|&s| DIM_OF[s as usize]).collect();
    let spec = spec_str(input_patterns, out_pattern);

    let in_data: Vec<Vec<f32>> = in_shapes
        .iter()
        .enumerate()
        .map(|(i, s)| fill_input(s, (i as u64) * 7 + 1))
        .collect();

    let expected = naive_reduce(
        input_patterns,
        &in_shapes,
        &in_data,
        out_pattern,
        &out_shape,
        reduce,
        combine,
    );

    let dense_inputs: Vec<Dense<f32>> = in_shapes
        .iter()
        .zip(&in_data)
        .map(|(s, d)| {
            let mut t = Dense::<f32>::zeros(s.clone());
            t.fill_from(d);
            t
        })
        .collect();
    let csr_inputs: Vec<Option<Csr<u32, f32>>> = in_shapes
        .iter()
        .zip(&in_data)
        .zip(sparse_mask)
        .map(|((s, d), &sp)| if sp { Some(dense_to_csr(s.clone(), d)) } else { None })
        .collect();

    // VM, dyn dispatch, mixed dense/sparse per mask.
    let vm_ins: Vec<&dyn NDIndex<f32>> = csr_inputs
        .iter()
        .zip(&dense_inputs)
        .map(|(c, d)| match c {
            Some(c) => c as &dyn NDIndex<f32>,
            None => d as &dyn NDIndex<f32>,
        })
        .collect();
    let mut vm_out = Dense::<f32>::zeros(out_shape.clone());
    einsum_reduce::<f32>(
        &spec,
        reduce,
        combine,
        &vm_ins,
        &mut [&mut vm_out as &mut dyn NDIndex<f32>],
    )
    .unwrap_or_else(|e| panic!("VM failed on {spec} ({reduce:?},{combine:?}): {e}"));
    assert_eq!(
        vm_out.data, expected,
        "VM mismatch: {spec} ({reduce:?},{combine:?}) sparse={sparse_mask:?}"
    );

    // JIT — dense inputs only (sparse non-(Sum,Mul) is rejected by design;
    // sparse (Sum,Mul) is covered exhaustively by einsum_sweep).
    #[cfg(feature = "jit")]
    if sparse_mask.iter().all(|&s| !s) {
        use linalg::jit::{einsum_jit_reduce, JitInput};
        let jit_ins: Vec<JitInput> = dense_inputs.iter().map(JitInput::Dense).collect();
        let mut jit_out = Dense::<f32>::zeros(out_shape.clone());
        einsum_jit_reduce(&spec, reduce, combine, &jit_ins, &mut [&mut jit_out])
            .unwrap_or_else(|e| panic!("JIT failed on {spec} ({reduce:?},{combine:?}): {e}"));
        assert_eq!(
            jit_out.data, expected,
            "JIT mismatch: {spec} ({reduce:?},{combine:?})"
        );
    }
}

/// Every dense/sparse mask over inputs (sparse only possible for rank ≥ 2).
fn sparse_masks(input_patterns: &[Vec<u8>]) -> Vec<Vec<bool>> {
    let can: Vec<bool> = input_patterns.iter().map(|p| p.len() >= 2).collect();
    let mut masks = vec![vec![false; input_patterns.len()]];
    for i in 0..input_patterns.len() {
        if can[i] {
            for m in masks.clone() {
                let mut m2 = m;
                m2[i] = true;
                masks.push(m2);
            }
        }
    }
    masks
}

#[test]
fn reduce_differential_sweep() {
    let patterns = all_patterns();
    let cases = AtomicUsize::new(0);

    // n = 1 input.
    patterns.par_iter().for_each(|p| {
        let inputs = vec![p.clone()];
        let union = union_slots(&inputs);
        for out in output_arrangements(&union) {
            for mask in sparse_masks(&inputs) {
                for (r, c) in OPS {
                    check_case(&inputs, &out, &mask, r, c);
                    cases.fetch_add(1, Ordering::Relaxed);
                }
            }
        }
    });

    // n = 2 inputs.
    patterns.par_iter().for_each(|p1| {
        for p2 in &patterns {
            let inputs = vec![p1.clone(), p2.clone()];
            let union = union_slots(&inputs);
            for out in output_arrangements(&union) {
                for mask in sparse_masks(&inputs) {
                    for (r, c) in OPS {
                        check_case(&inputs, &out, &mask, r, c);
                        cases.fetch_add(1, Ordering::Relaxed);
                    }
                }
            }
        }
    });

    let total = cases.load(Ordering::Relaxed);
    println!("[reduce_sweep] {total} cases checked");
    assert!(total > 100_000, "expected a substantial sweep, got {total}");
}
