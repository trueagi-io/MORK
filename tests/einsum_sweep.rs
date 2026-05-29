//! Exhaustive differential sweep over the einsum design space.
//!
//! Enumerates every einsum spec under the bounds:
//! - alphabet `{a, b, c, d}` (up to 4 distinct indices),
//! - 1–2 inputs (ordered, may repeat),
//! - each input is an ordered string of length 1–4 over the alphabet, **with
//!   within-input repeats allowed** (so traces like `"aa"` are included),
//! - single output: any ordered sequence of distinct free indices, **including
//!   the empty (scalar) output**,
//! - per `≥ 2D` input, both dense and CSR-sparse variants are exercised.
//!
//! For each case the result of the runtime VM and the Cranelift JIT is
//! compared element-wise against a naive nested-loop reference. Input data
//! is small integer-valued so f32 arithmetic is exact and we can assert
//! bit-equal results. The JIT backend is freed after every case so the test
//! does not accumulate compiled code memory.
//!
//! Approximately 19.5 million cases. Marked `#[ignore]` — run on demand with:
//!
//! ```text
//! cargo test --features jit --release --test einsum_sweep -- --ignored --nocapture
//! ```

#![cfg(all(feature = "jit", feature = "rayon", feature = "csr", feature = "dense"))]

use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Instant;

use rayon::prelude::*;

use linalg::csr::Csr;
use linalg::dense::Dense;
use linalg::einsum::einsum;
use linalg::jit::{EinsumF32Jit, JitError, JitInput};
use linalg::tensor::NDIndex;

// ─────────────────────────────────────────────────────────────────────────
// Fixed per-label dimensions. Distinct so any stride/shape bug shows up.
// ─────────────────────────────────────────────────────────────────────────

const DIM_OF: [usize; 4] = [2, 3, 4, 5]; // a, b, c, d

fn slot_to_ch(s: u8) -> char {
    (b'a' + s) as char
}

fn pat_str(p: &[u8]) -> String {
    p.iter().map(|&s| slot_to_ch(s)).collect()
}

fn spec_str(inputs: &[Vec<u8>], out: &[u8]) -> String {
    let lhs: Vec<String> = inputs.iter().map(|p| pat_str(p)).collect();
    format!("{}->{}", lhs.join(","), pat_str(out))
}

fn input_shape(pat: &[u8]) -> Vec<usize> {
    pat.iter().map(|&s| DIM_OF[s as usize]).collect()
}

// ─────────────────────────────────────────────────────────────────────────
// Enumerators
// ─────────────────────────────────────────────────────────────────────────

/// All 340 ordered strings of length 1–4 over the alphabet, repeats allowed.
fn all_patterns() -> Vec<Vec<u8>> {
    let mut v = Vec::with_capacity(340);
    for len in 1..=4 {
        let total = 4usize.pow(len as u32);
        for code in 0..total {
            let mut pat = Vec::with_capacity(len);
            let mut c = code;
            for _ in 0..len {
                pat.push((c % 4) as u8);
                c /= 4;
            }
            v.push(pat);
        }
    }
    v
}

fn union_slots(patterns: &[Vec<u8>]) -> Vec<u8> {
    let mut seen = [false; 4];
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

/// All ordered sequences of distinct labels drawn from `union`, of every
/// length 0..=|union| (including the empty sequence = scalar output).
fn output_arrangements(union: &[u8]) -> Vec<Vec<u8>> {
    let mut out = vec![Vec::new()];
    for size in 1..=union.len() {
        permute_distinct(union, size, &mut Vec::new(), &mut out);
    }
    out
}

// ─────────────────────────────────────────────────────────────────────────
// Data + sparse construction
// ─────────────────────────────────────────────────────────────────────────

/// Deterministic small-integer values in `-2..=2`. Including 0 so the sparse
/// path actually skips structural zeros. Range stays inside f32 exact ints.
fn fill_input(shape: &[usize], seed: u64) -> Vec<f32> {
    let n: usize = if shape.is_empty() { 1 } else { shape.iter().product() };
    let mut state = seed.wrapping_mul(0x9E37_79B9_7F4A_7C15).wrapping_add(0xDEAD_BEEF);
    let mut data = Vec::with_capacity(n);
    for _ in 0..n {
        state = state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let r = ((state >> 33) % 5) as i32 - 2;
        data.push(r as f32);
    }
    data
}

/// Build a CSR view of the same logical data: the last axis is the stored
/// column, the leading axes flatten row-major into compound rows.
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

// ─────────────────────────────────────────────────────────────────────────
// Naive nested-loop reference
// ─────────────────────────────────────────────────────────────────────────

fn naive_einsum(
    input_patterns: &[Vec<u8>],
    input_shapes: &[Vec<usize>],
    input_data: &[Vec<f32>],
    out_pattern: &[u8],
    out_shape: &[usize],
) -> Vec<f32> {
    let out_len: usize = if out_shape.is_empty() { 1 } else { out_shape.iter().product() };
    let mut out = vec![0.0f32; out_len];

    // Union of all slots used, with their dims.
    let mut seen = [false; 4];
    let mut slots = Vec::new();
    for p in input_patterns.iter().chain(std::iter::once(&out_pattern.to_vec())) {
        for &s in p {
            if !seen[s as usize] {
                seen[s as usize] = true;
                slots.push(s);
            }
        }
    }
    let dims: Vec<usize> = slots.iter().map(|&s| DIM_OF[s as usize]).collect();
    let n = slots.len();

    let mut vals = [0usize; 4];
    if n == 0 {
        // No iteration: product is 1 (empty product), but with no inputs this
        // shouldn't happen — we always have at least one input with ≥1 axis.
        return out;
    }
    let mut idx = vec![0usize; n];
    loop {
        for (k, &s) in slots.iter().enumerate() {
            vals[s as usize] = idx[k];
        }
        // Product of input element values.
        let mut prod = 1.0f32;
        for (i, pat) in input_patterns.iter().enumerate() {
            let shape = &input_shapes[i];
            let mut a = 0usize;
            for (k, &s) in pat.iter().enumerate() {
                a = a * shape[k] + vals[s as usize];
            }
            prod *= input_data[i][a];
        }
        // Output address.
        let mut oa = 0usize;
        for (k, &s) in out_pattern.iter().enumerate() {
            oa = oa * out_shape[k] + vals[s as usize];
        }
        out[oa] += prod;

        // Increment Cartesian counter.
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

// ─────────────────────────────────────────────────────────────────────────
// Per-case differential check
// ─────────────────────────────────────────────────────────────────────────

fn check_case(input_patterns: &[Vec<u8>], out_pattern: &[u8], sparse_mask: &[bool]) {
    let in_shapes: Vec<Vec<usize>> = input_patterns.iter().map(|p| input_shape(p)).collect();
    let out_shape: Vec<usize> = out_pattern.iter().map(|&s| DIM_OF[s as usize]).collect();

    let in_data: Vec<Vec<f32>> = in_shapes
        .iter()
        .enumerate()
        .map(|(i, s)| fill_input(s, (i as u64) * 7 + 1))
        .collect();

    let expected = naive_einsum(input_patterns, &in_shapes, &in_data, out_pattern, &out_shape);

    // Dense tensors (kept around for both VM and JIT to borrow).
    let dense_inputs: Vec<Dense<f32>> = in_shapes
        .iter()
        .zip(&in_data)
        .map(|(s, d)| {
            let mut t = Dense::<f32>::zeros(s.clone());
            t.fill_from(d);
            t
        })
        .collect();

    // CSR equivalents where requested.
    let csr_inputs: Vec<Option<Csr<u32, f32>>> = (0..input_patterns.len())
        .map(|i| {
            if sparse_mask[i] {
                Some(dense_to_csr(in_shapes[i].clone(), &in_data[i]))
            } else {
                None
            }
        })
        .collect();

    let spec = spec_str(input_patterns, out_pattern);

    // ── VM (dyn) ──
    let mut vm_out = Dense::<f32>::zeros(out_shape.clone());
    {
        let in_refs: Vec<&dyn NDIndex<f32>> = (0..input_patterns.len())
            .map(|i| {
                if let Some(c) = &csr_inputs[i] {
                    c as &dyn NDIndex<f32>
                } else {
                    &dense_inputs[i] as &dyn NDIndex<f32>
                }
            })
            .collect();
        einsum::<f32>(&spec, &in_refs, &mut [&mut vm_out as &mut dyn NDIndex<f32>])
            .unwrap_or_else(|e| panic!("VM rejected spec {spec}: {e}"));
    }
    if vm_out.data != expected {
        panic!(
            "VM mismatch on {spec} sparse={sparse_mask:?}:\n  expected {expected:?}\n  got      {:?}",
            vm_out.data
        );
    }

    // ── JIT ──
    let jit_inputs: Vec<JitInput> = (0..input_patterns.len())
        .map(|i| {
            if let Some(c) = &csr_inputs[i] {
                JitInput::Csr(c)
            } else {
                JitInput::Dense(&dense_inputs[i])
            }
        })
        .collect();

    match EinsumF32Jit::compile(&spec, &jit_inputs, &[out_shape.clone()]) {
        Ok(jit) => {
            let mut jit_out = Dense::<f32>::zeros(out_shape.clone());
            jit.run(&jit_inputs, &mut [&mut jit_out]);
            jit.free_memory();
            if jit_out.data != expected {
                panic!(
                    "JIT mismatch on {spec} sparse={sparse_mask:?}:\n  expected {expected:?}\n  got      {:?}",
                    jit_out.data
                );
            }
        }
        // Some sparse schedules (e.g. two sparse operands sharing the col
        // index, or a sparse trace input) genuinely have no JIT row-iteration
        // schedule and the backend rejects them on purpose. Those are still
        // exercised by the VM check above.
        Err(JitError::Unsupported(_)) => {}
        Err(e) => panic!("Unexpected JIT compile error on {spec}: {e}"),
    }
}

struct Sweep {
    counter: AtomicUsize,
    total: usize,
    start: Instant,
    progress_every: usize,
}

fn fmt_secs(secs: f64) -> String {
    let s = secs as u64;
    if s < 60 {
        format!("{s:>3}s")
    } else if s < 3600 {
        format!("{:>2}m{:02}s", s / 60, s % 60)
    } else {
        format!("{}h{:02}m{:02}s", s / 3600, (s % 3600) / 60, s % 60)
    }
}

fn enumerate_outputs_and_masks(inputs: &[Vec<u8>], sweep: &Sweep) {
    let union = union_slots(inputs);
    let arrangements = output_arrangements(&union);
    let eligible: Vec<usize> = (0..inputs.len()).filter(|&i| inputs[i].len() >= 2).collect();

    let n_masks = 1usize << eligible.len();
    let mut sparse_mask = vec![false; inputs.len()];

    for output in &arrangements {
        for bits in 0..n_masks {
            for v in &mut sparse_mask {
                *v = false;
            }
            for (k, &i) in eligible.iter().enumerate() {
                sparse_mask[i] = (bits >> k) & 1 == 1;
            }
            check_case(inputs, output, &sparse_mask);

            let n = sweep.counter.fetch_add(1, Ordering::Relaxed) + 1;
            if n % sweep.progress_every == 0 {
                let elapsed = sweep.start.elapsed().as_secs_f64();
                let pct = n as f64 * 100.0 / sweep.total as f64;
                let rate = n as f64 / elapsed.max(1e-6);
                let eta = (sweep.total - n) as f64 / rate;
                eprintln!(
                    "  {n:>10} / {} ({pct:5.1}%)  elapsed {}  ETA {}  ({:.0}k/s)",
                    sweep.total,
                    fmt_secs(elapsed),
                    fmt_secs(eta),
                    rate / 1000.0,
                );
            }
        }
    }
}

/// Pre-compute the exact case count from the enumeration parameters: for each
/// input-tuple, # outputs = A(|union|) (arrangements incl. empty) and # sparse
/// masks = 2^(inputs with ndim >= 2). Cheap (~115k input-tuples) — done once.
fn total_cases(patterns: &[Vec<u8>]) -> usize {
    // A(s) = sum_{m=0..=s} P(s,m) = arrangements of a size-s set, incl. empty.
    let a = [1usize, 2, 5, 16, 65];
    let union2 = |p1: &[u8], p2: &[u8]| -> usize {
        let mut seen = [false; 4];
        for &s in p1.iter().chain(p2) {
            seen[s as usize] = true;
        }
        seen.iter().filter(|&&b| b).count()
    };
    let distinct = |p: &[u8]| -> usize {
        let mut seen = [false; 4];
        for &s in p {
            seen[s as usize] = true;
        }
        seen.iter().filter(|&&b| b).count()
    };
    let sparse_mult = |p: &[u8]| -> usize {
        if p.len() >= 2 { 2 } else { 1 }
    };
    let mut total = 0usize;
    for p in patterns {
        total += a[distinct(p)] * sparse_mult(p);
    }
    for p1 in patterns {
        for p2 in patterns {
            total += a[union2(p1, p2)] * sparse_mult(p1) * sparse_mult(p2);
        }
    }
    total
}

// ─────────────────────────────────────────────────────────────────────────
// The test
// ─────────────────────────────────────────────────────────────────────────

#[test]
#[ignore = "exhaustive: ~19.5M cases — run with --ignored --release"]
fn exhaustive_einsum_sweep_up_to_2_inputs() {
    let patterns = all_patterns();
    assert_eq!(patterns.len(), 340);

    let total = total_cases(&patterns);
    eprintln!("[plan] {total} total cases to check");

    let sweep = Sweep {
        counter: AtomicUsize::new(0),
        total,
        start: Instant::now(),
        progress_every: 100_000,
    };

    eprintln!("[n=1] {} input patterns…", patterns.len());
    patterns.par_iter().for_each(|p1| {
        let inputs = vec![p1.clone()];
        enumerate_outputs_and_masks(&inputs, &sweep);
    });
    let after_n1 = sweep.counter.load(Ordering::Relaxed);
    eprintln!(
        "[n=1] done: {after_n1} cases ({:.1}%) in {}",
        after_n1 as f64 * 100.0 / total as f64,
        fmt_secs(sweep.start.elapsed().as_secs_f64()),
    );

    eprintln!("[n=2] {}^2 input pairs…", patterns.len());
    patterns.par_iter().for_each(|p1| {
        for p2 in &patterns {
            let inputs = vec![p1.clone(), p2.clone()];
            enumerate_outputs_and_masks(&inputs, &sweep);
        }
    });

    let final_count = sweep.counter.load(Ordering::Relaxed);
    eprintln!(
        "[done] {final_count} / {total} cases in {} (n=2 alone: {})",
        fmt_secs(sweep.start.elapsed().as_secs_f64()),
        final_count - after_n1,
    );
    assert_eq!(final_count, total, "enumeration count diverged from precomputed total");
}
