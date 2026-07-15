//! Data-parallel ground join over MORK's live PathMap.
//!
//! `ground_join` walks the byte-trie variable-at-a-time with one held `SubtermCursor` per factor,
//! descending and ascending it in place as columns bind and backtrack (it never re-opens a zipper
//! from the trie root, the dominant cost of a naive per-column re-descend). `ground_join_parallel`
//! partitions the leading variable's domain across worker threads by hash, each running the join on
//! the shared read-only map into its own answer buffer, then concatenates. The workers' answer sets
//! partition the whole, so the parallel result equals the sequential one (asserted here and by
//! `ground_join_parallel_matches_sequential`).
//!
//!   RUSTFLAGS="-C target-cpu=native" cargo +nightly run -p mork --release --example ground_join_parallel

use mork::space::Space;
use mork::zipper_join::{ground_join, ground_join_parallel, parse_body_factors};
use std::time::Instant;

/// Encode a conjunction body with MORK's own parser: insert `(, p1 p2 ..)` and read the key back.
fn encode_body(patterns: &[&str]) -> Vec<u8> {
    use pathmap::zipper::{ZipperIteration, ZipperMoving};
    let mut s = Space::new();
    s.add_all_sexpr(format!("(, {})", patterns.join(" ")).as_bytes())
        .unwrap();
    let mut rz = s.btm.read_zipper();
    rz.to_next_val();
    rz.path().to_vec()
}

fn main() {
    // A deterministic directed graph (xorshift, no rng dependency), dense enough that the two-hop
    // join produces millions of answers.
    let nodes: u64 = 3000;
    let n_edges: usize = 150_000;
    let mut st: u64 = 0x9E3779B97F4A7C15;
    let mut next = move || {
        st ^= st << 13;
        st ^= st >> 7;
        st ^= st << 17;
        st
    };
    let mut prog = String::with_capacity(n_edges * 12);
    for _ in 0..n_edges {
        let a = next() % nodes;
        let b = next() % nodes;
        prog.push_str(&format!("(edge {} {})\n", a, b));
    }
    let mut s = Space::new();
    s.add_all_sexpr(prog.as_bytes()).unwrap();
    println!("graph: {} nodes, {} distinct edges", nodes, s.btm.val_count());

    // (, (edge $x $y) (edge $y $z)): trans(x, z) two-hop.
    let body = encode_body(&["(edge $x $y)", "(edge $y $z)"]);
    let (factors, nvars) = parse_body_factors(&body).expect("body parses to ground-join factors");
    let var_order: Vec<usize> = (0..nvars).collect();

    let t = Instant::now();
    let seq = ground_join(&s.btm, &factors, &var_order, nvars);
    let seq_ms = t.elapsed().as_millis();
    println!("sequential ground_join: {} answers in {} ms", seq.len(), seq_ms);

    for nt in [4usize, 8, 16, 32] {
        let t = Instant::now();
        let par = ground_join_parallel(&s.btm, &factors, &var_order, nvars, nt);
        let par_ms = t.elapsed().as_millis();
        assert_eq!(par.len(), seq.len(), "parallel answer count must equal sequential");
        println!(
            "parallel x{:<2} ground_join: {} answers in {} ms  ({:.1}x)",
            nt,
            par.len(),
            par_ms,
            seq_ms as f64 / par_ms.max(1) as f64
        );
    }
}
