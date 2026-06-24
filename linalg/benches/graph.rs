//! Graph connectivity / matrix-power benchmarks for [`Csr`].
//!
//! Ported from the sparse-linear-algebra-tests repo's `long-tests` benches:
//!   1. `bench_repeated_exponentiation` — A^k = A^(k-1) × A step by step,
//!      sequential vs parallel SpGEMM (magnus comparison dropped).
//!   2. `bench_lattice_3d_power_until_stable` — transitive closure of A + I
//!      by repeated squaring until the sparsity pattern stabilises; component
//!      count cross-checked against union-find `connected_components`.
//!   3. `bench_diameter` — graph diameter via repeated squaring (upper bound)
//!      plus linear refinement (exact), verified on Moore lattices where the
//!      diameter is known to be `side - 1`.
//!   4./5. `bench_diameter` / `bench_real_graphs` on real edge lists.
//!
//! Run with `cargo bench --bench graph`.
//!
//! Environment:
//!   GRAPH_BENCH_LARGE=1   include the bigger lattice configurations (slow,
//!                         the closure of a connected 8000-node graph is dense)
//!   GRAPH_EDGES_DIR=path  directory containing {cora,nell,ogbn_arxiv}.edges
//!                         ("<int> <int>" per line) for the real-graph sections

use std::time::Instant;

use linalg::csr::Csr;

type M = Csr<u32, u32>;

// ─── helpers ────────────────────────────────────────────────────────────

fn xorshift(seed: u64) -> impl FnMut() -> u64 {
    let mut x = seed.max(1);
    move || {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        x
    }
}

#[cfg(feature = "rayon")]
fn mul(a: &M, b: &M, par: bool) -> M {
    if par { a.matmul_par(b) } else { a.matmul(b) }
}

#[cfg(not(feature = "rayon"))]
fn mul(a: &M, b: &M, _par: bool) -> M {
    a.matmul(b)
}

/// 3D Moore-neighbourhood lattice with side `s`, optionally periodic,
/// randomly thinned to roughly `target_epn` directed edges per node.
/// Thinning is decided once per undirected pair so the result stays
/// symmetric (required for the connectivity sections).
fn lattice_csr(s: usize, target_epn: f64, torus: bool, seed: u64) -> M {
    let n = s * s * s;
    let keep_p = (target_epn / 26.0).clamp(0.0, 1.0);
    let mut rng = xorshift(seed);
    let mut triplets: Vec<(u32, u32, u32)> = Vec::new();

    for node in 0..n {
        let (x, y, z) = (
            (node / (s * s)) as i32,
            ((node / s) % s) as i32,
            (node % s) as i32,
        );
        for dx in -1i32..=1 {
            for dy in -1i32..=1 {
                for dz in -1i32..=1 {
                    if dx == 0 && dy == 0 && dz == 0 {
                        continue;
                    }
                    let (nx, ny, nz) = (x + dx, y + dy, z + dz);
                    let (nx, ny, nz) = if torus {
                        (
                            nx.rem_euclid(s as i32),
                            ny.rem_euclid(s as i32),
                            nz.rem_euclid(s as i32),
                        )
                    } else {
                        if nx < 0
                            || nx >= s as i32
                            || ny < 0
                            || ny >= s as i32
                            || nz < 0
                            || nz >= s as i32
                        {
                            continue;
                        }
                        (nx, ny, nz)
                    };
                    let neighbour = (nx as usize) * s * s + (ny as usize) * s + nz as usize;
                    // Each undirected pair is visited from both endpoints;
                    // decide it once, from the smaller one.
                    if neighbour <= node {
                        continue;
                    }
                    if (rng() as f64 / u64::MAX as f64) < keep_p {
                        triplets.push((node as u32, neighbour as u32, 1));
                        triplets.push((neighbour as u32, node as u32, 1));
                    }
                }
            }
        }
    }

    Csr::from_coo(n as u32, &mut triplets)
}

fn same_pattern(a: &M, b: &M) -> bool {
    a.nnz() == b.nnz() && a.row_ptr == b.row_ptr && a.col_idx == b.col_idx
}

/// Repeated squaring A, A², A⁴, … until the sparsity pattern stabilises.
/// Returns the closure and the number of squarings (including the one that
/// detected stability).
fn power_until_stable(a: &M, par: bool) -> (M, usize) {
    let mut current = a.clone();
    let mut k = 0usize;
    loop {
        let next = mul(&current, &current, par);
        k += 1;
        if same_pattern(&next, &current) {
            return (next, k);
        }
        current = next;
    }
}

/// Count components from a symmetric reflexive closure: each row lists its
/// whole component, so the first (minimum) column is a canonical
/// representative.
fn closure_components(closure: &M) -> usize {
    let n = closure.n_rows();
    let mut is_rep = vec![false; n];
    for r in 0..n {
        let start = closure.row_ptr[r];
        is_rep[closure.col_idx[start] as usize] = true;
    }
    is_rep.iter().filter(|&&b| b).count()
}

/// Diameter of an undirected graph (max eccentricity within components):
/// phase 1 squares R₀ = A + I until the pattern stabilises, bracketing the
/// diameter in (reach/2, reach]; phase 2 refines linearly from the last
/// pre-stable power. Returns the exact diameter.
fn diameter_squaring(name: &str, a_sym: &M) -> usize {
    let n = a_sym.n_rows();
    let r0 = a_sym.add(&M::identity(n as u32));
    println!("\n[{name}] n={n}, undirected nnz={}", a_sym.nnz());

    let mut current = r0.clone();
    let mut reach = 1usize; // current covers distances ≤ reach
    let mut prev_saved = r0.clone(); // last power before stabilisation
    let mut prev_reach = 0usize;
    let mut squarings = 0usize;

    loop {
        let t0 = Instant::now();
        let next = mul(&current, &current, true);
        let t_ms = t0.elapsed().as_millis();
        squarings += 1;
        let new_reach = reach * 2;
        println!(
            "  squaring {squarings}: reach ≤{new_reach}, nnz={}, {t_ms} ms",
            next.nnz()
        );
        if same_pattern(&next, &current) {
            println!("  stabilised: diameter ∈ ({prev_reach}, {reach}]");
            break;
        }
        prev_saved = std::mem::replace(&mut current, next);
        prev_reach = reach;
        reach = new_reach;
    }

    if prev_reach == 0 {
        // Stabilised on the very first squaring: R₀ was already the closure.
        println!("  diameter = 1 (or 0 if edgeless)");
        return 1;
    }

    let mut refine = prev_saved;
    let mut d = prev_reach;
    loop {
        let t0 = Instant::now();
        let next = mul(&refine, &r0, true);
        let t_ms = t0.elapsed().as_millis();
        d += 1;
        println!("  refine d={d}: nnz={}, {t_ms} ms", next.nnz());
        if same_pattern(&next, &refine) {
            let diam = d - 1;
            println!("  diameter = {diam}");
            return diam;
        }
        refine = next;
    }
}

/// Load directed edges from a file with "<int> <int>" per line.
/// Returns (n, edges) where n = max node id + 1, or None if unreadable.
fn load_edges(path: &str) -> Option<(u32, Vec<(u32, u32)>)> {
    let contents = std::fs::read_to_string(path).ok()?;
    let mut edges = Vec::new();
    let mut max_id = 0u32;
    for line in contents.lines() {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        let mut parts = line.split_whitespace();
        let a: u32 = parts.next()?.parse().ok()?;
        let b: u32 = parts.next()?.parse().ok()?;
        max_id = max_id.max(a).max(b);
        edges.push((a, b));
    }
    Some((max_id + 1, edges))
}

fn from_edges_undirected(n: u32, edges: &[(u32, u32)]) -> M {
    let mut triplets: Vec<(u32, u32, u32)> = Vec::with_capacity(edges.len() * 2);
    for &(a, b) in edges {
        triplets.push((a, b, 1));
        if a != b {
            triplets.push((b, a, 1));
        }
    }
    Csr::from_coo(n, &mut triplets)
}

// ─── 1. Repeated exponentiation ─────────────────────────────────────────

fn section_repeated_exponentiation(large: bool) {
    let s = if large { 30 } else { 20 };
    const TARGET_EPN: f64 = 3.0;
    const MAX_STEP: usize = 7;
    const ITERS: u32 = 3;

    let a = lattice_csr(s, TARGET_EPN, true, 42);
    let n = s * s * s;
    let epn = a.nnz() as f64 / n as f64;

    println!("\n=== 1. Repeated exponentiation: A^k = A^(k-1) × A ===");
    println!("({s}×{s}×{s} torus, n={n}, {epn:.1} e/n, nnz={})", a.nnz());
    println!("step,nnz,seq_us,par_us,speedup");

    let mut prev = a.clone();
    for step in 2..=MAX_STEP {
        // Warmup + seq/par cross-check
        let r_seq = prev.matmul(&a);
        let r_par = mul(&prev, &a, true);
        assert_eq!(r_seq.nnz(), r_par.nnz(), "step {step}: seq vs par nnz");

        let t0 = Instant::now();
        for _ in 0..ITERS {
            std::hint::black_box(prev.matmul(&a));
        }
        let t_seq = t0.elapsed().as_micros() / ITERS as u128;

        let t0 = Instant::now();
        for _ in 0..ITERS {
            std::hint::black_box(mul(&prev, &a, true));
        }
        let t_par = t0.elapsed().as_micros() / ITERS as u128;

        let speedup = if t_par > 0 {
            t_seq as f64 / t_par as f64
        } else {
            f64::INFINITY
        };
        println!("{step},{},{t_seq},{t_par},{speedup:.2}", r_seq.nnz());
        prev = r_seq;
    }
}

// ─── 2. Connectivity via power-until-stable vs union-find ──────────────

fn section_power_until_stable(large: bool) {
    let sides: &[usize] = if large { &[5, 10, 20] } else { &[5, 10] };
    let epns = [1.0, 2.0, 4.0, 8.0, 13.0, 26.0];

    println!("\n=== 2. Connectivity: closure by repeated squaring vs union-find ===");
    println!("side,n,e_per_n,nnz,components,squarings,closure_nnz,power_ms,uf_us");

    for &s in sides {
        for (i, &epn) in epns.iter().enumerate() {
            let m = lattice_csr(s, epn, true, 1000 + i as u64);
            let n = s * s * s;
            let actual_epn = m.nnz() as f64 / n as f64;
            let with_id = m.add(&M::identity(n as u32));

            let t0 = Instant::now();
            let (closure, squarings) = power_until_stable(&with_id, true);
            let power_ms = t0.elapsed().as_millis();
            let comp_closure = closure_components(&closure);

            let t0 = Instant::now();
            let comp_uf = m.connected_components();
            let uf_us = t0.elapsed().as_micros();
            let n_comp_uf = comp_uf.iter().copied().max().map_or(0, |x| x + 1);

            assert_eq!(
                comp_closure, n_comp_uf,
                "side {s} epn {epn}: closure vs union-find component count"
            );

            println!(
                "{s},{n},{actual_epn:.1},{},{comp_closure},{squarings},{},{power_ms},{uf_us}",
                m.nnz(),
                closure.nnz()
            );
        }
    }
}

// ─── 3. Diameter via repeated squaring (lattices) ──────────────────────

fn section_diameter_lattice(large: bool) {
    println!("\n=== 3. Diameter via repeated squaring + refinement (Moore lattice) ===");
    let sides: &[usize] = if large { &[6, 10, 16] } else { &[6, 10] };
    for &s in sides {
        // Full Moore neighbourhood, no wraparound: diameter = side - 1
        // (Chebyshev distance between opposite corners).
        let a = lattice_csr(s, 26.0, false, 7);
        let d = diameter_squaring(&format!("lattice {s}^3"), &a);
        assert_eq!(d, s - 1, "Moore lattice {s}^3 diameter should be side-1");
    }
}

// ─── 4./5. Real graphs (optional, GRAPH_EDGES_DIR) ─────────────────────

fn section_diameter_real(dir: &str, large: bool) {
    println!("\n=== 4. Diameter via repeated squaring (real graphs) ===");
    // The closure of a connected graph is dense (n² entries, 8 bytes each)
    // and the squaring loop holds ~3 copies — skip graphs that would not fit.
    let budget: usize = if large { 64 << 30 } else { 8 << 30 };
    for name in ["cora", "nell", "ogbn_arxiv"] {
        let path = format!("{dir}/{name}.edges");
        let Some((n, edges)) = load_edges(&path) else {
            println!("  (skipping {path}: not readable)");
            continue;
        };
        let projected = 3 * (n as usize) * (n as usize) * 8;
        if projected > budget {
            println!(
                "  (skipping {name}: n={n}, dense closure needs ~{} GB > {} GB budget)",
                projected >> 30,
                budget >> 30
            );
            continue;
        }
        // Undirected + self-loops: R₀[i][j] > 0 ⟺ dist(i,j) ≤ 1
        let a_sym = from_edges_undirected(n, &edges);
        diameter_squaring(name, &a_sym);
    }
}

fn section_real_graph_powers(dir: &str, large: bool) {
    const MAX_POWER: usize = 14;
    let max_nnz: usize = if large { 2_000_000_000 } else { 200_000_000 };

    println!("\n=== 5. Matrix powers on real graphs ===");
    println!("graph,n,edges,step,nnz_out,mul_us");

    for name in ["cora", "nell", "ogbn_arxiv"] {
        let path = format!("{dir}/{name}.edges");
        let Some((n, edges)) = load_edges(&path) else {
            println!("  (skipping {path}: not readable)");
            continue;
        };
        let a = M::from_edges(n, &edges);
        let mut prev = a.clone();

        for step in 2..=MAX_POWER {
            let t0 = Instant::now();
            let result = mul(&prev, &a, true);
            let t_us = t0.elapsed().as_micros();
            let nnz_out = result.nnz();
            println!("{name},{n},{},{step},{nnz_out},{t_us}", edges.len());
            prev = result;
            if nnz_out > max_nnz {
                println!("  (stopped: nnz > {max_nnz})");
                break;
            }
        }
    }
}

// ─── main ───────────────────────────────────────────────────────────────

fn main() {
    let large = std::env::var("GRAPH_BENCH_LARGE").is_ok_and(|v| !v.is_empty() && v != "0");
    let edges_dir = std::env::var("GRAPH_EDGES_DIR").ok();

    println!("=== linalg graph bench (connectivity / matrix powers) ===");
    #[cfg(feature = "rayon")]
    println!("(rayon enabled: par columns use matmul_par)");
    #[cfg(not(feature = "rayon"))]
    println!("(rayon disabled: par columns fall back to sequential matmul)");
    if large {
        println!("(GRAPH_BENCH_LARGE set: including big configurations)");
    }

    section_repeated_exponentiation(large);
    section_power_until_stable(large);
    section_diameter_lattice(large);

    if let Some(dir) = &edges_dir {
        section_diameter_real(dir, large);
        section_real_graph_powers(dir, large);
    } else {
        println!(
            "\n(set GRAPH_EDGES_DIR=<dir with cora.edges/nell.edges/ogbn_arxiv.edges> \
             for the real-graph sections)"
        );
    }

    println!("\n=== done ===");
}
