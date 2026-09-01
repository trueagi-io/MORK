//! Cross-check `mork_expr::unifiable_reuse_state` against the checked-in Prolog oracle.
//!
//! `unify_with_mork_unifier` in this crate runs every axiom against every other and writes the
//! result per axiom, which is hours of work and needs collating before it can be compared. This
//! binary answers the same question over a bounded slice of left-hand sides, in memory, and diffs
//! against `kernel/resources/big_enumerated_unification_results_oracle.metta` directly -- so a
//! change to the unifier can be cross-checked against an independent implementation in minutes.
//!
//!   cargo run --release -p unification_test_laws --bin oracle_check -- [FIRST_LHS] [LHS_COUNT]
//!
//! Every left-hand side in the slice is unified against ALL 100k right-hand sides, and both
//! directions of disagreement are reported: a pair this unifier accepts and the oracle does not,
//! and a pair the oracle has that this unifier rejects.

use std::collections::HashSet;

fn main() {
    let workspace = std::path::PathBuf::from(env!("CARGO_WORKSPACE_DIR"));
    let axioms_path = workspace.join("kernel/resources/big_enumerated.metta");
    let oracle_path =
        workspace.join("kernel/resources/big_enumerated_unification_results_oracle.metta");

    let args: Vec<String> = std::env::args().collect();
    let first: usize = args.get(1).map_or(0, |s| s.parse().expect("FIRST_LHS"));
    let count: usize = args.get(2).map_or(64, |s| s.parse().expect("LHS_COUNT"));

    // Parse the axioms exactly as `unify_with_mork_unifier` does: one expression per line, all in
    // one block, with the `(line N <axiom>)` wrapper stripped by pointing past its header.
    let mut space = mork::space::Space::new();
    let text = std::fs::read_to_string(&axioms_path).expect("big_enumerated.metta");
    let mut block = Vec::with_capacity(text.len() * 2);
    unsafe { block.set_len(block.capacity()) };
    let mut pos = Vec::new();
    let mut offset = 0usize;
    for line in text.split('\n') {
        if line.is_empty() {
            break;
        }
        pos.push(offset);
        let e = space
            .parse_sexpr(line.as_bytes(), (&mut block[offset..]).as_mut_ptr())
            .expect("axiom parses");
        offset += e.1;
    }
    pos.push(offset);
    let n = pos.len() - 1;

    // `(line N <axiom>)` is `[Arity(3)][Sym(4)]line[Sym(k)]<digits><axiom>`, so the axiom starts
    // past the line number and the number itself is the identity the oracle uses.
    let line_and_expr = |nth: usize| -> (usize, mork_expr::Expr) {
        const NUM_TAG_POS: usize = 6;
        let e = mork_expr::Expr {
            ptr: block[pos[nth]..pos[nth + 1]].as_ptr().cast_mut(),
        };
        let span = unsafe { e.span().as_ref() }.unwrap();
        let mork_expr::Tag::SymbolSize(k) = mork_expr::byte_item(span[NUM_TAG_POS]) else {
            panic!("line number must be a symbol")
        };
        let digits = &span[NUM_TAG_POS + 1..NUM_TAG_POS + 1 + k as usize];
        let id = std::str::from_utf8(digits).unwrap().parse().unwrap();
        let axiom = mork_expr::Expr {
            ptr: unsafe { e.ptr.add(NUM_TAG_POS + 1 + k as usize) },
        };
        (id, axiom)
    };

    let last = (first + count).min(n);
    println!("axioms {n}, checking left-hand sides {first}..{last} against all {n}");

    // The oracle, restricted to the slice under test.
    let mut expected: HashSet<(usize, usize)> = HashSet::new();
    let oracle = std::fs::read_to_string(&oracle_path).expect("oracle");
    for line in oracle.lines() {
        let body = line.trim();
        let Some(rest) = body.strip_prefix("(unifies ") else { continue };
        let rest = rest.trim_end_matches(')');
        let mut it = rest.split_whitespace();
        let (Some(l), Some(r)) = (it.next(), it.next()) else { continue };
        let (l, r): (usize, usize) = (l.parse().unwrap(), r.parse().unwrap());
        if l >= first && l < last {
            expected.insert((l, r));
        }
    }
    println!("oracle pairs for this slice: {}", expected.len());

    let mut stack: Vec<(u8, u8)> = Vec::new();
    let mut assignments: Vec<(u8, u8)> = Vec::new();
    let mut envs: Vec<(mork_expr::ExprEnv, mork_expr::ExprEnv)> = Vec::new();

    let mut got: HashSet<(usize, usize)> = HashSet::new();
    let mut checked = 0usize;
    for li in first..last {
        let (l_id, l_expr) = line_and_expr(li);
        for ri in 0..n {
            let (r_id, r_expr) = line_and_expr(ri);
            checked += 1;
            if mork_expr::unifiable_reuse_state(
                l_expr,
                r_expr,
                &mut envs,
                &mut stack,
                &mut assignments,
            ) {
                got.insert((l_id, r_id));
            }
        }
    }

    let false_positive: Vec<_> = got.difference(&expected).take(20).collect();
    let false_negative: Vec<_> = expected.difference(&got).take(20).collect();
    println!(
        "pairs unified: {} checked, {} accepted (oracle {})",
        checked,
        got.len(),
        expected.len()
    );
    if false_positive.is_empty() && false_negative.is_empty() {
        println!("AGREES with the oracle on every pair in the slice");
    } else {
        println!("DISAGREES: {} accepted-not-in-oracle, {} in-oracle-not-accepted",
                 got.difference(&expected).count(), expected.difference(&got).count());
        for p in false_positive {
            println!("  accepted but oracle says no: {p:?}");
        }
        for p in false_negative {
            println!("  oracle says yes but rejected: {p:?}");
        }
        std::process::exit(1);
    }
}
