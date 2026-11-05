// Purpose: hold the planner to the one property that makes reordering legal -- the answer set
//   of a conjunctive body does not depend on the order its conjuncts were written in.
// Assumes: the space-to-space transform dispatches to `Space::query_multi_planned`, so a rule
//   written here is answered by the planned descent whenever `conjunct_order` accepts a plan.
// Guarantees: each test states, and asserts, whether the body it uses is one the planner
//   actually reorders, so none of them can pass by the planner declining.
// Fails when: nothing here reaches the planned descent. Under the `leapfrog` feature these
//   bodies are answered by that join instead, so the tests still hold -- the answer set is the
//   same either way -- but they are then checking the other engine.
// Decides: the graph these use is 40 vertices and 300 edges, big enough that the planner
//   accepts rather than declining on cost, and small enough to run in milliseconds.

// The planner is a feature; so is its test file. `no_search` is excluded because it replaces
// the searching descent with an enumerate-and-unify reference engine, which these programs'
// 300-edge relation is far too large for: `origin/main` built with that feature does not finish
// `differential/corpus/programs/plan_root_triangle.mm2` either.
#![cfg(all(feature = "conjunct_order", not(feature = "no_search")))]

use mork::conjunct_order::plan_cached;
use mork::expr;
use mork::space::{transitions, Space};
use std::collections::BTreeSet;

/// Answers produced and trie transitions walked by one descent. `transitions` is the engine's
/// own diagnostic counter, so this measures search rather than wall-clock and does not move
/// with the machine.
fn descend(run: impl FnOnce() -> usize) -> (usize, usize) {
    let before = unsafe { transitions };
    let answers = run();
    (answers, unsafe { transitions } - before)
}

/// The graph `bench clique` builds, scaled down: `nnodes` vertices and `nedges` distinct
/// undirected edges written as ordered pairs, from a fixed seed so the corpus is stable.
fn graph_edges(nnodes: u64, nedges: usize) -> Vec<(u64, u64)> {
    let mut edges = BTreeSet::new();
    // A linear congruential generator, spelled out so the graph does not depend on which
    // `rand` version is in the lockfile.
    let mut state = 0x2545_f491_4f6c_dd1du64;
    let mut next = || {
        state = state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        (state >> 33) % nnodes
    };
    while edges.len() < nedges {
        let (i, j) = (next(), next());
        if i != j {
            edges.insert((i.min(j), i.max(j)));
        }
    }
    edges.into_iter().collect()
}

fn edge_facts(nnodes: u64, nedges: usize) -> String {
    graph_edges(nnodes, nedges)
        .into_iter()
        .map(|(i, j)| format!("(edge n{i} n{j})\n"))
        .collect()
}

fn dump(space: &Space, pattern: mork_expr::Expr, template: mork_expr::Expr) -> BTreeSet<String> {
    let mut out = Vec::new();
    space.dump_sexpr(pattern, template, &mut out);
    String::from_utf8(out).unwrap().lines().map(str::to_owned).collect()
}

/// Whether `body` -- the `(, ...)` of an exec rule, written as MeTTa -- is one the planner
/// reorders against `space`. Every test that means to exercise a reorder asserts this, so a
/// change that makes the planner decline shows up as a failing test rather than as coverage
/// quietly disappearing.
fn is_reordered(space: &mut Space, body: &str) -> bool {
    plan_cached(&space.btm, expr!(space, body)).is_some()
}

#[test]
fn the_answer_set_does_not_depend_on_the_written_order() {
    // Four conjuncts over one 300-edge relation and one 3-row table. Written table-last the
    // descent enumerates every triangle before testing which vertex is a root; written
    // table-first it enumerates three. The two must still agree on every answer.
    let mut space = Space::new();
    let mut program = edge_facts(40, 300);
    program.push_str("(root n0)\n(root n1)\n(root n2)\n");

    let factors = ["(edge $x $y)", "(edge $y $z)", "(root $x)", "(edge $x $z)"];
    let orders = [
        ("Tabcd", [0, 1, 2, 3]),
        ("Tcabd", [2, 0, 1, 3]),
        ("Tdcba", [3, 2, 1, 0]),
        ("Tbdac", [1, 3, 0, 2]),
    ];
    for (relation, order) in orders {
        program.push_str(&format!(
            "(exec {relation} (, {} {} {} {}) (, ({relation} $x $y $z)))\n",
            factors[order[0]], factors[order[1]], factors[order[2]], factors[order[3]]
        ));
    }
    space.add_all_sexpr(program.as_bytes()).unwrap();

    assert!(
        is_reordered(&mut space, "[5] , [3] edge $ $ [3] edge _2 $ [2] root _1 [3] edge _1 _3"),
        "the written-order-first arrangement must be one the planner reorders, or this test \
         proves nothing about reordering"
    );

    assert_eq!(space.metta_calculus(orders.len()), orders.len());

    let tuples = |space: &Space, relation: &str| -> BTreeSet<String> {
        dump(
            space,
            expr!(space, format!("[4] {relation} $ $ $").as_str()),
            expr!(space, format!("[4] {relation} _1 _2 _3").as_str()),
        )
        .into_iter()
        .map(|line| line[relation.len() + 2..line.len() - 1].to_owned())
        .collect()
    };

    let first = tuples(&space, orders[0].0);
    assert!(!first.is_empty(), "the body must have answers for this to test anything");
    for (relation, _) in &orders[1..] {
        assert_eq!(tuples(&space, relation), first, "{relation} disagreed with {}", orders[0].0);
    }
}

#[test]
fn a_reordered_descent_keeps_coreferent_variables_coreferent() {
    // The reorder renumbers each factor's variables to the planned order. A variable shared by
    // the first and last conjunct is the case that renumbering can get wrong: after the move
    // the sharing has to run backwards, from the later factor to the earlier one.
    let mut space = Space::new();
    let mut program = edge_facts(40, 300);
    program.push_str("(root n0)\n(root n1)\n(root n2)\n");
    program.push_str("(exec R (, (edge $x $y) (edge $y $z) (root $x) (edge $x $z)) (, (R $x $y $z)))\n");
    space.add_all_sexpr(program.as_bytes()).unwrap();

    let body = "[5] , [3] edge $ $ [3] edge _2 $ [2] root _1 [3] edge _1 _3";
    assert!(is_reordered(&mut space, body), "this body must be reordered");
    assert_eq!(space.metta_calculus(1), 1);

    let answers = dump(&space, expr!(space, "[4] R $ $ $"), expr!(space, "[4] R _1 _2 _3"));
    assert!(!answers.is_empty());

    // The graph is written as ordered pairs, so `(edge $x $y)` matches one direction only and
    // an answer's three edges must each be present exactly as stored.
    let edges: BTreeSet<(u64, u64)> = graph_edges(40, 300).into_iter().collect();
    let vertex = |s: &str| s.trim_start_matches('n').parse::<u64>().unwrap();
    for answer in &answers {
        let parts: Vec<&str> = answer[3..answer.len() - 1].split(' ').collect();
        let (x, y, z) = (vertex(parts[0]), vertex(parts[1]), vertex(parts[2]));
        assert!(x < 3, "{answer}: $x must be a root");
        for pair in [(x, y), (y, z), (x, z)] {
            assert!(edges.contains(&pair), "{answer}: {pair:?} is not a stored edge");
        }
    }

    // Every such triangle, computed here rather than taken from the engine.
    let mut expected = BTreeSet::new();
    for &(x, y) in &edges {
        if x >= 3 {
            continue;
        }
        for z in 0..40 {
            if edges.contains(&(y, z)) && edges.contains(&(x, z)) {
                expected.insert(format!("(R n{x} n{y} n{z})"));
            }
        }
    }
    assert_eq!(answers, expected);
}

#[test]
fn a_relation_holding_variables_does_not_mislead_the_planner() {
    // A stored variable unifies with every value. `(root $r)` therefore binds `$x` to a
    // VARIABLE once, and the `(edge $x $y)` that follows has nothing to seek on and scans the
    // whole relation for that one binding. A cost model that reads a bound column as seekable
    // regardless of what it holds prices that step at one row-range and takes the order, which
    // it should not: measured against the written order this body walked 27x more transitions
    // at 300 edges and 463x more at 4,800, so the loss GREW with the input rather than
    // settling. The two sizes below are what makes this a test of that growth and not of one
    // constant.
    for (nnodes, nedges) in [(40u64, 300usize), (160, 1200)] {
        let mut space = Space::new();
        let mut program = edge_facts(nnodes, nedges);
        program.push_str("(root n0)\n(root n1)\n(root n2)\n");
        program.push_str("(root $r)\n");
        space.add_all_sexpr(program.as_bytes()).unwrap();

        let body = expr!(space, "[5] , [3] edge $ $ [3] edge _2 $ [2] root _1 [3] edge _1 _3");
        assert!(
            plan_cached(&space.btm, body).is_some(),
            "{nedges} edges: the planner must accept this body, or the assertions below hold \
             vacuously"
        );

        let (written_answers, written) = descend(|| Space::query_multi(&space.btm, body, |_, _| true));
        let (planned_answers, planned) =
            descend(|| Space::query_multi_planned(&space.btm, body, |_, _| true));

        assert_eq!(
            planned_answers, written_answers,
            "{nedges} edges: reordering changed how many candidates the descent produced"
        );
        assert!(
            planned <= written * 2,
            "{nedges} edges: the planned order walked {planned} transitions against the written \
             order's {written}. A body the planner ACCEPTS may lose a little to estimation \
             error, never a factor."
        );
    }
}

#[test]
fn a_body_the_planner_declines_is_answered_exactly_as_before() {
    // The other half of the contract: most bodies are refused, and a refusal must leave the
    // descent doing what it always did. This one is three tiny relations, far below the cost
    // at which planning could repay itself.
    let mut space = Space::new();
    space
        .add_all_sexpr(
            br#"
(A a)
(A b)
(B c)
(C a)
(C c)

(exec 0 (, (A $x) (B $y) (C $x)) (, (R $x $y)))
"#,
        )
        .unwrap();
    assert!(
        !is_reordered(&mut space, "[4] , [2] A $ [2] B $ [2] C _1"),
        "a body this small must be refused"
    );
    assert_eq!(space.metta_calculus(1), 1);

    let answers = dump(&space, expr!(space, "[3] R $ $"), expr!(space, "[3] R _1 _2"));
    assert_eq!(answers, BTreeSet::from(["(R a c)".to_owned()]));
}
