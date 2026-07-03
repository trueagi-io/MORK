//! Generalized hypertree decomposition (GHD) planner for the worst-case-optimal join.
//!
//! The WCO leapfrog join (`zipper_join`) runs a whole conjunction as one global
//! variable-at-a-time join in `O(N^rho*)` time, `rho*` the fractional edge-cover number.
//! For a *cyclic* body a hypertree decomposition does better: split the body into a tree of
//! small BAGS, materialize each bag with the WCO join, and run Yannakakis over the bags in
//! `O(N^fhtw + OUT)`, and `fhtw <= rho*`. The 4-cycle is the witness: `rho* = 2` (one global
//! WCO join is `O(N^2)`) but a width-2 decomposition into two 2-paths is `O(N^{3/2})`. Acyclic
//! bodies are already output-optimal under the WCO join, so the win is exactly the cyclic case.
//!
//! This module is the PLANNER: the query hypergraph (factors = hyperedges over the body's
//! variables), GYO alpha-acyclicity + join tree, and a minimum-width decomposition search.
//! Soundness is machine-checked in Alloy (`scratchpad/fac14_ghd.als`, Model 14): under the
//! cover condition every factor sits in some bag, so the join of the bags equals the join of
//! all factors. Evaluation (materialize bags via the WCO join, Yannakakis over them) lives
//! separately; this file is pure planning and is unit-tested on the hypergraph in isolation.

use crate::zipper_join::{
    collect_factor_vars, first_subterm_len, run_unify_join_stream, Factor, FactorColumn,
};
use pathmap::PathMap;
use std::collections::{BTreeMap, BTreeSet};

/// The query hypergraph: per factor, the set of body variables it constrains (its hyperedge).
pub fn hypergraph(factors: &[Factor]) -> Vec<BTreeSet<usize>> {
    factors
        .iter()
        .map(|f| {
            let mut s = BTreeSet::new();
            collect_factor_vars(f, &mut s);
            s
        })
        .collect()
}

/// A bag of a decomposition: the factor indices it covers and the variables they span.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Bag {
    pub factors: Vec<usize>,
    pub vars: BTreeSet<usize>,
}

/// A generalized hypertree decomposition: bags plus a join tree over them. `width` is the
/// largest number of factors in any bag (the hypertree width).
#[derive(Clone, Debug)]
pub struct Ghd {
    pub bags: Vec<Bag>,
    /// `parent[i]` is bag `i`'s parent in the join tree, or `None` for the root.
    pub parent: Vec<Option<usize>>,
    pub width: usize,
}

/// GYO ear removal. Returns `Some(parent)` (join-tree parents per edge) iff the hypergraph is
/// alpha-acyclic, else `None`. An ear is an edge whose *shared* vertices (those also in some
/// other live edge) are all contained in one witness edge; remove it with that witness as its
/// parent. A connected acyclic hypergraph reduces to a single surviving root.
pub fn gyo_join_tree(edges: &[BTreeSet<usize>]) -> Option<Vec<Option<usize>>> {
    let n = edges.len();
    if n == 0 {
        return Some(vec![]);
    }
    let mut alive = vec![true; n];
    let mut parent: Vec<Option<usize>> = vec![None; n];
    loop {
        let mut removed_one = false;
        'scan: for i in 0..n {
            if !alive[i] {
                continue;
            }
            // shared vertices of edge i: those appearing in some other live edge.
            let shared: BTreeSet<usize> = edges[i]
                .iter()
                .cloned()
                .filter(|v| (0..n).any(|j| j != i && alive[j] && edges[j].contains(v)))
                .collect();
            if shared.is_empty() {
                continue; // isolated, or the last edge of its component: a root, not an ear.
            }
            // witness: another live edge containing all of edge i's shared vertices.
            for j in 0..n {
                if j != i && alive[j] && shared.iter().all(|v| edges[j].contains(v)) {
                    alive[i] = false;
                    parent[i] = Some(j);
                    removed_one = true;
                    break 'scan; // degrees changed; restart the scan.
                }
            }
        }
        if !removed_one {
            break;
        }
    }
    if alive.iter().filter(|&&a| a).count() <= 1 {
        Some(parent)
    } else {
        None
    }
}

/// The union of variables of a set of factors (a bag's variable set).
fn bag_vars(edges: &[BTreeSet<usize>], factors: &[usize]) -> BTreeSet<usize> {
    let mut v = BTreeSet::new();
    for &f in factors {
        v.extend(edges[f].iter().cloned());
    }
    v
}

/// Find a minimum-width GHD of the body. An alpha-acyclic body gets width 1 (each factor its
/// own bag, along the GYO join tree). A cyclic body searches partitions of the factors into
/// blocks of size `<= k` for increasing `k`, taking the smallest `k` whose block var-sets are
/// alpha-acyclic (so Yannakakis applies over the bags). `k_max` caps the search; `None` means
/// no low-width decomposition was found and the caller keeps the global WCO join.
pub fn decompose(edges: &[BTreeSet<usize>], k_max: usize) -> Option<Ghd> {
    let n = edges.len();
    if n == 0 {
        return None;
    }
    // width 1: alpha-acyclic body, each factor its own bag.
    if let Some(parent) = gyo_join_tree(edges) {
        let bags = (0..n)
            .map(|i| Bag {
                factors: vec![i],
                vars: edges[i].clone(),
            })
            .collect();
        return Some(Ghd {
            bags,
            parent,
            width: 1,
        });
    }
    // width >= 2: smallest block size whose bag-query is acyclic.
    for k in 2..=k_max.min(n) {
        if let Some(ghd) = search_partition(edges, k) {
            return Some(ghd);
        }
    }
    None
}

/// Search partitions of the factors into blocks of size `<= k` whose bag var-sets are
/// alpha-acyclic; return the minimum-width such decomposition, if any.
fn search_partition(edges: &[BTreeSet<usize>], k: usize) -> Option<Ghd> {
    let n = edges.len();
    let mut best: Option<Ghd> = None;
    let mut blocks: Vec<Vec<usize>> = Vec::new();
    partition_rec(edges, k, 0, n, &mut blocks, &mut best);
    best
}

fn partition_rec(
    edges: &[BTreeSet<usize>],
    k: usize,
    i: usize,
    n: usize,
    blocks: &mut Vec<Vec<usize>>,
    best: &mut Option<Ghd>,
) {
    if i == n {
        let bag_var_sets: Vec<BTreeSet<usize>> = blocks.iter().map(|b| bag_vars(edges, b)).collect();
        if let Some(parent) = gyo_join_tree(&bag_var_sets) {
            let width = blocks.iter().map(|b| b.len()).max().unwrap_or(1);
            if best.as_ref().map_or(true, |g| width < g.width) {
                let bags = blocks
                    .iter()
                    .zip(bag_var_sets.iter())
                    .map(|(b, v)| Bag {
                        factors: b.clone(),
                        vars: v.clone(),
                    })
                    .collect();
                *best = Some(Ghd {
                    bags,
                    parent,
                    width,
                });
            }
        }
        return;
    }
    for bi in 0..blocks.len() {
        if blocks[bi].len() < k {
            blocks[bi].push(i);
            partition_rec(edges, k, i + 1, n, blocks, best);
            blocks[bi].pop();
        }
    }
    blocks.push(vec![i]);
    partition_rec(edges, k, i + 1, n, blocks, best);
    blocks.pop();
}

// ---- Evaluation: materialize each bag with the WCO join, then join the bags ----

/// One match of a bag: the matched fact bytes for each of the bag's factors (in `bag.factors`
/// order) and the value bound to each of the bag's variables (its join-key material).
#[derive(Clone, Debug)]
pub struct BagMatch {
    pub facts: Vec<Vec<u8>>,
    pub vars: BTreeMap<usize, Vec<u8>>,
}

/// Read the value bound to each top-level `Var` column of `factor` from a matched `fact`. A fact
/// is a full s-expression: `fact[0]` is the arity byte (the factor's seek prefix), then one
/// subterm per column. Coreference is enforced by the join, so a variable's first occurrence
/// carries its value.
fn extract_var_values(fact: &[u8], factor: &Factor, out: &mut BTreeMap<usize, Vec<u8>>) {
    let mut pos = 1; // skip the arity byte
    for col in &factor.cols {
        if pos >= fact.len() {
            break;
        }
        let len = first_subterm_len(&fact[pos..]);
        if let FactorColumn::Var(v) = col {
            out.entry(*v).or_insert_with(|| fact[pos..pos + len].to_vec());
        }
        pos += len;
    }
}

/// Materialize a bag: run the WCO join over the bag's factors and collect, per match, the matched
/// facts and the bag's variable values. Ascending variable order is a valid elimination order
/// because `catch_up` seeks already-bound columns, so a factor whose columns are not in ascending
/// variable order still binds correctly.
pub fn materialize_bag(
    map: &PathMap<()>,
    all_factors: &[Factor],
    bag: &Bag,
    nvars: usize,
) -> Vec<BagMatch> {
    let bag_factors: Vec<Factor> = bag.factors.iter().map(|&i| all_factors[i].clone()).collect();
    let var_order: Vec<usize> = bag.vars.iter().cloned().collect();
    let mut out = Vec::new();
    run_unify_join_stream(map, &bag_factors, &var_order, nvars, &mut |tuple: &[Vec<u8>]| {
        let facts: Vec<Vec<u8>> = tuple.to_vec();
        let mut vars = BTreeMap::new();
        for (k, &fi) in bag.factors.iter().enumerate() {
            extract_var_values(&facts[k], &all_factors[fi], &mut vars);
        }
        out.push(BagMatch { facts, vars });
        true
    });
    out
}

/// Natural-join the materialized bags on their shared variables, producing one full tuple of
/// matched facts per original factor (indexed by original factor id). The bags cover every factor
/// (Model 14), so a completed tuple binds every factor. This first version is a nested-loop join
/// (correct for any order); Yannakakis semijoin reduction over the join tree replaces it for the
/// asymptotic bound.
pub fn join_bags(bags: &[(Bag, Vec<BagMatch>)], n_factors: usize) -> Vec<Vec<Vec<u8>>> {
    let mut acc: Vec<(Vec<Option<Vec<u8>>>, BTreeMap<usize, Vec<u8>>)> =
        vec![(vec![None; n_factors], BTreeMap::new())];
    for (bag, matches) in bags {
        let mut next = Vec::new();
        for (partial_facts, partial_vars) in &acc {
            for m in matches {
                // agree on every already-bound shared variable
                let agree = m
                    .vars
                    .iter()
                    .all(|(v, val)| partial_vars.get(v).map_or(true, |pv| pv == val));
                if !agree {
                    continue;
                }
                let mut facts = partial_facts.clone();
                for (k, &fi) in bag.factors.iter().enumerate() {
                    facts[fi] = Some(m.facts[k].clone());
                }
                let mut vars = partial_vars.clone();
                for (v, val) in &m.vars {
                    vars.insert(*v, val.clone());
                }
                next.push((facts, vars));
            }
        }
        acc = next;
    }
    acc.into_iter()
        .filter_map(|(facts, _)| facts.into_iter().collect::<Option<Vec<Vec<u8>>>>())
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn e(vs: &[usize]) -> BTreeSet<usize> {
        vs.iter().cloned().collect()
    }

    // variables: a=0 b=1 c=2 d=3
    #[test]
    fn chain_is_acyclic_width_1() {
        // R(a,b) S(b,c) T(c,d): a path, alpha-acyclic.
        let edges = vec![e(&[0, 1]), e(&[1, 2]), e(&[2, 3])];
        assert!(gyo_join_tree(&edges).is_some(), "a path must be alpha-acyclic");
        let g = decompose(&edges, 3).expect("chain decomposes");
        assert_eq!(g.width, 1, "acyclic body has hypertree width 1");
        assert_eq!(g.bags.len(), 3);
    }

    #[test]
    fn triangle_is_cyclic_width_2() {
        // R(a,b) S(b,c) T(c,a): the triangle, cyclic, ghw = 2.
        let edges = vec![e(&[0, 1]), e(&[1, 2]), e(&[2, 0])];
        assert!(gyo_join_tree(&edges).is_none(), "the triangle must be cyclic");
        let g = decompose(&edges, 3).expect("triangle decomposes at width 2");
        assert_eq!(g.width, 2, "triangle ghw is 2");
        // cover (Model 14): every factor sits in some bag.
        let covered: BTreeSet<usize> = g.bags.iter().flat_map(|b| b.factors.iter().cloned()).collect();
        assert_eq!(covered, e(&[0, 1, 2]), "every factor must be covered");
    }

    #[test]
    fn four_cycle_is_cyclic_width_2() {
        // R(a,b) S(b,c) T(c,d) U(d,a): the 4-cycle. rho* = 2 (WCO is O(N^2)); a width-2
        // decomposition into two 2-paths evaluates in O(N^{3/2}). This is the GHD win.
        let edges = vec![e(&[0, 1]), e(&[1, 2]), e(&[2, 3]), e(&[3, 0])];
        assert!(gyo_join_tree(&edges).is_none(), "the 4-cycle must be cyclic");
        let g = decompose(&edges, 4).expect("4-cycle decomposes at width 2");
        assert_eq!(g.width, 2, "4-cycle can be covered by width-2 bags");
        // the bag-query is alpha-acyclic (Yannakakis applies over the bags).
        let bag_edges: Vec<BTreeSet<usize>> = g.bags.iter().map(|b| b.vars.clone()).collect();
        assert!(gyo_join_tree(&bag_edges).is_some(), "the bag-query must be acyclic");
        let covered: BTreeSet<usize> = g.bags.iter().flat_map(|b| b.factors.iter().cloned()).collect();
        assert_eq!(covered, e(&[0, 1, 2, 3]), "every factor must be covered");
    }

    #[test]
    fn single_factor_width_1() {
        let edges = vec![e(&[0, 1])];
        let g = decompose(&edges, 3).expect("one factor decomposes");
        assert_eq!(g.width, 1);
        assert_eq!(g.bags.len(), 1);
    }

    fn bm(facts: &[&[u8]], vars: &[(usize, &[u8])]) -> BagMatch {
        BagMatch {
            facts: facts.iter().map(|f| f.to_vec()).collect(),
            vars: vars.iter().map(|(v, b)| (*v, b.to_vec())).collect(),
        }
    }

    #[test]
    fn join_bags_natural_join_on_shared_var() {
        // bag A = factor 0 over vars {0=x, 1=y}; bag B = factor 1 over vars {1=y, 2=z}.
        // They share variable 1 (y): only matches agreeing on y join.
        let bag_a = Bag { factors: vec![0], vars: e(&[0, 1]) };
        let bag_b = Bag { factors: vec![1], vars: e(&[1, 2]) };
        let a = vec![
            bm(&[b"FA0"], &[(0, b"x0"), (1, b"y0")]),
            bm(&[b"FA1"], &[(0, b"x1"), (1, b"y1")]),
        ];
        let b = vec![
            bm(&[b"FB0"], &[(1, b"y0"), (2, b"z0")]),
            bm(&[b"FB9"], &[(1, b"y9"), (2, b"z9")]),
        ];
        let bags = vec![(bag_a, a), (bag_b, b)];
        let full = join_bags(&bags, 2);
        // only (y0) agrees: full tuple is [factor0 = FA0, factor1 = FB0].
        assert_eq!(full, vec![vec![b"FA0".to_vec(), b"FB0".to_vec()]]);
    }

    #[test]
    fn join_bags_places_facts_at_original_factor_ids() {
        // bag covers factors {2, 0} (out of 3): the full tuple must slot facts by original id.
        let bag = Bag { factors: vec![2, 0], vars: e(&[0]) };
        let m = vec![bm(&[b"F2", b"F0"], &[(0, b"v")])];
        let solo = Bag { factors: vec![1], vars: e(&[0]) };
        let m1 = vec![bm(&[b"F1"], &[(0, b"v")])];
        let full = join_bags(&[(bag, m), (solo, m1)], 3);
        assert_eq!(full, vec![vec![b"F0".to_vec(), b"F1".to_vec(), b"F2".to_vec()]]);
    }
}
