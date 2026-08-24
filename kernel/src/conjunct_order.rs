// Purpose: choose the order in which the ProductZipper descent visits a conjunctive body's
//   factors, which is the join order of MORK's shipped nested-loop matcher.
// Assumes: `factors` is `leapfrog::parse_body_factors`' output for the same `body`, so
//   factor `i` is the conjunction's argument `i`; `map` is the space the descent will read.
// Guarantees: returns either `None` (keep the written order) or a permutation of
//   `0..factors.len()`. Reordering changes only the ORDER answers are produced in, never the
//   multiset: every factor is still visited, and the caller re-encodes coreference through
//   `Space::renormalize_query_factors`.
// Fails when: the caller's consumer folds over the match set in arrival order. Reordering is
//   offered only through `Space::query_multi_planned`, which is what the space-to-space
//   transform dispatches to; the sink and source routes keep `Space::query_multi`. The whole
//   module is behind the `conjunct_order` feature, and without it nothing here is compiled.
// Decides: what one measurement may spend (`COLUMN_CAP`, `COLUMN_BYTE_CAP`, `BREADTH`); how
//   cheap a body has to be before it is not worth searching over (`PLAN_MIN_WRITTEN_COST`,
//   `PLAN_MIN_ROWS_PER_SUBSET`); where the exact search gives way to the greedy one
//   (`DP_MAX_FACTORS`); and how far a predicted win has to clear the written order before it
//   is taken (`SETTLED_BAND`, `UNCERTAINTY_WIDTH`).
//
//! Join order for the ProductZipper descent.
//!
//! `Space::query_multi` used to hand the conjunction's arguments to the descent in WRITTEN
//! order, which is the join order of a nested-loop join and therefore the single largest plan
//! decision in the engine. Over `bench clique`'s three bodies, written order is
//! [measured: 384,237,856,849 instructions:u, min of 3; command=`mork bench clique`;
//! fixture=200 nodes / 3600 edges;
//! commit=WORKTREE] and the order this module picks is
//! [measured: 2,865,023,996 instructions:u, min of 3; command=`mork bench clique --features
//! conjunct_order`, built in the same source directory as the baseline since the manifest path
//! is baked in and its length moves layout; fixture=200 nodes / 3600 edges;
//! commit=WORKTREE], the same 7,824 / 2,320 / 102 cliques either way.
//!
//! The gain is not a constant, and `mork bench clique_scaling` is there to show it: it holds a
//! random graph's average degree at 10, grows it, and prints `transitions` per size, so run it
//! on a build with this feature and one without and read the exponents off directly. The
//! four-clique body's written order grows as |E|^1.07 and the planned order's as |E|^0.88; for
//! five-clique, |E|^1.15 against |E|^0.74. The ratio therefore WIDENS with the input rather
//! than settling -- 10.6x to 17.0x, and 58.1x to 160.6x, over |E| = 300 to 3,400
//! [measured: four-clique |E|^1.07 written against |E|^0.88 planned, five-clique |E|^1.15
//! against |E|^0.74, least squares over the five sizes; command=`mork bench clique_scaling`,
//! run once without the feature and once with it; fixture=degree-10 random graphs, |E| = 300,
//! 800, 1300, 2100, 3400;
//! commit=WORKTREE]. The answer counts agree at every point.
//!
//! The cost model is System R's (Selinger et al., SIGMOD 1979), and it needs BOTH halves of
//! that paper's model, not just the famous one.
//!
//! The cardinality half estimates how many partial matches reach each step of the order, under
//! uniformity and independence: a variable's second and later occurrences are equalities that
//! divide out one domain apiece. The ACCESS PATH half estimates what one step then costs, and
//! that is where a byte-trie differs from a relational store. A PathMap indexes prefixes only.
//! A factor is entered by seeking its leading columns and scanning whatever is left, so a
//! variable bound in a leading column makes the step selective while the same variable bound in
//! a later column only rejects rows the descent has already walked. [`crate::leapfrog`] meets
//! the same fact from the other side: its `is_inverted` detects a factor whose bound variable
//! is not in leading position, and it pays to re-index that factor into a private map.
//!
//! Charging only the cardinality half reads the trie as though every column were indexed, and
//! that is not a small error. On a 3,400-edge graph of average degree 10 the four-clique body's
//! written order costs 1,538,745 transitions; cardinality alone prefers an order costing
//! 4,346,487, and the two-term model picks one costing 87,537.
//!
//! The access-path half has a second edge to it, which is what a term store has and a relational
//! store does not: a column can hold a VARIABLE. A stored variable unifies with every value, so
//! a query variable read out of such a column may itself be a variable, and the factor entered
//! next by seeking on it has no key to seek -- it scans. This is the degradation first-argument
//! indexing has in a WAM, where a clause with a variable head argument belongs in every bucket
//! and the index stops discriminating, in the retrieval-as-join setting of Riazanov and
//! Voronkov, `Efficient Instance Retrieval with Standard and Relational Path Indexing`, CADE-19,
//! LNAI 2741, pages 380-396, 2003. Missing it is not a bounded error either: one `(root $r)`
//! among three ground rows made a four-conjunct body's planned order walk 27x the written
//! order's transitions at 300 edges and 463x at 4,800, growing with the input. See
//! [`FactorStats::col_wildcard`], and `a_relation_holding_variables_does_not_mislead_the_planner`
//! in `kernel/tests/conjunct_order.rs`, which fails on a model that leaves it out.
//!
//! The search is the same paper's subset dynamic program. Each step's cost depends only on the
//! subset before it and the factor appended, so the program stays an exact minimisation over
//! the model rather than a heuristic over it. What differs from the textbook is where the
//! numbers come from: there are no materialized relations or collected histograms to read, so
//! every count is enumerated off the live byte-trie at plan time, which is what the measurement
//! ladder below is for.
//!
//! The structural alternative -- order by "most already-bound variables first", which is the
//! criterion Maude's `findConstraintPropagationSequence` uses -- wins the same order of
//! magnitude on `clique` and loses 37.1x on `finite_domain` and 24.6x on `counter_machine`,
//! because it cannot see that a conjunct is a 64-row lookup table rather than a 10,000-row
//! input relation. Cardinality is not optional here either.

use crate::leapfrog::{parse_body_factors, Factor, FactorColumn, SubtermCursor};
use log::trace;
use pathmap::PathMap;

/// Largest conjunct count the exact subset DP runs for. `2^12 * 12` transitions is tens of
/// thousands of f64 operations, paid once per transform and amortized over its whole join;
/// above it the greedy order on the same cost model takes over.
const DP_MAX_FACTORS: usize = 12;

/// How much better a plan must look when NOTHING about the body was measured to exhaustion. A
/// body whose every column was enumerated fully carries no uncertainty and needs no margin at
/// all; this is the other end of that scale.
const UNCERTAINTY_WIDTH: f64 = 4.0;

/// Floor on the written order's cost below which planning is skipped however badly the body is
/// ordered: a descent this short cannot repay being planned.
const PLAN_MIN_WRITTEN_COST: f64 = 10_000.0;

/// Rows the written order must walk for each subset the exact search would visit, on top of
/// that floor. The search is `2^n` entries of a few f64 operations; the descent walks
/// [`order_cost`] rows at a few tens of instructions each. Asking for roughly an order of
/// magnitude in hand puts the crossing point here.
///
/// A flat floor charges an eleven-conjunct body the same admission as a three-conjunct one when
/// the search it is buying is 256 times larger. `bench finite_domain`'s body is the case: eleven
/// conjuncts, a written order that walks 42,940 rows, and a full 2^11 search that concludes the
/// written order was already best. That search was +0.13% instructions:u on the benchmark, for
/// an answer it could not have used.
const PLAN_MIN_ROWS_PER_SUBSET: f64 = 250.0;

/// The written-order cost below which `n` conjuncts are not worth searching over.
fn plan_admission_cost(n: usize) -> f64 {
    let subsets = (1u64 << n.min(DP_MAX_FACTORS)) as f64;
    PLAN_MIN_WRITTEN_COST.max(PLAN_MIN_ROWS_PER_SUBSET * subsets)
}

/// Clamp on a prefix's log2 size. Past this the prefix is astronomically large and the exact
/// magnitude cannot change a comparison, but leaving it unclamped overflows the f64 sum.
const LOG_SIZE_CLAMP: f64 = 240.0;

/// What the plan needs to know about the body, all read in one descent per factor.
struct BodyStats {
    /// Estimated facts matching each factor's own skeleton, ignoring the rest of the body.
    rows: Vec<f64>,
    /// Each factor's query variables as a bitmask over the body's global numbering.
    vars: Vec<u64>,
    /// Each query variable's estimated distinct-value count: the largest number of distinct
    /// values seen at any column the variable occupies on its own.
    dom: Vec<f64>,
    /// `rows` and `dom` in log2, taken once. Every size the planner compares is a product of
    /// these, so the search works in logs; taking the logarithms inside the subset loop
    /// instead cost 12M instructions per plan and 16.5G on `bench counter_machine`.
    log_rows: Vec<f64>,
    log_dom: Vec<f64>,
    /// Each factor's access path, as a table indexed by how many leading columns are bound.
    ///
    /// A PathMap is a prefix trie, so a factor is entered by seeking its leading columns and
    /// scanning what is left: a bound column that is not in that leading run filters the
    /// factor's output but does not reduce the walk. This is the half of System R's model that
    /// is about access paths rather than cardinalities, and without it the planner reads a trie
    /// as though every column were indexed. See [`lead_scale`].
    ///
    /// Entry `k` is (the variables columns `0..k` need, the reciprocal of what seeking them
    /// divides the factor's rows by). Precomputed because the search consults it once per
    /// subset per factor, and a reciprocal multiplied there is an `exp2` not taken: charging
    /// the step in logs and exponentiating inside the loop cost `bench finite_domain`, whose
    /// eleven-conjunct body runs the full 2^11 search, +0.43% instructions:u on its own.
    lead: Vec<Vec<(u64, f64)>>,
    /// Share of the measured columns whose enumeration was cut short rather than exhausted, in
    /// `0.0..=1.0`. This is the evidence's uncertainty mass, and it is what the decision below
    /// discounts by: with none of it the estimate is exact and any predicted win may be taken,
    /// with all of it the plan must beat the written order by [`UNCERTAINTY_WIDTH`].
    uncertainty: f64,
}

/// The share of factor `f`'s rows the descent still walks once `bound` is bound: one over what
/// seeking its leading bound columns divides them by.
///
/// The walk stops at the first column whose variables are not all in `bound`. Past that point
/// the trie has no key to seek on, so the descent scans, and a column bound further right can
/// only reject rows it has already walked. A factor entered with nothing bound is a full scan
/// of the relation however many of its variables the rest of the body has already fixed.
#[inline]
fn lead_scale(stats: &BodyStats, f: usize, bound: u64) -> f64 {
    let path = &stats.lead[f];
    // The entries' masks are cumulative, so the last one asks for every variable the factor
    // mentions: one test settles the case a good order arranges, where the whole factor is
    // seekable and the descent walks a single row-range.
    match path.last() {
        None => return 1.0,
        Some(&(needs, reciprocal)) if needs & !bound == 0 => return reciprocal,
        Some(_) => {}
    }
    let mut scale = 1.0f64;
    for &(needs, reciprocal) in path {
        if needs & !bound != 0 {
            break;
        }
        scale = reciprocal;
    }
    scale
}

/// One factor's statistics: what its own relation looks like, independent of the body that
/// mentions it.
#[derive(Clone)]
struct FactorStats {
    /// Facts matching the factor's own skeleton, capped at the sample size.
    rows: f64,
    /// Distinct values seen at each column, in column order.
    col_distinct: Vec<usize>,
    /// Per column, whether its enumeration RAN OUT rather than being cut short. An exhaustive
    /// enumeration makes the count exact and the estimate certain; a truncated one makes it a
    /// lower bound, and the plan is only allowed to act on it when the win survives that.
    col_exact: Vec<bool>,
    /// Per column, whether any value stored there carries a VARIABLE.
    ///
    /// A stored variable unifies with every value, so a query variable read out of such a
    /// column may itself be a variable, and a later factor entered by seeking on it has no key
    /// to seek. This is the degradation first-argument indexing has in a WAM -- a clause whose
    /// head argument is a variable belongs in every bucket, so the index stops discriminating
    /// -- carried over to the retrieval-as-join setting of Riazanov and Voronkov, `Efficient
    /// Instance Retrieval with Standard and Relational Path Indexing`, CADE-19, LNAI 2741,
    /// pages 380-396, 2003.
    ///
    /// Cached with the rest of these and refreshed on the same schedule, so a relation that
    /// gains its first variable fact keeps the old reading until the next refresh. That costs a
    /// worse order and never a wrong answer, which is the trade the whole cache already makes.
    col_wildcard: Vec<bool>,
}

/// The cache key for a factor's statistics: its relation prefix and its column SHAPE, with
/// ground columns spelled out and every other column collapsed to one marker.
///
/// Statistics belong to a relation, not to the body that mentions it. Keying them here rather
/// than on the whole body is what keeps the measurement off the per-firing path: `bench
/// counter_machine` runs 1,368 distinct bodies over a handful of relations, and measuring each
/// body separately cost 16.5G instructions, more than the benchmark itself.
fn factor_key(factor: &Factor<'_>) -> Vec<u8> {
    let mut key = factor.prefix.to_vec();
    for column in &factor.cols {
        match column {
            FactorColumn::Term(term) if term.is_ground() => {
                key.push(0);
                key.extend_from_slice(unsafe { term.expr.span().as_ref().unwrap() });
            }
            _ => key.push(1),
        }
    }
    key
}

/// Cap on the statistics cache, so a program that keeps inventing relations cannot grow it
/// without bound. Reaching it clears the cache rather than evicting one entry: the whole point
/// is that the working set is small, and a cache this large is evidence it is not.
const STATS_CACHE_CAP: usize = 4096;

thread_local! {
    static FACTOR_STATS: std::cell::RefCell<std::collections::HashMap<Vec<u8>, (FactorStats, u32, usize)>> =
        std::cell::RefCell::new(std::collections::HashMap::new());
}

/// [`measure_factor`] with its result cached by [`factor_key`], refreshed when the use count
/// reaches a power of two so the statistics track a growing space at logarithmic cost.
fn factor_stats(map: &PathMap<()>, factor: &Factor<'_>, breadth: usize) -> Option<FactorStats> {
    let key = factor_key(factor);
    FACTOR_STATS.with(|cell| {
        let mut cache = cell.borrow_mut();
        if let Some((stats, uses, at)) = cache.get_mut(&key) {
            *uses = uses.saturating_add(1);
            if !uses.is_power_of_two() && *at >= breadth {
                return Some(stats.clone());
            }
        }
        let fresh = measure_factor(map, factor, breadth)?;
        if cache.len() >= STATS_CACHE_CAP {
            cache.clear();
        }
        cache.insert(key, (fresh.clone(), 1, breadth));
        Some(fresh)
    })
}

/// Hard ceiling on a single column's enumeration, so a pathological relation cannot make the
/// planner unbounded. The stopping rule below almost always stops long before this.
const COLUMN_CAP: usize = 4096;

/// Hard ceiling on the BYTES a single column's enumeration walks. A cursor step is a walk over
/// the value's own bytes, so this is the ceiling in the unit the enumeration actually spends;
/// [`COLUMN_CAP`] bounds how many values are read, not how long they are, and a relation over
/// deep terms can walk two orders of magnitude more per value than one over symbols.
///
/// `bench exponential_fringe` builds exponentially nested terms: its widest column averages 31
/// bytes a value and walked 129,896 of them under the value ceiling alone, which cost +0.117%
/// instructions:u on a body the planner goes on to decline. `bench clique`'s widest column
/// walks 666 bytes in total, and `bench finite_domain`'s 133, so neither reaches this and the
/// plan that wins clique 44x is unchanged by it.
const COLUMN_BYTE_CAP: usize = 16_384;

/// Values a column is enumerated for before the plateau rule may stop it. Below this a column
/// has not been seen well enough for "nothing new lately" to mean anything.
const COLUMN_MIN_SAMPLE: usize = 64;

/// Consecutive values adding nothing new that end a column's enumeration. Sampling until the
/// estimate stops moving, rather than to a fixed count, is what makes the planner's cost track
/// the column it is measuring: a 64-value domain costs 64 steps, a 200-value one costs 200, and
/// a column with a million distinct values stops as soon as the count is clearly large.
///
/// This is deliberately the assumption-free rule. Good and Turing's coverage estimator and
/// Chao's extrapolation of the unseen count are the textbook answer to the same question
/// (Haas, Naughton, Seshadri and Stokes, "Sampling-based estimation of the number of distinct
/// values of an attribute", VLDB 1995), and they measured WORSE here: they assume a random
/// sample of the population, and a trie enumerates the leftmost values under the leftmost
/// prefix, so the correction adds bias instead of removing it. Substituting Chao's estimate
/// inflated every domain, which divides in the size model, so the model under-estimated the
/// join and accepted a plan that cost `bench finite_domain` +127.061% instructions:u.
const COLUMN_PLATEAU: usize = 64;

/// How many values of the preceding column a later column's domain is unioned over. One is the
/// domain conditioned on whichever value sorts first -- an edge relation's out-degree rather
/// than its vertex count -- and that under-estimate made the four-clique body's plan miss by
/// enough to be refused.
///
/// The breadth is spent adaptively too: sampling stops early once a further value of the
/// preceding column adds no new value to the union, because the column's domain is then already
/// determined by what has been seen.
const BREADTH: usize = 8;

/// Position `cursor` past columns `0..i`, with column `i - 1` at its `s`-th value and every
/// earlier column at its first. False when a column runs out before that.
fn position_prefix(
    cursor: &mut SubtermCursor<pathmap::zipper::ReadZipperUntracked<'_, '_, ()>>,
    factor: &Factor<'_>,
    i: usize,
    s: usize,
) -> bool {
    for (j, column) in factor.cols.iter().enumerate().take(i) {
        match column {
            FactorColumn::Term(term) if term.is_ground() => {
                let bytes = unsafe { term.expr.span().as_ref().unwrap() };
                cursor.seek(bytes);
                if cursor.key() != Some(bytes) {
                    return false;
                }
            }
            _ => {
                cursor.first();
                if j + 1 == i {
                    for _ in 0..s {
                        cursor.next();
                    }
                }
                if cursor.key().is_none() {
                    return false;
                }
            }
        }
        cursor.descend_floor();
    }
    true
}

/// Read one factor's size and per-column distinct-value counts off the live trie.
///
/// The walk is COLUMN-wise, not fact-wise: the trie already groups a relation by column, so
/// enumerating a column's distinct values costs one cursor step per value instead of one pass
/// over every fact's bytes. Splitting sampled facts instead cost 12.8G instructions on `bench
/// counter_machine`, whose facts are around a kilobyte each.
///
/// A column after the first is measured under `BREADTH` different values of the column before
/// it: the union of those is the estimate of its MARGINAL domain, and the average of their
/// counts is its contribution to the relation's size. `rows` is the product of those averages,
/// which is exact when the relation is rectangular.
fn measure_factor(map: &PathMap<()>, factor: &Factor<'_>, breadth: usize) -> Option<FactorStats> {
    if breadth <= 1 {
        return measure_factor_once(map, factor);
    }
    let mut col_distinct = Vec::with_capacity(factor.cols.len());
    let mut col_exact = Vec::with_capacity(factor.cols.len());
    let mut col_wildcard = Vec::with_capacity(factor.cols.len());
    let mut rows = 1.0f64;

    for i in 0..factor.cols.len() {
        // A ground column does not branch: it is one value, and the only question is whether
        // the relation has it. Enumerating instead of seeking scanned every value at that
        // position -- for the usual factor whose column 0 is the relation head, that is every
        // head in the space -- and multiplied `rows` by the count it found there.
        if let FactorColumn::Term(term) = &factor.cols[i] {
            if term.is_ground() {
                let mut cursor = SubtermCursor::new(map.read_zipper_at_path(&factor.prefix));
                if !position_prefix(&mut cursor, factor, i, 0) {
                    return None;
                }
                let bytes = unsafe { term.expr.span().as_ref().unwrap() };
                cursor.seek(bytes);
                if cursor.key() != Some(bytes) {
                    return None;
                }
                col_distinct.push(1);
                col_exact.push(true);
                // A ground pattern column names one value and binds no query variable, so
                // there is nothing here a stored variable could make unseekable.
                col_wildcard.push(false);
                continue;
            }
        }
        let breadth = if i == 0 { 1 } else { breadth };
        let mut union = std::collections::HashSet::new();
        let mut total = 0usize;
        let mut samples = 0usize;
        let mut truncated = false;
        let mut wildcard = false;
        for s in 0..breadth {
            let before = union.len();
            let mut cursor = SubtermCursor::new(map.read_zipper_at_path(&factor.prefix));
            if !position_prefix(&mut cursor, factor, i, s) {
                break;
            }
            let (seen, cut, wild) = enumerate_column(&mut cursor, &mut union);
            truncated |= cut;
            wildcard |= wild;
            if seen == 0 {
                break;
            }
            total += seen;
            samples += 1;
            if s > 0 && union.len() == before {
                break;
            }
        }
        if samples == 0 {
            return None;
        }
        rows *= total as f64 / samples as f64;
        col_distinct.push(union.len().max(1));
        col_exact.push(!truncated);
        col_wildcard.push(wildcard);
    }

    Some(FactorStats {
        rows,
        col_distinct,
        col_exact,
        col_wildcard,
    })
}

/// The cheap reading: ONE descent through the factor's columns, measuring each as the cursor
/// passes it.
///
/// The wide reading has to re-open the cursor per sample because it revisits a column under
/// several values of the column before it. With one sample there is nothing to revisit, so
/// re-descending from the factor prefix for every column made the walk quadratic in the column
/// count for no gain -- 165 descents rather than 55 on an eleven-conjunct body.
fn measure_factor_once(map: &PathMap<()>, factor: &Factor<'_>) -> Option<FactorStats> {
    let mut col_distinct = Vec::with_capacity(factor.cols.len());
    let mut col_exact = Vec::with_capacity(factor.cols.len());
    let mut col_wildcard = Vec::with_capacity(factor.cols.len());
    let mut rows = 1.0f64;
    let mut cursor = SubtermCursor::new(map.read_zipper_at_path(&factor.prefix));

    for column in &factor.cols {
        match column {
            FactorColumn::Term(term) if term.is_ground() => {
                let bytes = unsafe { term.expr.span().as_ref().unwrap() };
                cursor.seek(bytes);
                if cursor.key() != Some(bytes) {
                    return None;
                }
                col_distinct.push(1);
                col_exact.push(true);
                col_wildcard.push(false);
            }
            _ => {
                // A column enumeration yields each value once, so counting them IS the
                // distinct count and the hashing the wide reading needs is dead weight here.
                let (seen, truncated, wildcard) = count_column(&mut cursor);
                if seen == 0 {
                    return None;
                }
                rows *= seen as f64;
                col_distinct.push(seen);
                col_exact.push(!truncated);
                col_wildcard.push(wildcard);
                cursor.first();
                if cursor.key().is_none() {
                    return None;
                }
            }
        }
        cursor.descend_floor();
    }

    Some(FactorStats {
        rows,
        col_distinct,
        col_exact,
        col_wildcard,
    })
}

/// Whether one value read off a column is ground. The cursor's key is exactly one complete
/// subterm, so this is the encoded term's own test and not a scan for tag bytes, which a
/// symbol's payload could impersonate.
#[inline]
fn value_is_ground(key: &[u8]) -> bool {
    mork_expr::Expr { ptr: key.as_ptr().cast_mut() }.is_ground()
}

/// Count the cursor's current column, stopping at the cap. Every value is distinct, so there is
/// nothing to deduplicate and no plateau to detect. Also reports whether any value there was
/// non-ground; see [`FactorStats::col_wildcard`].
fn count_column(
    cursor: &mut SubtermCursor<pathmap::zipper::ReadZipperUntracked<'_, '_, ()>>,
) -> (usize, bool, bool) {
    cursor.first();
    let mut seen = 0usize;
    let mut bytes = 0usize;
    let mut wildcard = false;
    while let Some(key) = cursor.key() {
        if seen >= COLUMN_CAP || bytes >= COLUMN_BYTE_CAP {
            return (seen, true, wildcard);
        }
        bytes += key.len();
        wildcard |= !value_is_ground(key);
        seen += 1;
        cursor.next();
    }
    (seen, false, wildcard)
}

/// Enumerate the cursor's current column into `union`, stopping on the plateau rule or the cap.
/// Returns how many values were seen, whether the enumeration was cut short, and whether any
/// value there was non-ground; see [`FactorStats::col_wildcard`].
fn enumerate_column(
    cursor: &mut SubtermCursor<pathmap::zipper::ReadZipperUntracked<'_, '_, ()>>,
    union: &mut std::collections::HashSet<u64>,
) -> (usize, bool, bool) {
    cursor.first();
    let mut seen = 0usize;
    let mut bytes = 0usize;
    let mut since_new = 0usize;
    let mut truncated = false;
    let mut wildcard = false;
    while let Some(key) = cursor.key() {
        if seen >= COLUMN_CAP || bytes >= COLUMN_BYTE_CAP {
            truncated = true;
            break;
        }
        bytes += key.len();
        wildcard |= !value_is_ground(key);
        if union.insert(fnv1a(key)) {
            since_new = 0;
        } else {
            since_new += 1;
        }
        seen += 1;
        if seen >= COLUMN_MIN_SAMPLE && since_new >= COLUMN_PLATEAU {
            truncated = true;
            break;
        }
        cursor.next();
    }
    (seen, truncated, wildcard)
}

/// The query variables one column needs bound before it can be sought.
#[inline]
fn column_var_mask(column: &FactorColumn<'_>) -> u64 {
    match column {
        FactorColumn::Var(v) if *v < 64 => 1u64 << v,
        // Past the mask's width the column can never read as bound, which stops the seek there
        // rather than claiming a selectivity the descent will not get.
        FactorColumn::Var(_) => u64::MAX,
        FactorColumn::Term(term) => term.vars(),
    }
}

/// Assemble the body's statistics from its factors'.
///
/// Returns `None` when a factor matches nothing here, since a plan built on an absent relation
/// is a plan built on a guess.
fn measure(
    map: &PathMap<()>,
    factors: &[Factor<'_>],
    nvars: usize,
    breadth: usize,
) -> Option<BodyStats> {
    let mut rows = Vec::with_capacity(factors.len());
    let mut columns_measured = 0usize;
    let mut columns_truncated = 0usize;
    let mut vars = Vec::with_capacity(factors.len());
    let mut lead = Vec::with_capacity(factors.len());
    let mut dom = vec![1.0f64; nvars];

    // Every factor is measured before any access path is costed, because the two are in
    // different factors: the column that stores a variable is one conjunct, and the seek that
    // variable defeats is another. `(root $x)` over a table holding `(root $r)` binds `$x` to a
    // variable once, and the `(edge $x $y)` that follows then scans all of `edge` for that one
    // binding -- the whole of a 27x pessimisation the cardinality-and-access-path model
    // otherwise reads as the body's best order.
    let measured: Vec<FactorStats> = factors
        .iter()
        .map(|factor| factor_stats(map, factor, breadth))
        .collect::<Option<_>>()?;

    // The variables a stored variable can reach. `column_var_mask` is read here as "what this
    // column can bind" rather than "what it needs", which agrees on every column the mask can
    // represent and, past its width, taints the whole body -- the conservative reading, since a
    // variable it cannot name is one it cannot exempt either.
    let mut wildcard = 0u64;
    for (factor, stats) in factors.iter().zip(&measured) {
        for (column, holds_a_variable) in factor.cols.iter().zip(&stats.col_wildcard) {
            if *holds_a_variable {
                wildcard |= column_var_mask(column);
            }
        }
    }

    for (factor, stats) in factors.iter().zip(&measured) {
        let mask = factor_var_mask(factor);

        let mut path = Vec::with_capacity(factor.cols.len());
        let mut needs = 0u64;
        let mut divisor = 1.0f64;
        for ((column, count), exact) in factor
            .cols
            .iter()
            .zip(stats.col_distinct.iter())
            .zip(stats.col_exact.iter())
        {
            let _ = exact;
            needs |= column_var_mask(column);
            if let FactorColumn::Var(v) = column {
                dom[*v] = dom[*v].max(*count as f64);
            }
            divisor *= (*count as f64).max(1.0);
            // A prefix that needs a wildcard variable is not a seek. The value bound to it may
            // itself be a variable, and the trie holds that under a variable byte rather than
            // under the value being sought, so the descent scans from here on. Ending the path
            // charges the rest of the factor as the scan it is.
            if needs & wildcard != 0 {
                break;
            }
            path.push((needs, 1.0 / divisor));
        }
        columns_measured += stats.col_exact.len();
        columns_truncated += stats.col_exact.iter().filter(|e| !**e).count();
        rows.push(stats.rows);
        vars.push(mask);
        lead.push(path);
    }

    let log_rows: Vec<f64> = rows.iter().map(|r| r.max(1.0).log2()).collect();
    // A variable's repeated occurrence is an equality that divides out one domain -- unless its
    // values can be variables, which unify with everything. Then the equality holds for free
    // and the join does not shrink there, which a domain of one says exactly.
    let log_dom: Vec<f64> = dom
        .iter()
        .enumerate()
        .map(|(v, d)| if v < 64 && wildcard & (1u64 << v) != 0 { 0.0 } else { d.max(1.0).log2() })
        .collect();
    let uncertainty = if columns_measured == 0 {
        1.0
    } else {
        columns_truncated as f64 / columns_measured as f64
    };
    Some(BodyStats {
        rows,
        vars,
        dom,
        log_rows,
        log_dom,
        lead,
        uncertainty,
    })
}

/// The plan cache's key: a bounded prefix of the body mixed with its length.
///
/// Hashing the whole body costs a pass over it on every transform, and a body is not small --
/// `bench counter_machine`'s carry whole machine states, and paying for them here was 0.91pp of
/// that benchmark against 0.21pp for everything the planner actually does. A prefix is enough
/// because a collision is harmless: every entry is a permutation of factor indices, so applying
/// one to the wrong body of the same factor count is still answer-preserving, and that count is
/// checked before the plan is used.
fn body_key(body: &[u8]) -> u64 {
    const PREFIX: usize = 64;
    let head = &body[..body.len().min(PREFIX)];
    fnv1a(head) ^ (body.len() as u64).wrapping_mul(0x9e37_79b9_7f4a_7c15)
}

/// FNV-1a over a column's bytes. Only distinctness matters here, and a collision costs an
/// estimate one unit of domain, so a 64-bit non-cryptographic hash is the right tool. The
/// crate's own expression hash is not, for either caller: it walks the whole term, and both
/// [`body_key`] and the column enumeration are bounded on purpose.
fn fnv1a(bytes: &[u8]) -> u64 {
    let mut hash = 0xcbf2_9ce4_8422_2325u64;
    for &b in bytes {
        hash ^= b as u64;
        hash = hash.wrapping_mul(0x0000_0100_0000_01b3);
    }
    hash
}

/// log2 of the estimated number of partial matches after joining the factors in `set`. This is
/// the model's cardinality half; [`lead_scale`] is its access-path half, and
/// [`order_cost`] is where the two meet.
///
/// Under uniformity and independence the join of a set of relations has
/// `prod(|R_f|) / prod_v dom(v)^(occurrences(v) - 1)` tuples: each variable after its first
/// occurrence is an equality that divides out one domain. The expression does not mention the
/// order the factors are joined in, which is exactly what makes the subset DP below exact for
/// this model rather than a heuristic over it.
fn set_log_size(stats: &BodyStats, set: u32) -> f64 {
    let (log_rows, log_dom) = (&stats.log_rows, &stats.log_dom);
    let mut log_size = 0.0f64;
    let mut seen = 0u64;
    for f in 0..stats.rows.len() {
        if set & (1u32 << f) == 0 {
            continue;
        }
        log_size += log_rows[f];
        let mut repeated = stats.vars[f] & seen;
        while repeated != 0 {
            let v = repeated.trailing_zeros() as usize;
            repeated &= repeated - 1;
            log_size -= log_dom[v];
        }
        seen |= stats.vars[f];
    }
    log_size.clamp(-LOG_SIZE_CLAMP, LOG_SIZE_CLAMP)
}

/// The descent's cost for one order: for each step, how many rows of the new factor the descent
/// walks, once for every partial match the steps before it produced.
///
/// The two halves are separately estimated and neither alone ranks orders correctly. The
/// PREFIX SIZE, from [`set_log_size`], is how many partial matches reach this step. The ROWS
/// WALKED is what entering the factor costs each of them, and on a prefix trie that is
/// `rows * `[`lead_scale`]. Charging the prefix size alone, as though every column were
/// indexed, ranks a body's orders by output and reads a trie as a relational store: on a
/// 3,400-edge graph of average degree 10 it preferred an order costing 4,346,487 transitions
/// to the written order's 1,538,745, where this model picks one costing 87,537.
fn order_cost(stats: &BodyStats, order: &[usize]) -> f64 {
    let mut set = 0u32;
    let mut bound = 0u64;
    let mut size = 1.0f64;
    let mut total = 0.0f64;
    for &f in order {
        total += size * stats.rows[f] * lead_scale(stats, f, bound);
        set |= 1u32 << f;
        bound |= stats.vars[f];
        size = set_log_size(stats, set).exp2();
    }
    total
}

/// Exact minimum-cost order by subset dynamic programming: `dp[S] = size(S) + min over f in S
/// of dp[S \ {f}]`. Selinger's left-deep enumeration over the size estimate above.
///
/// The size of each subset is built incrementally rather than recomputed: dropping `S`'s
/// lowest factor gives a subset already solved, so an entry costs one addition plus one
/// subtraction per variable the new factor shares with what is already there.


fn dp_order(stats: &BodyStats, n: usize) -> Vec<usize> {
    let full = 1usize << n;
    let mut union = vec![0u64; full];
    let mut log_size = vec![0.0f64; full];
    // `size[0]` is the empty prefix: one tuple, so the first factor of an order is charged a
    // full scan of itself rather than nothing.
    let mut size = vec![1.0f64; full];
    for set in 1..full {
        let f = set.trailing_zeros() as usize;
        let prev = set & (set - 1);
        let mut ls = log_size[prev] + stats.log_rows[f];
        let mut repeated = stats.vars[f] & union[prev];
        while repeated != 0 {
            let v = repeated.trailing_zeros() as usize;
            repeated &= repeated - 1;
            ls -= stats.log_dom[v];
        }
        ls = ls.clamp(-LOG_SIZE_CLAMP, LOG_SIZE_CLAMP);
        log_size[set] = ls;
        size[set] = ls.exp2();
        union[set] = union[prev] | stats.vars[f];
    }

    // The step's cost is a function of the subset BEFORE it and the factor appended, and of
    // nothing else, so Bellman's principle still holds and this remains an exact minimisation
    // over the model rather than a heuristic over it.
    let mut dp = vec![f64::INFINITY; full];
    let mut last = vec![usize::MAX; full];
    dp[0] = 0.0;
    for set in 1..full {
        let mut bits = set;
        while bits != 0 {
            let f = bits.trailing_zeros() as usize;
            bits &= bits - 1;
            let before = set & !(1 << f);
            let prev = dp[before];
            if !prev.is_finite() {
                continue;
            }
            let cost = prev + size[before] * stats.rows[f] * lead_scale(stats, f, union[before]);
            if cost < dp[set] {
                dp[set] = cost;
                last[set] = f;
            }
        }
    }

    let mut order = Vec::with_capacity(n);
    let mut set = full - 1;
    while set != 0 {
        let f = last[set];
        if f == usize::MAX {
            return Vec::new();
        }
        order.push(f);
        set &= !(1 << f);
    }
    order.reverse();
    order
}

/// Greedy order on the same cost model, for bodies past `DP_MAX_FACTORS`: repeatedly append
/// the factor that leaves the smallest prefix.
fn greedy_order(stats: &BodyStats, n: usize) -> Vec<usize> {
    let mut order = Vec::with_capacity(n);
    let mut set = 0u32;
    let mut used = vec![false; n];
    let mut bound = 0u64;
    let mut size = 1.0f64;
    for _ in 0..n {
        let mut best = usize::MAX;
        let mut best_step = f64::INFINITY;
        for f in 0..n {
            if used[f] {
                continue;
            }
            // The same step cost the exact search minimises, chosen one factor at a time.
            let step = size * stats.rows[f] * lead_scale(stats, f, bound);
            if step < best_step {
                best_step = step;
                best = f;
            }
        }
        used[best] = true;
        set |= 1u32 << best;
        bound |= stats.vars[best];
        size = set_log_size(stats, set).exp2();
        order.push(best);
    }
    order
}

/// The order the ProductZipper should descend `factors` in, or `None` to keep the written one.
///
/// `None` covers every case where planning cannot help or cannot be trusted: fewer than three
/// conjuncts (nothing to choose), an estimate that does not read off the trie, a plan that is
/// the written order already, and a plan whose predicted cost does not beat the written
/// order's by the margin [`decide`] applies.
fn plan(map: &PathMap<()>, factors: &[Factor<'_>], nvars: usize) -> Option<Vec<usize>> {
    let n = factors.len();
    if n < 3 || n > 32 || nvars == 0 || nvars > 64 {
        return None;
    }
    if !reordering_can_matter(factors) {
        return None;
    }
    // One pass per column first. A later column measured under a single value of the column
    // before it under-reports its domain -- an edge relation's second endpoint reads as the
    // first vertex's out-degree -- so this reading is cheap and biased in a known direction.
    let cheap = measure(map, factors, nvars, 1)?;
    let written: Vec<usize> = (0..n).collect();
    if order_cost(&cheap, &written) < plan_admission_cost(n) {
        // The descent this would re-plan walks fewer rows than the search over its orders
        // costs, so any order is fast enough and the plan is pure overhead.
        return None;
    }
    match decide(&cheap, n, &written) {
        // Settled: no refinement of the measurement could move the decision across the
        // margin, so buying one would be spending for an answer already in hand. This is
        // Russell and Wefald's stopping rule ("Principles of Metareasoning", KR 1989):
        // deliberate only while deliberation can still change the choice.
        Decision::Take(order) => return Some(order),
        Decision::Keep => return None,
        Decision::Unsettled(..) => {}
    }

    // In doubt, and only then, pay for the wider reading: each column after the first
    // measured under several values of the column before it, whose union estimates the
    // marginal the cheap pass under-reports.
    let stats = measure(map, factors, nvars, BREADTH)?;
    // Nothing further can be bought, so the band no longer applies and the margin decides.
    match decide(&stats, n, &written) {
        Decision::Take(order) => Some(order),
        Decision::Unsettled(order, ratio) if ratio > 1.0 => Some(order),
        Decision::Keep | Decision::Unsettled(..) => None,
    }
}

/// What the evidence says about the written order, and how firmly.
enum Decision {
    /// Take this order: it wins by more than a further measurement could take back.
    Take(Vec<usize>),
    /// Keep the written order: it is not losing by enough for a further measurement to matter.
    Keep,
    /// Close enough to the margin that a better measurement could change the answer. Carries
    /// the order and how far past the margin it sits, so a caller with nothing left to buy can
    /// decide on it anyway.
    Unsettled(Vec<usize>, f64),
}

/// How far from the margin a decision has to be before a better measurement cannot move it.
/// Inside this band the cheap reading is refined; outside it the answer is already known.
const SETTLED_BAND: f64 = 8.0;

fn decide(stats: &BodyStats, n: usize, written: &[usize]) -> Decision {
    let candidate = if n <= DP_MAX_FACTORS {
        dp_order(stats, n)
    } else {
        greedy_order(stats, n)
    };
    if candidate.len() != n || candidate == written {
        return Decision::Keep;
    }
    let written_cost = order_cost(stats, written);
    let candidate_cost = order_cost(stats, &candidate);
    // How much better the plan must look before it is taken, derived from the evidence rather
    // than fixed: none when every column was enumerated to exhaustion and the counts are exact,
    // rising to `UNCERTAINTY_WIDTH` when every one of them was cut short. A flat margin stands
    // in for this, and stands in badly, because it charges a well-measured body the same
    // scepticism as a barely-measured one.
    //
    // Applying the widening per factor instead, so that the costs became intervals compared for
    // dominance, was tried and is wrong here: the widening compounds along the prefix, so a
    // six-conjunct body is charged `UNCERTAINTY_WIDTH^6` and no plan survives.
    let margin = 1.0 + (UNCERTAINTY_WIDTH - 1.0) * stats.uncertainty;
    let ratio = written_cost / (candidate_cost * margin).max(f64::MIN_POSITIVE);
    trace!(
        target: "conjunct_order",
        "written={written_cost:.3e} best={candidate_cost:.3e} margin={margin:.2} ratio={ratio:.2} plan={candidate:?} rows={:?} dom={:?}",
        stats.rows, stats.dom
    );
    if ratio > SETTLED_BAND {
        Decision::Take(candidate)
    } else if ratio < 1.0 {
        // Already losing on the cheap reading. The band is asymmetric here because refinement
        // is not monotone in the candidate's favour -- the triangle body's ratio FALLS from
        // 1.00 to 0.50 when its columns are measured wider -- so a candidate that cannot beat
        // the written order on the cheap reading is refused without buying the wide one. Every
        // plan this corpus eventually takes has a cheap-pass ratio above 1 (2.92 for the
        // four-clique body, 53.08 for the five), which is calibration, not a proof.
        Decision::Keep
    } else {
        Decision::Unsettled(candidate, ratio)
    }
}

/// The query variables of one factor, as a bitmask. [`parse_body_factors`] already recorded
/// each column's variables, so this is a fold rather than a walk.
fn factor_var_mask(factor: &Factor<'_>) -> u64 {
    let mut mask = 0u64;
    for column in &factor.cols {
        match column {
            FactorColumn::Var(v) if *v < 64 => mask |= 1u64 << v,
            FactorColumn::Var(_) => {}
            FactorColumn::Term(term) => mask |= term.vars(),
        }
    }
    mask
}

/// GYO reduction over the factors' variable sets: drop every variable that lies in one edge
/// only, then drop any edge contained in another, until nothing changes. A conjunctive body is
/// alpha-acyclic exactly when that peels it to one edge or none; whatever will not peel is a
/// cycle. Reads the body only, never the data.
fn body_is_cyclic(factors: &[Factor<'_>]) -> bool {
    let mut edges: Vec<u64> = factors
        .iter()
        .map(factor_var_mask)
        .filter(|m| *m != 0)
        .collect();
    loop {
        let mut changed = false;

        let mut once = 0u64;
        let mut more = 0u64;
        for e in &edges {
            more |= once & e;
            once |= e;
        }
        let shared = more;
        for e in &mut edges {
            let reduced = *e & shared;
            if reduced != *e {
                *e = reduced;
                changed = true;
            }
        }

        let mut removed = None;
        'outer: for i in 0..edges.len() {
            for j in 0..edges.len() {
                if i != j && edges[i] & !edges[j] == 0 {
                    if edges[i] == edges[j] && i > j {
                        continue;
                    }
                    removed = Some(i);
                    break 'outer;
                }
            }
        }
        if let Some(i) = removed {
            edges.remove(i);
            changed = true;
        }

        if !changed {
            break;
        }
    }
    edges.len() > 1
}

/// Whether reordering can change this body's ASYMPTOTICS, decided from the body alone with no
/// trie access at all.
///
/// A nested-loop join over an alpha-acyclic body extends one hyperedge at a time along its join
/// tree, so every connected order enumerates the same class of intermediates and the written one
/// is within a constant factor of the best. What the order does decide is
///
///   - when a CYCLE's closing edges are checked. `clique`'s five-clique body is written
///     star-first, so all six cross edges are deferred until every vertex is bound; and
///   - whether a prefix is DISCONNECTED from the factor that follows it, which makes that step a
///     Cartesian product.
///
/// Everything else is left alone. That is what keeps the measurement off the bodies that fire
/// thousands of times over small relations: reading `bench counter_machine`'s facts to decide an
/// order cost 12.8G instructions, more than the benchmark, and the answer was always "keep the
/// written order".
fn reordering_can_matter(factors: &[Factor<'_>]) -> bool {
    if body_is_cyclic(factors) {
        return true;
    }
    let mut bound = 0u64;
    for factor in factors {
        let mask = factor_var_mask(factor);
        if bound != 0 && mask != 0 && mask & bound == 0 {
            return true;
        }
        bound |= mask;
    }
    false
}

/// Consecutive refusals before the planner starts skipping bodies.
const BACKOFF_TRIGGER: u32 = 2;

/// Longest run of bodies the planner will skip. One accepted plan resets the backoff, so this
/// only bounds how long a workload that has never benefited waits before asking again.
const BACKOFF_CAP: u32 = 4096;

/// Adaptive admission for the planner.
///
/// Planning costs a bounded read of the space per body, and a program whose bodies are all
/// refused pays that on every firing: `bench counter_machine` fires 1,813 transforms over 1,368
/// distinct cyclic bodies, every one of which the margin refuses, and measuring them all cost
/// more than the benchmark. After `BACKOFF_TRIGGER` consecutive refusals the planner skips a run
/// of bodies and doubles that run each time it refuses again, so a workload that never benefits
/// converges to no planning while one that does keeps it: a single acceptance clears the state.
#[derive(Default)]
struct Governor {
    refusals: u32,
    skip_remaining: u32,
    skip_len: u32,
}

thread_local! {
    static GOVERNOR: std::cell::Cell<(u32, u32, u32)> = const { std::cell::Cell::new((0, 0, 0)) };
}

/// How many sets the plan cache has, and how many ways each set holds. The product bounds the
/// number of specialized plans that can be live; both are powers of two so indexing is masking.
const CACHE_SETS: usize = 256;
const CACHE_WAYS: usize = 4;

/// Heat added to a slot each time its site asks for a plan, and the ceiling it saturates at.
const HEAT_TICK: f32 = 0.25;

/// Calls between decay sweeps, and the factor each sweep applies. PyPy runs its sweep off minor
/// collections; there is no equivalent hook here, so it runs off the call count.
const DECAY_INTERVAL: u32 = 4096;
const DECAY: f32 = 0.75;

/// Heat below which a slot is treated as absent, so its plan is re-derived against whatever the
/// space now holds. This is the deoptimisation edge: a plan lives exactly as long as the body
/// it was measured for keeps being fired.
const COLD: f32 = 0.05;

/// One decision, for one conjunctive body.
#[derive(Clone)]
struct PlanSlot {
    /// The body's key. Zero means empty; a collision is a wrong-but-valid plan, never a wrong
    /// answer, because `factors` is checked and every plan is a permutation.
    tag: u64,
    /// How much this body has been fired lately. Decays.
    heat: f32,
    /// The body's factor count, so a colliding tag cannot hand out a plan of the wrong length.
    factors: u16,
    /// `None` is a decision too: this body was measured and its written order kept.
    plan: Option<Box<[u8]>>,
}

impl PlanSlot {
    const EMPTY: PlanSlot = PlanSlot {
        tag: 0,
        heat: 0.0,
        factors: 0,
        plan: None,
    };
}

/// The plan cache: fixed size, set-associative, lossy, decaying.
///
/// The storage discipline is PyPy's JIT counter (`rpython/jit/metainterp/counter.py`), which
/// answers the same question -- is this worth compiling, and is what I compiled still worth
/// keeping. Three properties are carried over deliberately:
///
///   - **fixed size with accepted collisions.** No growth, no eviction policy, no rehash, and
///     no allocation to look one up. PyPy documents the cost of a collision exactly: the two
///     keys share a counter and warm twice as fast. Here a collision is caught by `factors`, and
///     even uncaught it can only produce a differently-ordered join, never a different answer.
///   - **heat rather than a use count.** A slot warms toward a ceiling and is evicted when it is
///     the coldest in its set, so a body that keeps firing holds its slot against one that does
///     not.
///   - **decay.** Every slot cools on a fixed interval, so a plan measured against a space that
///     has since grown does not survive on its past. A transform loop grows the space it is
///     reading, which is exactly the case where a plan measured once and kept forever goes
///     stale.
struct PlanCache {
    slots: Vec<PlanSlot>,
    since_decay: u32,
}

impl PlanCache {
    fn new() -> Self {
        PlanCache {
            slots: vec![PlanSlot::EMPTY; CACHE_SETS * CACHE_WAYS],
            since_decay: 0,
        }
    }

    fn set_base(tag: u64) -> usize {
        // The high bits pick the set, following PyPy: the low bits are already spent on the tag
        // comparison, so reusing them for the index would correlate the two.
        ((tag >> 40) as usize & (CACHE_SETS - 1)) * CACHE_WAYS
    }

    /// Warm the body's slot and return its decision, or `None` when it is absent or has gone
    /// cold. The outer `Option` is presence, the inner one is the decision: `Some(None)` is a
    /// remembered refusal, which is as much an answer as a remembered plan.
    fn get(&mut self, tag: u64) -> Option<Option<Vec<usize>>> {
        self.tick();
        let base = Self::set_base(tag);
        for way in 0..CACHE_WAYS {
            let slot = &mut self.slots[base + way];
            if slot.tag == tag {
                if slot.heat < COLD {
                    return None;
                }
                slot.heat = (slot.heat + HEAT_TICK).min(1.0);
                let plan = slot
                    .plan
                    .as_ref()
                    .map(|p| p.iter().map(|&i| i as usize).collect::<Vec<usize>>());
                return Some(plan.filter(|order| order.len() == slot.factors as usize));
            }
        }
        None
    }

    /// Install a decision for a body, evicting the coldest way of its set.
    fn put(&mut self, tag: u64, factors: usize, plan: Option<&[usize]>) {
        let base = Self::set_base(tag);
        let mut victim = base;
        for way in 0..CACHE_WAYS {
            let slot = &self.slots[base + way];
            if slot.tag == tag || slot.tag == 0 {
                victim = base + way;
                break;
            }
            if slot.heat < self.slots[victim].heat {
                victim = base + way;
            }
        }
        self.slots[victim] = PlanSlot {
            tag,
            heat: HEAT_TICK,
            factors: factors.min(u16::MAX as usize) as u16,
            plan: plan.map(|p| p.iter().map(|&i| i as u8).collect::<Box<[u8]>>()),
        };
    }

    fn tick(&mut self) {
        self.since_decay += 1;
        if self.since_decay < DECAY_INTERVAL {
            return;
        }
        self.since_decay = 0;
        for slot in &mut self.slots {
            slot.heat *= DECAY;
        }
    }
}

thread_local! {
    static PLANS: std::cell::RefCell<PlanCache> = std::cell::RefCell::new(PlanCache::new());
}

/// Plan `body`'s descent order, or `None` to keep the written one.
pub fn plan_cached(map: &PathMap<()>, pat_expr: mork_expr::Expr) -> Option<Vec<usize>> {
    // The backoff is consulted BEFORE the body is hashed. A workload the planner has given up
    // on then pays one integer decrement per transform instead of a pass over a kilobyte of
    // body bytes and a cache probe, which is the whole of what it costs `bench counter_machine`.
    let mut governor = GOVERNOR.with(|g| Governor {
        refusals: g.get().0,
        skip_remaining: g.get().1,
        skip_len: g.get().2,
    });
    if governor.skip_remaining > 0 {
        governor.skip_remaining -= 1;
        GOVERNOR.with(|g| g.set((governor.refusals, governor.skip_remaining, governor.skip_len)));
        return None;
    }

    // The span is taken HERE and not by the caller: it walks the whole body, and a body is not
    // small -- `bench counter_machine`'s carry whole machine states, and taking the span on
    // every transform before the backoff could decline was 0.91pp of that benchmark against
    // 0.21pp for everything the planner actually does.
    let body = unsafe { pat_expr.span().as_ref().unwrap() };
    let tag = body_key(body);
    if let Some(hit) = PLANS.with(|c| c.borrow_mut().get(tag)) {
        return hit;
    }

    let parsed = parse_body_factors(&pat_expr);
    let factor_count = parsed.as_ref().map_or(0, |(factors, _)| factors.len());
    let fresh = parsed.and_then(|(factors, nvars)| plan(map, &factors, nvars));

    if fresh.is_some() {
        governor = Governor::default();
    } else {
        governor.refusals += 1;
        if governor.refusals >= BACKOFF_TRIGGER {
            governor.refusals = 0;
            governor.skip_len = (governor.skip_len.max(1) * 2).min(BACKOFF_CAP);
            governor.skip_remaining = governor.skip_len;
        }
    }
    GOVERNOR.with(|g| g.set((governor.refusals, governor.skip_remaining, governor.skip_len)));

    PLANS.with(|c| c.borrow_mut().put(tag, factor_count, fresh.as_deref()));
    fresh
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::leapfrog::parse_body_factors;
    use mork_expr::{item_byte, Expr, Tag};

    fn sym(s: &str) -> Vec<u8> {
        let mut v = vec![item_byte(Tag::SymbolSize(s.len() as u8))];
        v.extend_from_slice(s.as_bytes());
        v
    }

    /// `(rel a0 a1 ...)` encoded: Arity(1+n), Sym(rel), then each argument's bytes.
    fn nest(rel: &str, args: &[Vec<u8>]) -> Vec<u8> {
        let mut v = vec![item_byte(Tag::Arity((1 + args.len()) as u8))];
        v.extend(sym(rel));
        for a in args {
            v.extend_from_slice(a);
        }
        v
    }

    fn conj(factors: &[Vec<u8>]) -> Vec<u8> {
        nest(",", factors)
    }

    fn new_var() -> Vec<u8> {
        vec![item_byte(Tag::NewVar)]
    }

    fn var_ref(idx: u8) -> Vec<u8> {
        vec![item_byte(Tag::VarRef(idx))]
    }

    /// A column value is a whole subterm, so a variable NESTED in one taints it exactly as a
    /// bare variable does: bind a query variable to `(p $a $b)` and the seek that follows is a
    /// pattern seek, not a key lookup. Reading only the value's first tag byte would call this
    /// ground.
    #[test]
    fn a_variable_nested_in_a_value_still_reads_as_a_wildcard() {
        assert!(value_is_ground(&sym("n7")));
        assert!(value_is_ground(&nest("p", &[sym("a"), sym("b")])));
        assert!(!value_is_ground(&new_var()));
        assert!(!value_is_ground(&var_ref(0)));
        assert!(!value_is_ground(&nest("p", &[sym("a"), new_var()])));
        assert!(!value_is_ground(&nest("p", &[nest("q", &[var_ref(0)]), sym("b")])));
    }

    /// A deterministic random graph as `(e vN vM)` facts, the shape `bench clique` builds.
    fn graph(nodes: usize, edges: usize) -> PathMap<()> {
        let mut map = PathMap::<()>::new();
        let mut state = 0x2545_f491_4f6c_dd1du64;
        let mut next = || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        let mut inserted = 0;
        while inserted < edges {
            let a = (next() as usize) % nodes;
            let b = (next() as usize) % nodes;
            if a == b {
                continue;
            }
            let (lo, hi) = if a < b { (a, b) } else { (b, a) };
            let fact = nest("e", &[sym(&format!("v{lo:03}")), sym(&format!("v{hi:03}"))]);
            if map.insert(&fact, ()).is_none() {
                map.insert(
                    &nest("e", &[sym(&format!("v{hi:03}")), sym(&format!("v{lo:03}"))]),
                    (),
                );
                inserted += 1;
            }
        }
        map
    }

    fn plan_for(map: &PathMap<()>, body: &[u8]) -> Option<Vec<usize>> {
        let body = Expr::from_slice(body);
        let (factors, nvars) = parse_body_factors(&body).expect("well-formed body");
        plan(map, &factors, nvars)
    }

    #[test]
    fn a_star_written_clique_body_is_replanned() {
        let map = graph(200, 3600);
        // (, (e $x0 $x1) (e $x0 $x2) (e $x0 $x3) (e $x1 $x2) (e $x1 $x3) (e $x2 $x3))
        let body = conj(&[
            nest("e", &[new_var(), new_var()]),
            nest("e", &[var_ref(0), new_var()]),
            nest("e", &[var_ref(0), new_var()]),
            nest("e", &[var_ref(1), var_ref(2)]),
            nest("e", &[var_ref(1), var_ref(3)]),
            nest("e", &[var_ref(2), var_ref(3)]),
        ]);
        let order = plan_for(&map, &body).expect("the star-first order must be replanned");
        let mut sorted = order.clone();
        sorted.sort_unstable();
        assert_eq!(sorted, (0..6).collect::<Vec<_>>(), "a permutation of the factors");

        let be = Expr::from_slice(&body);
        let (factors, nvars) = parse_body_factors(&be).unwrap();
        let stats = measure(&map, &factors, nvars, BREADTH).unwrap();
        assert!(
            order_cost(&stats, &order) * (1.0 + (UNCERTAINTY_WIDTH - 1.0) * stats.uncertainty)
                < order_cost(&stats, &(0..6).collect::<Vec<_>>()),
            "the plan must beat the written order by the evidence-derived margin it was accepted under"
        );
    }

    #[test]
    fn a_triangle_keeps_its_written_order() {
        let map = graph(40, 300);
        // (, (e $x0 $x1) (e $x0 $x2) (e $x1 $x2)) -- every order costs the same
        let body = conj(&[
            nest("e", &[new_var(), new_var()]),
            nest("e", &[var_ref(0), new_var()]),
            nest("e", &[var_ref(1), var_ref(2)]),
        ]);
        assert_eq!(plan_for(&map, &body), None);
    }

    #[test]
    fn a_functional_pipeline_keeps_its_written_order() {
        // The `finite_domain` shape: a wide input relation feeding lookup tables whose output
        // column is determined by their inputs. Written order is already optimal, and an order
        // that starts from a small table instead multiplies the tables together.
        let mut map = PathMap::<()>::new();
        for a in 0..20u8 {
            for b in 0..20u8 {
                map.insert(
                    &nest(
                        "op",
                        &[sym(&format!("s{a:02}")), sym(&format!("s{b:02}")), sym(&format!("s{:02}", (a + b) % 20))],
                    ),
                    (),
                );
            }
        }
        for a in 0..20u8 {
            map.insert(
                &nest("sq", &[sym(&format!("s{a:02}")), sym(&format!("s{:02}", (a * a) % 20))]),
                (),
            );
        }
        for a in 0..20u8 {
            for b in 0..20u8 {
                map.insert(
                    &nest("args", &[sym(&format!("s{a:02}")), sym(&format!("s{b:02}"))]),
                    (),
                );
            }
        }
        // (, (args $x0 $x1) (op $x0 $x1 $x2) (sq $x2 $x3))
        let body = conj(&[
            nest("args", &[new_var(), new_var()]),
            nest("op", &[var_ref(0), var_ref(1), new_var()]),
            nest("sq", &[var_ref(2), new_var()]),
        ]);
        assert_eq!(plan_for(&map, &body), None);
    }

    #[test]
    fn a_body_over_an_absent_relation_is_not_planned() {
        let map = graph(40, 300);
        let body = conj(&[
            nest("missing", &[new_var(), new_var()]),
            nest("e", &[var_ref(0), new_var()]),
            nest("e", &[var_ref(1), var_ref(2)]),
        ]);
        assert_eq!(plan_for(&map, &body), None);
    }
    #[test]
    fn two_bodies_keep_their_own_plans() {
        let mut cache = PlanCache::new();
        let one = body_key(b"a body");
        let other = body_key(b"a different body");
        assert_ne!(one, other, "distinct bodies must key apart");

        cache.put(one, 3, Some(&[2, 0, 1]));
        cache.put(other, 3, Some(&[2, 1, 0]));
        assert_eq!(cache.get(one), Some(Some(vec![2, 0, 1])));
        assert_eq!(cache.get(other), Some(Some(vec![2, 1, 0])));
    }

    #[test]
    fn a_refusal_is_cached_as_a_decision() {
        // "Keep the written order" is an answer, and re-deriving it every firing is what the
        // cache exists to prevent.
        let mut cache = PlanCache::new();
        let tag = body_key(b"another body");
        cache.put(tag, 4, None);
        assert_eq!(cache.get(tag), Some(None));
    }

    #[test]
    fn a_cold_site_is_replanned() {
        // Deoptimisation: a specialization survives only while its site keeps using it, so a
        // plan measured against a space that has since moved does not live on its past.
        let mut cache = PlanCache::new();
        let tag = body_key(b"cooling body");
        cache.put(tag, 3, Some(&[1, 2, 0]));
        assert!(cache.get(tag).is_some());
        for slot in &mut cache.slots {
            slot.heat = 0.0;
        }
        assert_eq!(cache.get(tag), None, "a cold site must be re-derived");
    }

    #[test]
    fn a_collision_cannot_hand_out_a_plan_of_the_wrong_length() {
        // The table is lossy on purpose. A collision may cost a worse order; it may never cost
        // an order the caller would index out of.
        let mut cache = PlanCache::new();
        let tag = body_key(b"body");
        cache.put(tag, 5, Some(&[1, 0, 2]));
        assert_eq!(cache.get(tag), Some(None), "a length mismatch is refused, not returned");
    }

    #[test]
    fn the_dynamic_program_beats_the_greedy_order_it_falls_back_to() {
        // The exact search is worth its 2^n only if it finds orders the greedy one misses. On
        // the four-clique body it does, and on any body it must never find a worse one.
        let map = graph(200, 3600);
        let body = conj(&[
            nest("e", &[new_var(), new_var()]),
            nest("e", &[var_ref(0), new_var()]),
            nest("e", &[var_ref(0), new_var()]),
            nest("e", &[var_ref(1), var_ref(2)]),
            nest("e", &[var_ref(1), var_ref(3)]),
            nest("e", &[var_ref(2), var_ref(3)]),
        ]);
        let be = Expr::from_slice(&body);
        let (factors, nvars) = parse_body_factors(&be).unwrap();
        let stats = measure(&map, &factors, nvars, BREADTH).unwrap();
        let exact = dp_order(&stats, 6);
        let greedy = greedy_order(&stats, 6);
        assert_eq!(exact.len(), 6);
        let mut sorted = exact.clone();
        sorted.sort_unstable();
        assert_eq!(sorted, (0..6).collect::<Vec<_>>(), "a permutation of the factors");
        assert!(
            order_cost(&stats, &exact) <= order_cost(&stats, &greedy),
            "the exact search must not lose to the greedy one it replaces"
        );
    }
}
