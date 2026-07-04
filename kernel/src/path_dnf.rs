use pathmap::PathMap;

/// Execution counters for a feature-gated PathMap DNF evaluation.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct DnfPathSetStats {
    /// Number of disjunctive clauses supplied by the caller.
    pub clauses: usize,
    /// Clauses actually evaluated before completion or short-circuit.
    pub clauses_evaluated: usize,
    /// Clauses skipped by a short-circuiting aggregate query.
    pub short_circuit_skipped_clauses: usize,
    /// Total number of supplied conjunctive factor positions in evaluated clauses.
    pub factors: usize,
    /// Factor positions whose pathsets were actually inspected before a clause
    /// completed or became empty.
    pub factors_evaluated: usize,
    /// Factor positions skipped after a conjunction became empty.
    pub short_circuit_skipped_factors: usize,
    /// Clauses with exactly one factor, which can be joined directly.
    pub singleton_clauses: usize,
    /// Clauses with at least two factors, which require meet operations.
    pub multi_factor_clauses: usize,
    /// Exact `PathMap::meet` operations used to materialize clause results.
    pub meet_ops: usize,
    /// Exact `PathMap::join` operations used to union clause results.
    pub join_ops: usize,
    /// Distinct factor references observed by pointer identity.
    pub distinct_factor_refs: usize,
    /// Repeated factor references beyond the first occurrence.
    pub repeated_factor_refs: usize,
    /// Sum of input factor value counts across evaluated factor positions
    /// (positions skipped by an empty-meet short-circuit are not counted).
    pub factor_input_values: usize,
    /// Sum of materialized clause-result value counts before final union.
    pub clause_output_values: usize,
    /// Clause-result values eliminated by duplicate-removing final union.
    pub duplicate_clause_values: usize,
    /// Evaluated clauses that produced an empty pathset.
    pub empty_clause_results: usize,
    /// Evaluated clauses that produced at least one path.
    pub non_empty_clause_results: usize,
    /// Largest materialized clause-result value count.
    pub peak_clause_values: usize,
    /// Largest materialized accumulated result value count.
    pub peak_result_values: usize,
}

/// Result of evaluating a finite pathset expression in disjunctive normal form.
#[derive(Clone, Debug)]
pub struct DnfPathSetResult {
    /// Exact pathset result of `clause0 OR clause1 OR ...`.
    pub map: PathMap<()>,
    /// Diagnostic counters that make the fallback work visible in tests.
    pub stats: DnfPathSetStats,
}

/// Result of checking whether a finite DNF pathset is non-empty.
#[derive(Clone, Debug)]
pub struct DnfPathSetExistenceResult {
    /// Whether at least one DNF clause produced an output path.
    pub exists: bool,
    /// Diagnostic counters for the short-circuiting DNF existence path.
    pub stats: DnfPathSetStats,
}

/// Result of exactly counting a finite DNF pathset.
#[derive(Clone, Debug)]
pub struct DnfPathSetCountResult {
    /// Duplicate-eliminated number of paths in the DNF result.
    pub count: usize,
    /// Diagnostic counters for the exact DNF count path.
    pub stats: DnfPathSetStats,
}

/// Errors for finite DNF pathset evaluation.
///
/// Known divergence, surfaced deliberately: this evaluator REJECTS an empty
/// clause, because the empty conjunction denotes the universal pathset (the DNF
/// convention: an empty AND is TOP), which no finite `PathMap<()>` represents.
/// PathMap's `zipper_merge_dnf` instead treats an empty clause as an EMPTY
/// contribution to the union (see its
/// `zipper_merge_dnf_treats_empty_clause_as_empty_finite_clause` test), i.e. as
/// BOTTOM rather than TOP. One of the two conventions should win before either
/// is load-bearing; the differential tests below therefore only exercise
/// non-empty clauses, and the divergence itself is pinned by a dedicated test.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DnfPathSetError {
    /// An empty conjunction would denote the universal pathset, which is not a
    /// finite `PathMap<()>` value.
    EmptyClause { clause_index: usize },
}

/// Evaluates a finite pathset expression in disjunctive normal form.
///
/// Each inner slice is a conjunction evaluated with [`PathMap::meet`]. Clause
/// results are then combined with [`PathMap::join`]. This is the deliberately
/// simple reference for PathMap's fused `zipper_merge_dnf` engine
/// (`pathmap::experimental::zipper_algebra`, feature `zipper_alg`): every step
/// delegates to a public PathMap algebra op, so the differential tests below
/// can seal the fused engine against it.
pub fn evaluate_pathmap_dnf(
    clauses: &[&[&PathMap<()>]],
) -> Result<DnfPathSetResult, DnfPathSetError> {
    let (accumulated, stats) = evaluate_accumulated_dnf(clauses)?;

    Ok(DnfPathSetResult {
        map: accumulated.into_map(),
        stats,
    })
}

/// Checks whether a finite DNF pathset is non-empty without materializing the
/// final duplicate-eliminating union.
pub fn evaluate_pathmap_dnf_exists(
    clauses: &[&[&PathMap<()>]],
) -> Result<DnfPathSetExistenceResult, DnfPathSetError> {
    let mut exists = false;
    let stats = evaluate_clauses(clauses, |clause_result, _| {
        exists = clause_result.values > 0;
        Ok(exists)
    })?;

    Ok(DnfPathSetExistenceResult { exists, stats })
}

/// Counts a finite DNF pathset exactly, without returning the map.
///
/// Exact set count over DNF clauses is duplicate-sensitive because clauses may
/// overlap, so the count comes from the same duplicate-eliminating union the
/// full evaluation builds; only the map is not returned. As the reference
/// evaluator this stays the simplest correct thing rather than optimizing.
pub fn evaluate_pathmap_dnf_count(
    clauses: &[&[&PathMap<()>]],
) -> Result<DnfPathSetCountResult, DnfPathSetError> {
    let (accumulated, stats) = evaluate_accumulated_dnf(clauses)?;

    Ok(DnfPathSetCountResult {
        count: accumulated.count(),
        stats,
    })
}

fn evaluate_accumulated_dnf(
    clauses: &[&[&PathMap<()>]],
) -> Result<(DnfPathSetAccumulator, DnfPathSetStats), DnfPathSetError> {
    let mut accumulated = DnfPathSetAccumulator::new();
    let mut stats = evaluate_clauses(clauses, |clause_result, stats| {
        accumulated.push(clause_result, stats);
        Ok(false)
    })?;
    finish_accumulated_count(accumulated.count(), &mut stats);

    Ok((accumulated, stats))
}

fn evaluator_state(clauses: &[&[&PathMap<()>]]) -> (DnfPathSetStats, Vec<*const ()>) {
    (
        DnfPathSetStats {
            clauses: clauses.len(),
            ..DnfPathSetStats::default()
        },
        Vec::new(),
    )
}

fn evaluate_clauses(
    clauses: &[&[&PathMap<()>]],
    mut consume: impl FnMut(ClauseEvaluation, &mut DnfPathSetStats) -> Result<bool, DnfPathSetError>,
) -> Result<DnfPathSetStats, DnfPathSetError> {
    let (mut stats, mut distinct_factor_refs) = evaluator_state(clauses);

    for (clause_index, clause) in clauses.iter().enumerate() {
        let clause_result =
            evaluate_clause(clause_index, clause, &mut stats, &mut distinct_factor_refs)?;
        if consume(clause_result, &mut stats)? {
            stats.short_circuit_skipped_clauses = clauses.len().saturating_sub(clause_index + 1);
            break;
        }
    }

    Ok(stats)
}

fn finish_accumulated_count(count: usize, stats: &mut DnfPathSetStats) {
    stats.duplicate_clause_values = stats.clause_output_values.saturating_sub(count);
}

struct DnfPathSetAccumulator {
    map: PathMap<()>,
    has_result: bool,
    count: usize,
}

impl DnfPathSetAccumulator {
    fn new() -> Self {
        Self {
            map: PathMap::new(),
            has_result: false,
            count: 0,
        }
    }

    fn push(&mut self, clause_result: ClauseEvaluation, stats: &mut DnfPathSetStats) {
        if clause_result.values == 0 {
            return;
        }

        if self.has_result {
            self.map = self.map.join(&clause_result.map);
            stats.join_ops += 1;
            self.count = self.map.val_count();
        } else {
            self.count = clause_result.values;
            self.map = clause_result.map;
            self.has_result = true;
        }
        stats.peak_result_values = stats.peak_result_values.max(self.count);
    }

    fn count(&self) -> usize {
        self.count
    }

    fn into_map(self) -> PathMap<()> {
        self.map
    }
}

struct ClauseEvaluation {
    map: PathMap<()>,
    values: usize,
}

fn evaluate_clause(
    clause_index: usize,
    clause: &[&PathMap<()>],
    stats: &mut DnfPathSetStats,
    distinct_factor_refs: &mut Vec<*const ()>,
) -> Result<ClauseEvaluation, DnfPathSetError> {
    if clause.is_empty() {
        return Err(DnfPathSetError::EmptyClause { clause_index });
    }

    record_clause_shape(stats, clause);
    let clause_map = materialize_clause(clause, stats, distinct_factor_refs);
    let clause_values = record_clause_output(stats, &clause_map);

    Ok(ClauseEvaluation {
        map: clause_map,
        values: clause_values,
    })
}

fn record_clause_shape(stats: &mut DnfPathSetStats, clause: &[&PathMap<()>]) {
    stats.clauses_evaluated += 1;
    stats.factors += clause.len();

    if clause.len() == 1 {
        stats.singleton_clauses += 1;
    } else {
        stats.multi_factor_clauses += 1;
    }
}

fn record_factor_input(
    stats: &mut DnfPathSetStats,
    distinct_factor_refs: &mut Vec<*const ()>,
    factor: &PathMap<()>,
) {
    stats.factors_evaluated += 1;
    stats.factor_input_values += factor.val_count();
    let factor_ref = std::ptr::from_ref(factor).cast::<()>();
    if distinct_factor_refs.contains(&factor_ref) {
        stats.repeated_factor_refs += 1;
    } else {
        distinct_factor_refs.push(factor_ref);
        stats.distinct_factor_refs += 1;
    }
}

fn materialize_clause(
    clause: &[&PathMap<()>],
    stats: &mut DnfPathSetStats,
    distinct_factor_refs: &mut Vec<*const ()>,
) -> PathMap<()> {
    record_factor_input(stats, distinct_factor_refs, clause[0]);
    let mut clause_map = clause[0].clone();

    if clause_map.is_empty() {
        stats.short_circuit_skipped_factors += clause.len().saturating_sub(1);
        return clause_map;
    }

    for (factor_index, factor) in clause.iter().enumerate().skip(1) {
        record_factor_input(stats, distinct_factor_refs, factor);
        clause_map = clause_map.meet(factor);
        stats.meet_ops += 1;

        if clause_map.is_empty() {
            stats.short_circuit_skipped_factors += clause.len().saturating_sub(factor_index + 1);
            break;
        }
    }

    clause_map
}

fn record_clause_output(stats: &mut DnfPathSetStats, clause_map: &PathMap<()>) -> usize {
    let clause_values = clause_map.val_count();

    stats.clause_output_values += clause_values;
    stats.empty_clause_results += usize::from(clause_values == 0);
    stats.non_empty_clause_results += usize::from(clause_values > 0);
    stats.peak_clause_values = stats.peak_clause_values.max(clause_values);

    clause_values
}

#[cfg(test)]
mod tests {
    use super::*;

    type Paths = &'static [&'static [u8]];

    const SMALL_TRIE_1: Paths = &[&[0, 1, 2], &[0, 1, 3]];
    const SMALL_TRIE_2: Paths = &[&[0, 1], &[0, 2], &[3], &[2, 3]];
    const SMALL_TRIE_3: Paths = &[&[0, 1, 2], &[0, 1, 3], &[0, 1, 4]];
    const EMPTY_PATHS: Paths = &[];

    fn map(paths: Paths) -> PathMap<()> {
        PathMap::from_iter(paths.iter().copied())
    }

    fn assert_same_paths(actual: &PathMap<()>, expected: &PathMap<()>, expected_paths: Paths) {
        assert_eq!(
            expected.val_count(),
            expected_paths.len(),
            "test expected list does not describe the complete expected map"
        );

        let mut remainder = actual.clone();
        for path in expected_paths {
            assert!(
                actual.path_exists_at(path),
                "expected path {path:?} missing from actual result"
            );
            assert!(
                expected.path_exists_at(path),
                "test expected list contains path {path:?} not present in expected map"
            );
            remainder.remove_val_at(path, true);
        }

        for path in SMALL_TRIE_1
            .iter()
            .chain(SMALL_TRIE_2.iter())
            .chain(SMALL_TRIE_3.iter())
        {
            assert_eq!(
                actual.path_exists_at(path),
                expected.path_exists_at(path),
                "path {path:?} disagrees between actual and expected"
            );
        }
        assert_eq!(
            remainder.val_count(),
            0,
            "actual result contains extra paths"
        );
    }

    fn assert_stats(actual: DnfPathSetStats, expected: [usize; 19]) {
        let [clauses, clauses_evaluated, short_circuit_skipped_clauses, factors, factors_evaluated, short_circuit_skipped_factors, singleton_clauses, multi_factor_clauses, meet_ops, join_ops, distinct_factor_refs, repeated_factor_refs, factor_input_values, clause_output_values, duplicate_clause_values, empty_clause_results, non_empty_clause_results, peak_clause_values, peak_result_values] =
            expected;

        assert_eq!(
            actual,
            DnfPathSetStats {
                clauses,
                clauses_evaluated,
                short_circuit_skipped_clauses,
                factors,
                factors_evaluated,
                short_circuit_skipped_factors,
                singleton_clauses,
                multi_factor_clauses,
                meet_ops,
                join_ops,
                distinct_factor_refs,
                repeated_factor_refs,
                factor_input_values,
                clause_output_values,
                duplicate_clause_values,
                empty_clause_results,
                non_empty_clause_results,
                peak_clause_values,
                peak_result_values,
            }
        );
    }

    fn assert_output_stats(
        stats: &DnfPathSetStats,
        expected: (usize, usize, usize, usize, usize, usize, usize),
    ) {
        assert_eq!(
            (
                stats.factor_input_values,
                stats.clause_output_values,
                stats.duplicate_clause_values,
                stats.empty_clause_results,
                stats.non_empty_clause_results,
                stats.peak_clause_values,
                stats.peak_result_values,
            ),
            expected
        );
    }

    #[test]
    fn dnf_single_clause_matches_multiway_meet() {
        let trie1 = map(SMALL_TRIE_1);
        let trie2 = map(SMALL_TRIE_2);
        let trie3 = map(SMALL_TRIE_3);

        let result = evaluate_pathmap_dnf(&[&[&trie1, &trie2, &trie3]]).unwrap();
        let expected = trie1.meet(&trie2).meet(&trie3);

        assert_same_paths(&result.map, &expected, EMPTY_PATHS);
        assert_eq!(result.stats.clauses, 1);
        assert_eq!(result.stats.clauses_evaluated, 1);
        assert_eq!(result.stats.short_circuit_skipped_clauses, 0);
        assert_eq!(result.stats.factors, 3);
        assert_eq!(result.stats.factors_evaluated, 2);
        assert_eq!(result.stats.short_circuit_skipped_factors, 1);
        assert_eq!(result.stats.meet_ops, 1);
        assert_eq!(result.stats.join_ops, 0);
        assert_eq!(result.stats.distinct_factor_refs, 2);
        assert_eq!(result.stats.repeated_factor_refs, 0);
        assert_eq!(result.stats.factor_input_values, 6);
        assert_eq!(result.stats.clause_output_values, 0);
        assert_eq!(result.stats.duplicate_clause_values, 0);
        assert_eq!(result.stats.empty_clause_results, 1);
        assert_eq!(result.stats.non_empty_clause_results, 0);
        assert_eq!(result.stats.peak_clause_values, 0);
        assert_eq!(result.stats.peak_result_values, 0);
    }

    #[test]
    fn dnf_singleton_clauses_match_multiway_join() {
        let trie1 = map(SMALL_TRIE_1);
        let trie2 = map(SMALL_TRIE_2);
        let trie3 = map(SMALL_TRIE_3);

        let result = evaluate_pathmap_dnf(&[&[&trie1], &[&trie2], &[&trie3]]).unwrap();
        let expected = trie1.join(&trie2).join(&trie3);

        assert_same_paths(
            &result.map,
            &expected,
            &[
                &[0, 1],
                &[0, 1, 2],
                &[0, 1, 3],
                &[0, 1, 4],
                &[0, 2],
                &[2, 3],
                &[3],
            ],
        );
        assert_eq!(result.stats.singleton_clauses, 3);
        assert_eq!(result.stats.clauses_evaluated, 3);
        assert_eq!(result.stats.short_circuit_skipped_clauses, 0);
        assert_eq!(result.stats.multi_factor_clauses, 0);
        assert_eq!(result.stats.factors_evaluated, 3);
        assert_eq!(result.stats.short_circuit_skipped_factors, 0);
        assert_eq!(result.stats.meet_ops, 0);
        assert_eq!(result.stats.join_ops, 2);
        assert_eq!(result.stats.distinct_factor_refs, 3);
        assert_eq!(result.stats.repeated_factor_refs, 0);
        assert_eq!(result.stats.factor_input_values, 9);
        assert_eq!(result.stats.clause_output_values, 9);
        assert_eq!(result.stats.duplicate_clause_values, 2);
        assert_eq!(result.stats.empty_clause_results, 0);
        assert_eq!(result.stats.non_empty_clause_results, 3);
        assert_eq!(result.stats.peak_clause_values, 4);
        assert_eq!(result.stats.peak_result_values, 7);
    }

    #[test]
    fn dnf_partial_overlap_matches_distributed_reference() {
        let trie1 = map(SMALL_TRIE_1);
        let trie2 = map(SMALL_TRIE_2);
        let trie3 = map(SMALL_TRIE_3);

        let result = evaluate_pathmap_dnf(&[&[&trie1, &trie2], &[&trie1, &trie3]]).unwrap();
        let expected = trie1.meet(&trie2.join(&trie3));

        assert_same_paths(&result.map, &expected, SMALL_TRIE_1);
        assert_eq!(result.stats.clauses, 2);
        assert_eq!(result.stats.clauses_evaluated, 2);
        assert_eq!(result.stats.short_circuit_skipped_clauses, 0);
        assert_eq!(result.stats.factors, 4);
        assert_eq!(result.stats.factors_evaluated, 4);
        assert_eq!(result.stats.short_circuit_skipped_factors, 0);
        assert_eq!(result.stats.meet_ops, 2);
        assert_eq!(result.stats.join_ops, 0);
        assert_eq!(result.stats.distinct_factor_refs, 3);
        assert_eq!(result.stats.repeated_factor_refs, 1);
        assert_eq!(result.stats.factor_input_values, 11);
        assert_eq!(result.stats.clause_output_values, 2);
        assert_eq!(result.stats.duplicate_clause_values, 0);
        assert_eq!(result.stats.empty_clause_results, 1);
        assert_eq!(result.stats.non_empty_clause_results, 1);
        assert_eq!(result.stats.peak_clause_values, 2);
        assert_eq!(result.stats.peak_result_values, 2);
    }

    #[test]
    fn dnf_prunes_remaining_factors_after_empty_intermediate() {
        let trie1 = map(SMALL_TRIE_1);
        let trie2 = map(SMALL_TRIE_2);
        let trie3 = map(SMALL_TRIE_3);
        let empty = map(EMPTY_PATHS);

        let result = evaluate_pathmap_dnf(&[&[&trie1, &empty, &trie2, &trie3], &[&trie3]]).unwrap();

        assert_same_paths(&result.map, &trie3, SMALL_TRIE_3);
        assert_eq!(result.stats.clauses, 2);
        assert_eq!(result.stats.clauses_evaluated, 2);
        assert_eq!(result.stats.factors, 5);
        assert_eq!(result.stats.factors_evaluated, 3);
        assert_eq!(
            (
                result.stats.short_circuit_skipped_factors,
                result.stats.singleton_clauses,
                result.stats.multi_factor_clauses,
                result.stats.meet_ops,
                result.stats.join_ops,
            ),
            (2, 1, 1, 1, 0)
        );
        assert_eq!(result.stats.distinct_factor_refs, 3);
        assert_eq!(result.stats.repeated_factor_refs, 0);
        assert_output_stats(&result.stats, (5, 3, 0, 1, 1, 3, 3));
    }

    #[test]
    fn dnf_rejects_empty_clause_without_universal_pathset() {
        let trie1 = map(SMALL_TRIE_1);

        assert_eq!(
            evaluate_pathmap_dnf(&[&[&trie1], &[]]).unwrap_err(),
            DnfPathSetError::EmptyClause { clause_index: 1 }
        );
    }

    #[test]
    fn dnf_exists_short_circuits_without_final_union() {
        let trie1 = map(SMALL_TRIE_1);
        let trie2 = map(SMALL_TRIE_2);
        let trie3 = map(SMALL_TRIE_3);

        let result =
            evaluate_pathmap_dnf_exists(&[&[&trie1, &trie2, &trie3], &[&trie1], &[&trie2]])
                .unwrap();

        assert!(result.exists);
        assert_eq!(result.stats.clauses, 3);
        assert_eq!(result.stats.clauses_evaluated, 2);
        assert_eq!(result.stats.short_circuit_skipped_clauses, 1);
        assert_eq!(result.stats.factors, 4);
        assert_eq!(result.stats.factors_evaluated, 3);
        assert_eq!(
            (
                result.stats.short_circuit_skipped_factors,
                result.stats.singleton_clauses,
                result.stats.multi_factor_clauses,
                result.stats.meet_ops,
                result.stats.join_ops,
            ),
            (1, 1, 1, 1, 0)
        );
        assert_eq!(result.stats.distinct_factor_refs, 2);
        assert_eq!(result.stats.repeated_factor_refs, 1);
        assert_output_stats(&result.stats, (8, 2, 0, 1, 1, 2, 0));
    }

    #[test]
    fn dnf_count_matches_single_non_empty_clause() {
        let trie1 = map(SMALL_TRIE_1);
        let trie2 = map(SMALL_TRIE_2);
        let empty = map(EMPTY_PATHS);

        let result = evaluate_pathmap_dnf_count(&[&[&trie1, &empty, &trie2], &[&trie1]]).unwrap();

        assert_eq!(result.count, trie1.val_count());
        assert_stats(
            result.stats,
            [2, 2, 0, 4, 3, 1, 1, 1, 1, 0, 2, 1, 4, 2, 0, 1, 1, 2, 2],
        );
    }

    #[test]
    fn dnf_count_sums_disjoint_clauses_exactly() {
        let trie1 = map(SMALL_TRIE_1);
        let trie2 = map(SMALL_TRIE_2);

        let result = evaluate_pathmap_dnf_count(&[&[&trie1], &[&trie2]]).unwrap();

        assert_eq!(result.count, trie1.join(&trie2).val_count());
        assert_stats(
            result.stats,
            [2, 2, 0, 2, 2, 0, 2, 0, 0, 1, 2, 0, 6, 6, 0, 0, 2, 4, 6],
        );
    }

    #[test]
    fn dnf_count_eliminates_duplicates_across_overlapping_clauses() {
        let trie1 = map(SMALL_TRIE_1);
        let trie3 = map(SMALL_TRIE_3);

        let result = evaluate_pathmap_dnf_count(&[&[&trie1], &[&trie3]]).unwrap();

        assert_eq!(result.count, trie1.join(&trie3).val_count());
        assert_stats(
            result.stats,
            [2, 2, 0, 2, 2, 0, 2, 0, 0, 1, 2, 0, 5, 5, 2, 0, 2, 3, 3],
        );
    }

    /// Differential seal against PathMap's fused DNF engine: for every
    /// non-empty-clause DNF, the reference (meet/join composition) and
    /// `zipper_merge_dnf` must produce the same pathset. Empty clauses are
    /// excluded because the two conventions diverge there (see
    /// [`DnfPathSetError`]).
    mod differential {
        use super::*;
        use pathmap::experimental::zipper_algebra::zipper_merge_dnf;
        use pathmap::zipper::*;

        fn merged(clauses: &[&[&PathMap<()>]]) -> PathMap<()> {
            let mut out = PathMap::new();
            let mut zippers: Vec<Vec<_>> = clauses
                .iter()
                .map(|clause| clause.iter().map(|m| m.read_zipper()).collect())
                .collect();
            let mut clause_refs: Vec<Vec<_>> = zippers
                .iter_mut()
                .map(|clause| clause.iter_mut().collect::<Vec<_>>())
                .collect();
            match &mut clause_refs[..] {
                [a] => zipper_merge_dnf(&mut [&mut a[..]], &mut out.write_zipper()),
                [a, b] => zipper_merge_dnf(&mut [&mut a[..], &mut b[..]], &mut out.write_zipper()),
                [a, b, c] => zipper_merge_dnf(
                    &mut [&mut a[..], &mut b[..], &mut c[..]],
                    &mut out.write_zipper(),
                ),
                _ => panic!("differential harness covers 1-3 clauses"),
            }
            out
        }

        fn assert_agrees(clauses: &[&[&PathMap<()>]]) {
            let reference = evaluate_pathmap_dnf(clauses).unwrap().map;
            let fused = merged(clauses);
            assert_eq!(
                reference.val_count(),
                fused.val_count(),
                "value counts diverge"
            );
            let mut rz = reference.read_zipper();
            while rz.to_next_val() {
                assert!(
                    fused.path_exists_at(rz.path()),
                    "path {:?} in reference but not fused",
                    rz.path()
                );
            }
        }

        #[test]
        fn fused_engine_agrees_on_meet_join_and_mixed_shapes() {
            let trie1 = map(SMALL_TRIE_1);
            let trie2 = map(SMALL_TRIE_2);
            let trie3 = map(SMALL_TRIE_3);

            assert_agrees(&[&[&trie1, &trie2, &trie3]]);
            assert_agrees(&[&[&trie1], &[&trie2], &[&trie3]]);
            assert_agrees(&[&[&trie1, &trie2], &[&trie1, &trie3]]);
        }

        #[test]
        fn fused_engine_agrees_on_random_dnfs() {
            // deterministic LCG; no time or thread dependence
            let mut state = 0x9e37_79b9_u64;
            let mut next = move |bound: usize| {
                state = state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
                ((state >> 33) as usize) % bound
            };

            for _ in 0..60 {
                // a pool of 4 random tries over short paths
                let pool: Vec<PathMap<()>> = (0..4)
                    .map(|_| {
                        let n = 1 + next(6);
                        let mut m = PathMap::new();
                        for _ in 0..n {
                            let len = 1 + next(3);
                            let path: Vec<u8> = (0..len).map(|_| next(4) as u8).collect();
                            m.insert(&path[..], ());
                        }
                        m
                    })
                    .collect();

                let n_clauses = 1 + next(3);
                let shape: Vec<Vec<usize>> = (0..n_clauses)
                    .map(|_| (0..1 + next(3)).map(|_| next(pool.len())).collect())
                    .collect();
                let clauses: Vec<Vec<&PathMap<()>>> = shape
                    .iter()
                    .map(|clause| clause.iter().map(|&i| &pool[i]).collect())
                    .collect();
                let clause_slices: Vec<&[&PathMap<()>]> =
                    clauses.iter().map(|c| c.as_slice()).collect();

                assert_agrees(&clause_slices[..]);
            }
        }

        /// Pins the divergence rather than hiding it: the reference REJECTS the
        /// empty clause (empty conjunction = the universal pathset, unrepresentable),
        /// while the fused engine treats it as the empty set.
        #[test]
        fn empty_clause_divergence_is_pinned() {
            let trie1 = map(SMALL_TRIE_1);

            assert_eq!(
                evaluate_pathmap_dnf(&[&[&trie1], &[]]).unwrap_err(),
                DnfPathSetError::EmptyClause { clause_index: 1 }
            );

            let mut out = PathMap::new();
            let mut z1 = [trie1.read_zipper()];
            let mut z1_refs: Vec<_> = z1.iter_mut().collect();
            let mut empty_refs: Vec<&mut pathmap::zipper::ReadZipperUntracked<()>> = Vec::new();
            zipper_merge_dnf(
                &mut [&mut z1_refs[..], &mut empty_refs[..]],
                &mut out.write_zipper(),
            );
            // The empty clause contributes the empty set to the union, so the
            // result is exactly the other clause -- not TOP, and not an error.
            assert_eq!(
                out.val_count(),
                trie1.val_count(),
                "fused engine treats the empty clause as an empty contribution"
            );
        }
    }
}
