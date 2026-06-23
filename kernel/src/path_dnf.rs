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
    /// Total number of conjunctive factors across all clauses.
    pub factors: usize,
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
    /// Sum of input factor value counts across all clause positions.
    pub factor_input_values: usize,
    /// Sum of materialized clause-result value counts before final union.
    pub clause_output_values: usize,
    /// Clause-result values eliminated by duplicate-removing final union.
    pub duplicate_clause_values: usize,
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
    /// Whether the final duplicate-eliminating output map was materialized.
    pub final_output_materialized: bool,
}

/// Errors for finite DNF pathset evaluation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DnfPathSetError {
    /// An empty conjunction would denote the universal pathset, which is not a
    /// finite `PathMap<()>` value.
    EmptyClause { clause_index: usize },
}

/// Evaluates a finite pathset expression in disjunctive normal form.
///
/// Each inner slice is a conjunction evaluated with [`PathMap::meet`]. Clause
/// results are then combined with [`PathMap::join`]. This is a guarded semantic
/// adapter for evaluating the PathMap `origin/dnf` zipper-merge idea without
/// depending on that branch's broader zipper and grafting API changes.
pub fn evaluate_pathmap_dnf(
    clauses: &[&[&PathMap<()>]],
) -> Result<DnfPathSetResult, DnfPathSetError> {
    let mut stats = DnfPathSetStats {
        clauses: clauses.len(),
        ..DnfPathSetStats::default()
    };
    let mut result = PathMap::new();
    let mut has_result = false;
    let mut distinct_factor_refs = Vec::new();

    for (clause_index, clause) in clauses.iter().enumerate() {
        let (clause_map, _) =
            evaluate_clause(clause_index, clause, &mut stats, &mut distinct_factor_refs)?;

        if has_result {
            result = result.join(&clause_map);
            stats.join_ops += 1;
        } else {
            result = clause_map;
            has_result = true;
        }
        stats.peak_result_values = stats.peak_result_values.max(result.val_count());
    }
    stats.duplicate_clause_values = stats
        .clause_output_values
        .saturating_sub(result.val_count());

    Ok(DnfPathSetResult { map: result, stats })
}

/// Checks whether a finite DNF pathset is non-empty without materializing the
/// final duplicate-eliminating union.
pub fn evaluate_pathmap_dnf_exists(
    clauses: &[&[&PathMap<()>]],
) -> Result<DnfPathSetExistenceResult, DnfPathSetError> {
    let mut stats = DnfPathSetStats {
        clauses: clauses.len(),
        ..DnfPathSetStats::default()
    };
    let mut distinct_factor_refs = Vec::new();

    for (clause_index, clause) in clauses.iter().enumerate() {
        let (_, clause_values) =
            evaluate_clause(clause_index, clause, &mut stats, &mut distinct_factor_refs)?;

        if clause_values > 0 {
            stats.short_circuit_skipped_clauses = clauses.len().saturating_sub(clause_index + 1);

            return Ok(DnfPathSetExistenceResult {
                exists: true,
                stats,
                final_output_materialized: false,
            });
        }
    }

    Ok(DnfPathSetExistenceResult {
        exists: false,
        stats,
        final_output_materialized: false,
    })
}

fn evaluate_clause(
    clause_index: usize,
    clause: &[&PathMap<()>],
    stats: &mut DnfPathSetStats,
    distinct_factor_refs: &mut Vec<*const ()>,
) -> Result<(PathMap<()>, usize), DnfPathSetError> {
    if clause.is_empty() {
        return Err(DnfPathSetError::EmptyClause { clause_index });
    }

    record_clause_inputs(stats, distinct_factor_refs, clause);
    let clause_map = materialize_clause(clause, stats);
    let clause_values = record_clause_output(stats, &clause_map);

    Ok((clause_map, clause_values))
}

fn record_clause_inputs(
    stats: &mut DnfPathSetStats,
    distinct_factor_refs: &mut Vec<*const ()>,
    clause: &[&PathMap<()>],
) {
    stats.clauses_evaluated += 1;
    stats.factors += clause.len();

    if clause.len() == 1 {
        stats.singleton_clauses += 1;
    } else {
        stats.multi_factor_clauses += 1;
    }

    for factor in clause {
        stats.factor_input_values += factor.val_count();
        let factor_ref = std::ptr::from_ref(*factor).cast::<()>();
        if distinct_factor_refs.contains(&factor_ref) {
            stats.repeated_factor_refs += 1;
        } else {
            distinct_factor_refs.push(factor_ref);
            stats.distinct_factor_refs += 1;
        }
    }
}

fn materialize_clause(clause: &[&PathMap<()>], stats: &mut DnfPathSetStats) -> PathMap<()> {
    let mut clause_map = clause[0].clone();

    for factor in &clause[1..] {
        clause_map = clause_map.meet(factor);
        stats.meet_ops += 1;
    }

    clause_map
}

fn record_clause_output(stats: &mut DnfPathSetStats, clause_map: &PathMap<()>) -> usize {
    let clause_values = clause_map.val_count();

    stats.clause_output_values += clause_values;
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

    fn assert_overlap_stats(stats: DnfPathSetStats, join_ops: usize, peak_result_values: usize) {
        assert_eq!(stats.join_ops, join_ops);
        assert_eq!(stats.distinct_factor_refs, 3);
        assert_eq!(stats.repeated_factor_refs, 1);
        assert_eq!(stats.factor_input_values, 11);
        assert_eq!(stats.clause_output_values, 2);
        assert_eq!(stats.duplicate_clause_values, 0);
        assert_eq!(stats.peak_clause_values, 2);
        assert_eq!(stats.peak_result_values, peak_result_values);
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
        assert_eq!(result.stats.meet_ops, 2);
        assert_eq!(result.stats.join_ops, 0);
        assert_eq!(result.stats.distinct_factor_refs, 3);
        assert_eq!(result.stats.repeated_factor_refs, 0);
        assert_eq!(result.stats.factor_input_values, 9);
        assert_eq!(result.stats.clause_output_values, 0);
        assert_eq!(result.stats.duplicate_clause_values, 0);
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
        assert_eq!(result.stats.meet_ops, 0);
        assert_eq!(result.stats.join_ops, 2);
        assert_eq!(result.stats.distinct_factor_refs, 3);
        assert_eq!(result.stats.repeated_factor_refs, 0);
        assert_eq!(result.stats.factor_input_values, 9);
        assert_eq!(result.stats.clause_output_values, 9);
        assert_eq!(result.stats.duplicate_clause_values, 2);
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
        assert_eq!(result.stats.meet_ops, 2);
        assert_overlap_stats(result.stats, 1, 2);
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
        assert!(!result.final_output_materialized);
        assert_eq!(result.stats.clauses, 3);
        assert_eq!(result.stats.clauses_evaluated, 2);
        assert_eq!(result.stats.short_circuit_skipped_clauses, 1);
        assert_eq!(result.stats.factors, 4);
        assert_eq!(result.stats.singleton_clauses, 1);
        assert_eq!(result.stats.multi_factor_clauses, 1);
        assert_eq!(result.stats.meet_ops, 2);
        assert_overlap_stats(result.stats, 0, 0);
    }
}
