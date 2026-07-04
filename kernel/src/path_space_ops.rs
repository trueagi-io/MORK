use pathmap::PathMap;

/// Keeps accepted paths that have no accepted strict prefix: the prefix-minimal
/// antichain.
///
/// This is a finite-pathset reference oracle. Its in-tree counterpart is
/// `Space::prefix_subsumption`, whose self-representatives are exactly this
/// antichain; the differential test below seals the two against each other. It
/// intentionally materializes sorted path lists (the dumbest correct thing), so
/// it is a semantic target for zipper implementations rather than a hot path.
pub fn prefix_minimal_values(map: &PathMap<()>) -> PathMap<()> {
    let mut minimal = Vec::<Vec<u8>>::new();
    for path in sorted_paths(map) {
        if !minimal.iter().any(|prefix| path.starts_with(prefix)) {
            minimal.push(path);
        }
    }
    paths_to_map(&minimal)
}

/// Keeps accepted paths that have no accepted strict extension: the
/// prefix-maximal antichain (the dual of [`prefix_minimal_values`]). No in-tree
/// operation computes this yet; the oracle pins the semantics ahead of one.
pub fn prefix_maximal_values(map: &PathMap<()>) -> PathMap<()> {
    let paths = sorted_paths(map);
    let maximal = paths
        .iter()
        .enumerate()
        .filter_map(|(index, path)| {
            let has_extension = paths
                .get(index + 1)
                .is_some_and(|next| is_strict_prefix(path, next));
            (!has_extension).then_some(path.clone())
        })
        .collect::<Vec<_>>();
    paths_to_map(&maximal)
}

/// Computes the prefix-maximal common-prefix witnesses between accepted paths:
/// the longest common prefix of every left/right pair, reduced to the
/// prefix-maximal set. Deliberately pairwise and finite, a reference for a
/// future shared-structure (trie-intersection-by-prefix) operation.
pub fn shared_prefix_witnesses(left: &PathMap<()>, right: &PathMap<()>) -> PathMap<()> {
    let left_paths = sorted_paths(left);
    let right_paths = sorted_paths(right);
    let mut witnesses = PathMap::new();

    for left_path in &left_paths {
        for right_path in &right_paths {
            let len = common_prefix_len(left_path, right_path);
            witnesses.insert(&left_path[..len], ());
        }
    }

    prefix_maximal_values(&witnesses)
}

fn sorted_paths(map: &PathMap<()>) -> Vec<Vec<u8>> {
    let mut paths = Vec::new();
    map.for_each_value(|path, _| paths.push(path.to_vec()));
    paths.sort();
    paths.dedup();
    paths
}

fn paths_to_map(paths: &[Vec<u8>]) -> PathMap<()> {
    let mut map = PathMap::new();
    for path in paths {
        map.insert(path, ());
    }
    map
}

fn is_strict_prefix(prefix: &[u8], path: &[u8]) -> bool {
    prefix.len() < path.len() && path.starts_with(prefix)
}

fn common_prefix_len(left: &[u8], right: &[u8]) -> usize {
    left.iter()
        .zip(right.iter())
        .take_while(|(left, right)| left == right)
        .count()
}

#[cfg(test)]
mod tests {
    use super::*;

    type Paths = &'static [&'static [u8]];

    fn map(paths: Paths) -> PathMap<()> {
        PathMap::from_iter(paths.iter().copied())
    }

    fn paths(map: &PathMap<()>) -> Vec<Vec<u8>> {
        sorted_paths(map)
    }

    #[test]
    fn prefix_minimal_values_stop_below_accepted_ancestor() {
        let source = map(&[b"foo", b"foo/bar", b"foo/bar/baz", b"other"]);

        assert_eq!(
            paths(&prefix_minimal_values(&source)),
            vec![b"foo".to_vec(), b"other".to_vec()]
        );
    }

    #[test]
    fn prefix_maximal_values_keep_deepest_accepted_descendants() {
        let source = map(&[b"foo", b"foo/bar", b"foo/bar/baz", b"other"]);

        assert_eq!(
            paths(&prefix_maximal_values(&source)),
            vec![b"foo/bar/baz".to_vec(), b"other".to_vec()]
        );
    }

    #[test]
    fn empty_value_subsumes_and_is_not_instantiated_when_descendant_exists() {
        let source = map(&[b"", b"a", b"ab"]);

        assert_eq!(
            paths(&prefix_minimal_values(&source)),
            vec![Vec::<u8>::new()]
        );
        assert_eq!(paths(&prefix_maximal_values(&source)), vec![b"ab".to_vec()]);
    }

    #[test]
    fn shared_prefix_witnesses_keep_maximal_common_prefixes() {
        let left = map(&[b"alpha/red", b"beta"]);
        let right = map(&[b"alpha/blue", b"betamax"]);

        assert_eq!(
            paths(&shared_prefix_witnesses(&left, &right)),
            vec![b"alpha/".to_vec(), b"beta".to_vec()]
        );
    }

    #[test]
    fn shared_prefix_witnesses_can_return_empty_root_witness() {
        let left = map(&[b"alpha"]);
        let right = map(&[b"beta"]);

        assert_eq!(
            paths(&shared_prefix_witnesses(&left, &right)),
            vec![Vec::<u8>::new()]
        );
    }

    /// Differential seal against the in-tree operation: the self-representatives
    /// of `Space::prefix_subsumption` (out[i] == i) are exactly the
    /// prefix-minimal antichain this oracle computes.
    mod differential {
        use super::*;
        use crate::space::Space;

        fn subsumption_representatives(paths: &[Vec<u8>]) -> Vec<Vec<u8>> {
            let prefix_refs: Vec<&[u8]> = paths.iter().map(|p| p.as_slice()).collect();
            let out = Space::prefix_subsumption(&prefix_refs);
            let mut reps: Vec<Vec<u8>> = out
                .iter()
                .enumerate()
                .filter_map(|(i, &rep)| (rep == i).then(|| paths[i].clone()))
                .collect();
            reps.sort();
            reps.dedup();
            reps
        }

        fn assert_agrees(input: Paths) {
            let source = map(input);
            let oracle = paths(&prefix_minimal_values(&source));
            let engine = subsumption_representatives(&sorted_paths(&source));
            assert_eq!(oracle, engine, "antichain diverges on {input:?}");
        }

        #[test]
        fn engine_representatives_match_the_oracle_on_fixed_shapes() {
            assert_agrees(&[b"foo", b"foo/bar", b"foo/bar/baz", b"other"]);
            assert_agrees(&[b"", b"a", b"ab"]);
            assert_agrees(&[b"a", b"b", b"c"]);
            assert_agrees(&[b"ab", b"abc", b"abd", b"ab"]);
        }

        #[test]
        fn engine_representatives_match_the_oracle_on_random_pathsets() {
            // deterministic LCG; no time or thread dependence
            let mut state = 0x51ce_b00b_u64;
            let mut next = move |bound: usize| {
                state = state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
                ((state >> 33) as usize) % bound
            };

            for _ in 0..80 {
                let n = 1 + next(8);
                let mut input = PathMap::new();
                for _ in 0..n {
                    let len = next(4); // includes the empty path
                    let path: Vec<u8> = (0..len).map(|_| next(3) as u8).collect();
                    input.insert(&path[..], ());
                }

                let oracle = paths(&prefix_minimal_values(&input));
                let engine = subsumption_representatives(&sorted_paths(&input));
                assert_eq!(oracle, engine, "antichain diverges on random pathset");
            }
        }
    }
}
