use pathmap::PathMap;

/// Keeps accepted paths that have no accepted strict prefix.
///
/// This is a finite-pathset reference helper for the MORK `^space`
/// subsumption operation. It intentionally materializes path lists, so it is a
/// semantic target for future zipper/residual-DAG implementations rather than a
/// hot-path kernel.
pub fn prefix_minimal_values(map: &PathMap<()>) -> PathMap<()> {
    let mut minimal = Vec::<Vec<u8>>::new();
    for path in sorted_paths(map) {
        if !minimal.iter().any(|prefix| path.starts_with(prefix)) {
            minimal.push(path);
        }
    }
    paths_to_map(&minimal)
}

/// Keeps accepted paths that have no accepted strict extension.
///
/// This is a finite-pathset reference helper for the MORK `v space`
/// instantiation operation.
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

/// Computes the prefix-maximal common-prefix witnesses between accepted paths.
///
/// The implementation is deliberately pairwise and finite. It mirrors the
/// archive's `sharing` semantics as a compact reference oracle: collect the
/// longest common prefix for every left/right path pair, then keep only the
/// prefix-maximal witnesses.
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
}
