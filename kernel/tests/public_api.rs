use mork::weighted_paths::{
    WeightedPathError, WeightedPathIndex, WeightedPathStats, WeightedSelectionTreeStats,
};

#[test]
fn weighted_path_api_exposes_sidecar_and_stats() -> Result<(), WeightedPathError> {
    let mut index = WeightedPathIndex::new();

    index.set_weight(b"public", 2)?;

    let stats: WeightedPathStats = index.stats();
    assert_eq!(index.weight(b"missing"), 0);
    assert_eq!(index.total_positive_weight(), 2);
    assert_eq!(index.select_by_offset(0).as_deref(), Some(&b"public"[..]));
    assert_eq!(
        stats,
        WeightedPathStats {
            entries: 1,
            positive_entries: 1,
            non_positive_entries: 0,
            total_positive_weight: 2,
            updates: 1,
        }
    );
    Ok(())
}

#[test]
fn weighted_path_api_exposes_selection_tree() -> Result<(), WeightedPathError> {
    let mut index = WeightedPathIndex::new();

    index.set_weight(b"a", 2)?;
    index.set_weight(b"ab", 3)?;

    let tree = index.selection_tree()?;
    let stats: WeightedSelectionTreeStats = tree.stats();

    assert_eq!(tree.total_positive_weight(), 5);
    assert_eq!(tree.select_by_offset(0).as_deref(), Some(&b"a"[..]));
    assert_eq!(tree.select_by_offset(2).as_deref(), Some(&b"ab"[..]));
    assert_eq!(index.select_by_offset_tree(4)?.as_deref(), Some(&b"ab"[..]));
    assert_eq!(stats.total_positive_weight, 5);
    assert_eq!(stats.positive_value_nodes, 2);
    Ok(())
}
