use mork::weighted_paths::{WeightedPathIndex, WeightedPathStats};

#[test]
fn weighted_path_api_exposes_sidecar_and_stats() {
    let mut index = WeightedPathIndex::new();

    index.set_weight(b"public", 2);

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
}
