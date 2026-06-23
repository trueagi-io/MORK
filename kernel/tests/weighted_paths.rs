use mork::weighted_paths::{WeightedPathIndex, WeightedPathStats};

#[test]
fn weighted_path_index_keeps_weights_outside_authoritative_atom_store() {
    let mut index = WeightedPathIndex::new();

    index.apply_delta(b"(foo 1)", 4);
    index.apply_delta(b"(bar 1)", 1);
    index.apply_delta(b"(foo 1)", -1);

    assert_eq!(index.weight(b"(foo 1)"), 3);
    assert_eq!(index.total_positive_weight(), 4);
    assert_eq!(index.select_by_offset(0).as_deref(), Some(&b"(bar 1)"[..]));
    assert_eq!(index.select_by_offset(1).as_deref(), Some(&b"(foo 1)"[..]));

    assert_eq!(
        index.stats(),
        WeightedPathStats {
            entries: 2,
            positive_entries: 2,
            non_positive_entries: 0,
            total_positive_weight: 4,
            updates: 3,
        }
    );
}
