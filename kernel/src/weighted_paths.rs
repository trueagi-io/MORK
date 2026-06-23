use std::collections::BTreeMap;

use pathmap::morphisms::Catamorphism;
use pathmap::zipper::{Zipper, ZipperAbsolutePath, ZipperIteration, ZipperValues};
use pathmap::PathMap;

/// Derived weighted index over encoded MORK paths.
///
/// This keeps weights outside the authoritative `PathMap<()>` atom store. It is
/// intended as the safe version of the `ws` experiment from the iCog fork: a
/// future sink can maintain this sidecar without changing byte-path semantics.
#[derive(Clone, Debug, Default)]
pub struct WeightedPathIndex {
    weights: PathMap<i64>,
    total_positive_weight: u64,
    updates: usize,
}

/// Read-only counters for a [`WeightedPathIndex`].
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct WeightedPathStats {
    /// Number of retained non-zero weighted paths.
    pub entries: usize,
    /// Number of retained paths with positive sampling weight.
    pub positive_entries: usize,
    /// Number of retained paths with zero-or-negative signed weight.
    pub non_positive_entries: usize,
    /// Sum of positive weights visible to weighted selection.
    pub total_positive_weight: u64,
    /// Number of explicit set/delta operations applied to this sidecar.
    pub updates: usize,
}

/// Aggregate positive-weight snapshot for structural descent.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct WeightedSelectionTree {
    total_positive_weight: u64,
    nodes: BTreeMap<Vec<u8>, WeightedSelectionNode>,
}

/// Read-only counters for a [`WeightedSelectionTree`].
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct WeightedSelectionTreeStats {
    /// Structural trie positions retained in the aggregate snapshot.
    pub nodes: usize,
    /// Child edges retained across all aggregate nodes.
    pub child_edges: usize,
    /// Nodes with a positive value at the exact node path.
    pub positive_value_nodes: usize,
    /// Sum of positive weights visible to weighted selection.
    pub total_positive_weight: u64,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct WeightedSelectionNode {
    self_weight: u64,
    children: Box<[(u8, u64)]>,
}

impl WeightedPathIndex {
    /// Creates an empty weighted sidecar.
    pub fn new() -> Self {
        Self::default()
    }

    /// Returns the signed weight stored for `path`, or zero when absent.
    pub fn weight(&self, path: &[u8]) -> i64 {
        self.weights.get_val_at(path).copied().unwrap_or(0)
    }

    /// Returns the total positive weight used by [`select_by_offset`](Self::select_by_offset).
    pub fn total_positive_weight(&self) -> u64 {
        self.total_positive_weight
    }

    /// Sets the signed weight for `path`.
    ///
    /// Zero removes the sidecar entry. Negative values are retained as signed
    /// maintenance state, but are ignored by weighted selection.
    pub fn set_weight(&mut self, path: &[u8], weight: i64) {
        let previous = self.weight(path);
        self.update_total(previous, weight);

        if weight == 0 {
            self.weights.remove(path);
        } else {
            self.weights.insert(path, weight);
        }

        self.updates += 1;
    }

    /// Adds `delta` to the signed weight for `path`.
    ///
    /// The addition saturates at the `i64` bounds so malformed or adversarial
    /// updates cannot overflow debug builds.
    pub fn apply_delta(&mut self, path: &[u8], delta: i64) {
        let previous = self.weight(path);
        self.set_weight(path, previous.saturating_add(delta));
    }

    /// Selects the path containing `offset` in cumulative positive-weight order.
    ///
    /// `offset` is zero-based and must be smaller than
    /// [`total_positive_weight`](Self::total_positive_weight). Paths are visited
    /// in the `PathMap` value iteration order, which is deterministic for a
    /// fixed set of encoded paths.
    pub fn select_by_offset(&self, offset: u64) -> Option<Vec<u8>> {
        if offset >= self.total_positive_weight {
            return None;
        }

        let mut remaining = offset;
        let mut zipper = self.weights.read_zipper();

        if let Some(path) = select_here(&zipper, &mut remaining) {
            return Some(path);
        }

        while zipper.to_next_val() {
            if let Some(path) = select_here(&zipper, &mut remaining) {
                return Some(path);
            }
        }

        None
    }

    /// Builds a subtree-aggregate snapshot for repeated weighted selections.
    ///
    /// This is the sidecar-safe version of the iCog `btm_i32_ws_test` branch's
    /// weighted traversal idea: aggregate weights live outside the authoritative
    /// atom `PathMap<()>`, and selection can descend by child totals rather than
    /// scanning every weighted value for every sample.
    pub fn selection_tree(&self) -> WeightedSelectionTree {
        WeightedSelectionTree::from_weights(&self.weights)
    }

    /// Selects through a freshly built aggregate snapshot.
    ///
    /// Prefer [`selection_tree`](Self::selection_tree) when drawing several
    /// samples from the same weights.
    pub fn select_by_offset_tree(&self, offset: u64) -> Option<Vec<u8>> {
        self.selection_tree().select_by_offset(offset)
    }

    /// Returns sidecar counters without exposing the retained path data.
    pub fn stats(&self) -> WeightedPathStats {
        let mut stats = WeightedPathStats {
            total_positive_weight: self.total_positive_weight,
            updates: self.updates,
            ..WeightedPathStats::default()
        };

        self.weights.for_each_value(|_, &weight| {
            stats.entries += 1;
            if weight > 0 {
                stats.positive_entries += 1;
            } else {
                stats.non_positive_entries += 1;
            }
        });

        stats
    }

    fn update_total(&mut self, previous: i64, next: i64) {
        let previous_positive = positive_weight(previous);
        let next_positive = positive_weight(next);

        if next_positive >= previous_positive {
            self.total_positive_weight = self
                .total_positive_weight
                .saturating_add(next_positive - previous_positive);
        } else {
            self.total_positive_weight -= previous_positive - next_positive;
        }
    }
}

impl WeightedSelectionTree {
    fn from_weights(weights: &PathMap<i64>) -> Self {
        let mut nodes = BTreeMap::new();
        let total_positive_weight = weights.read_zipper().into_cata_side_effect(
            |mask, children: &mut [u64], value, path| {
                let self_weight = value.copied().map(positive_weight).unwrap_or(0);
                let mut total_weight = self_weight;
                let children = mask
                    .iter()
                    .zip(children.iter().copied())
                    .map(|(byte, child_total)| {
                        total_weight = total_weight.saturating_add(child_total);
                        (byte, child_total)
                    })
                    .collect::<Vec<_>>()
                    .into_boxed_slice();

                nodes.insert(
                    path.to_vec(),
                    WeightedSelectionNode {
                        self_weight,
                        children,
                    },
                );

                total_weight
            },
        );

        Self {
            total_positive_weight,
            nodes,
        }
    }

    /// Returns the total positive weight represented by this snapshot.
    pub fn total_positive_weight(&self) -> u64 {
        self.total_positive_weight
    }

    /// Selects the path containing `offset` in cumulative positive-weight order
    /// by descending subtree aggregates.
    pub fn select_by_offset(&self, offset: u64) -> Option<Vec<u8>> {
        if offset >= self.total_positive_weight {
            return None;
        }

        let mut remaining = offset;
        let mut path = Vec::new();

        loop {
            let node = self.nodes.get(path.as_slice())?;
            if remaining < node.self_weight {
                return Some(path);
            }
            remaining -= node.self_weight;

            let mut descended = false;
            for &(byte, child_total) in node.children.iter() {
                if child_total == 0 {
                    continue;
                }
                if remaining < child_total {
                    path.push(byte);
                    descended = true;
                    break;
                }
                remaining -= child_total;
            }

            if !descended {
                return None;
            }
        }
    }

    /// Returns aggregate snapshot counters.
    pub fn stats(&self) -> WeightedSelectionTreeStats {
        WeightedSelectionTreeStats {
            nodes: self.nodes.len(),
            child_edges: self.nodes.values().map(|node| node.children.len()).sum(),
            positive_value_nodes: self
                .nodes
                .values()
                .filter(|node| node.self_weight > 0)
                .count(),
            total_positive_weight: self.total_positive_weight,
        }
    }
}

fn positive_weight(weight: i64) -> u64 {
    if weight > 0 {
        weight as u64
    } else {
        0
    }
}

fn select_here<Z>(zipper: &Z, remaining: &mut u64) -> Option<Vec<u8>>
where
    Z: Zipper + ZipperAbsolutePath + ZipperValues<i64>,
{
    let weight = positive_weight(*zipper.val()?);
    if weight == 0 {
        return None;
    }

    if *remaining < weight {
        return Some(zipper.path().to_vec());
    }

    *remaining -= weight;
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn select_by_offset_returns_paths_by_positive_weight_ranges() {
        let mut index = WeightedPathIndex::new();
        index.set_weight(b"foo", 2);
        index.set_weight(b"bar", 1);
        index.set_weight(b"zap", 3);

        assert_eq!(index.total_positive_weight(), 6);
        assert_eq!(index.select_by_offset(0).as_deref(), Some(&b"bar"[..]));
        assert_eq!(index.select_by_offset(1).as_deref(), Some(&b"foo"[..]));
        assert_eq!(index.select_by_offset(2).as_deref(), Some(&b"foo"[..]));
        assert_eq!(index.select_by_offset(3).as_deref(), Some(&b"zap"[..]));
        assert_eq!(index.select_by_offset(5).as_deref(), Some(&b"zap"[..]));
        assert_eq!(index.select_by_offset(6), None);
    }

    #[test]
    fn apply_delta_removes_zero_weight_entries_and_updates_total() {
        let mut index = WeightedPathIndex::new();
        index.apply_delta(b"foo", 5);
        index.apply_delta(b"foo", -2);
        index.apply_delta(b"foo", -3);

        assert_eq!(index.weight(b"foo"), 0);
        assert_eq!(index.total_positive_weight(), 0);
        assert_eq!(index.stats().entries, 0);
    }

    #[test]
    fn negative_weights_are_retained_but_not_selected() {
        let mut index = WeightedPathIndex::new();
        index.set_weight(b"cold", -4);
        index.set_weight(b"hot", 2);

        assert_eq!(index.weight(b"cold"), -4);
        assert_eq!(index.select_by_offset(0).as_deref(), Some(&b"hot"[..]));

        let stats = index.stats();
        assert_eq!(stats.entries, 2);
        assert_eq!(stats.positive_entries, 1);
        assert_eq!(stats.non_positive_entries, 1);
        assert_eq!(stats.total_positive_weight, 2);
    }

    #[test]
    fn selection_tree_matches_linear_selection_with_prefix_values() {
        let mut index = WeightedPathIndex::new();
        index.set_weight(b"a", 2);
        index.set_weight(b"ab", 3);
        index.set_weight(b"ac", 1);
        index.set_weight(b"b", -10);
        index.set_weight(b"bd", 4);

        let tree = index.selection_tree();

        assert_eq!(tree.total_positive_weight(), index.total_positive_weight());
        for offset in 0..index.total_positive_weight() {
            assert_eq!(
                tree.select_by_offset(offset),
                index.select_by_offset(offset),
                "offset {offset}",
            );
        }
        assert_eq!(tree.select_by_offset(index.total_positive_weight()), None);

        let stats = tree.stats();
        assert_eq!(stats.positive_value_nodes, 4);
        assert_eq!(stats.total_positive_weight, 10);
        assert!(stats.nodes >= stats.positive_value_nodes);
        assert!(stats.child_edges >= 4);
    }
}
