use std::collections::BTreeMap;

use crate::term_identity::{FactId, TermId, TermIdentitySidecar, TermKind};

/// Physical argument-order sidecar for relation-like facts.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ArrangementDescriptor {
    /// Relation/functor term at child position 0.
    pub relation: TermId,
    /// Number of relation arguments, excluding the relation/functor child.
    pub argument_count: u8,
    /// Argument positions used as the key, zero-based after the relation child.
    pub key_order: Box<[u8]>,
}

impl ArrangementDescriptor {
    /// Creates a descriptor after validating the key order.
    pub fn new(
        relation: TermId,
        argument_count: u8,
        key_order: impl Into<Box<[u8]>>,
    ) -> Result<Self, ArrangementError> {
        let key_order = key_order.into();
        validate_key_order(argument_count, &key_order)?;

        Ok(Self {
            relation,
            argument_count,
            key_order,
        })
    }
}

/// One arranged fact row.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ArrangementRow {
    /// Complete fact identity.
    pub fact: FactId,
    /// Root term for the fact.
    pub root: TermId,
}

/// Snapshot-local arrangement index.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ArrangementIndex {
    descriptor: ArrangementDescriptor,
    rows_by_key: BTreeMap<Box<[TermId]>, Vec<ArrangementRow>>,
    stats: ArrangementStats,
}

/// Counters for arrangement construction and lookup.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct ArrangementStats {
    /// Complete fact roots inspected during build.
    pub facts_scanned: usize,
    /// Facts whose root matched the relation and arity.
    pub rows: usize,
    /// Distinct arranged keys.
    pub distinct_keys: usize,
    /// Rows returned by prefix lookups.
    pub prefix_rows_returned: usize,
    /// Prefix lookup calls.
    pub prefix_lookups: usize,
}

/// Errors from arrangement construction.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ArrangementError {
    /// The relation term is absent from the term sidecar.
    UnknownRelation { relation: TermId },
    /// A key position is outside the declared argument count.
    InvalidKeyPosition { position: u8, argument_count: u8 },
    /// Duplicate key positions would not define a useful arrangement order.
    DuplicateKeyPosition { position: u8 },
    /// A fact referenced a missing term record.
    UnknownTerm { term: TermId },
    /// Encoded arity would overflow when adding the relation/functor child.
    ArityOverflow { argument_count: u8 },
}

impl ArrangementIndex {
    /// Builds a derived arrangement from a term snapshot.
    pub fn build(
        sidecar: &TermIdentitySidecar,
        descriptor: ArrangementDescriptor,
    ) -> Result<Self, ArrangementError> {
        if sidecar.get_term(descriptor.relation).is_none() {
            return Err(ArrangementError::UnknownRelation {
                relation: descriptor.relation,
            });
        }

        let encoded_arity =
            descriptor
                .argument_count
                .checked_add(1)
                .ok_or(ArrangementError::ArityOverflow {
                    argument_count: descriptor.argument_count,
                })?;
        let mut stats = ArrangementStats::default();
        let mut rows_by_key: BTreeMap<Box<[TermId]>, Vec<ArrangementRow>> = BTreeMap::new();

        for fact in sidecar.facts() {
            stats.facts_scanned += 1;
            let Some(root) = sidecar.get_term(fact.root) else {
                return Err(ArrangementError::UnknownTerm { term: fact.root });
            };
            if root.kind
                != (TermKind::Application {
                    arity: encoded_arity,
                })
            {
                continue;
            }
            let children = root.children();
            if children.first().copied() != Some(descriptor.relation) {
                continue;
            }

            let key = descriptor
                .key_order
                .iter()
                .map(|&position| children[usize::from(position) + 1])
                .collect::<Vec<_>>()
                .into_boxed_slice();
            rows_by_key.entry(key).or_default().push(ArrangementRow {
                fact: fact.id,
                root: fact.root,
            });
            stats.rows += 1;
        }

        stats.distinct_keys = rows_by_key.len();
        Ok(Self {
            descriptor,
            rows_by_key,
            stats,
        })
    }

    /// Arrangement descriptor.
    pub fn descriptor(&self) -> &ArrangementDescriptor {
        &self.descriptor
    }

    /// Returns counters accumulated by build and lookup calls.
    pub fn stats(&self) -> ArrangementStats {
        self.stats
    }

    /// Returns all rows whose arranged key starts with `prefix`.
    pub fn seek_prefix(&mut self, prefix: &[TermId]) -> Vec<ArrangementRow> {
        self.stats.prefix_lookups += 1;

        let mut rows = Vec::new();
        for (key, key_rows) in self.rows_by_key.range(prefix.to_vec().into_boxed_slice()..) {
            if !key.starts_with(prefix) {
                break;
            }
            rows.extend_from_slice(key_rows);
        }

        self.stats.prefix_rows_returned += rows.len();
        rows
    }

    /// Exact arranged-key lookup.
    pub fn get_exact(&self, key: &[TermId]) -> &[ArrangementRow] {
        self.rows_by_key.get(key).map(Vec::as_slice).unwrap_or(&[])
    }
}

fn validate_key_order(argument_count: u8, key_order: &[u8]) -> Result<(), ArrangementError> {
    let mut seen = 0u64;
    for &position in key_order {
        if position >= argument_count {
            return Err(ArrangementError::InvalidKeyPosition {
                position,
                argument_count,
            });
        }
        let bit = 1u64 << position;
        if seen & bit != 0 {
            return Err(ArrangementError::DuplicateKeyPosition { position });
        }
        seen |= bit;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::space::Space;
    use crate::term_identity::TermIdentitySidecar;
    use std::collections::BTreeSet;

    fn encoded_roots(
        sidecar: &TermIdentitySidecar,
        rows: impl IntoIterator<Item = ArrangementRow>,
    ) -> BTreeSet<Vec<u8>> {
        rows.into_iter()
            .map(|row| sidecar.get_term(row.root).unwrap().encoded().to_vec())
            .collect()
    }

    fn encoded_expr(space: &mut Space, expr: &'static str) -> Vec<u8> {
        let expr = crate::expr!(space, expr);
        unsafe { expr.span().as_ref().unwrap() }.to_vec()
    }

    #[test]
    fn suffix_bound_arrangement_matches_product_query_roots() {
        let mut space = Space::new();
        space
            .add_all_sexpr(
                br#"
(edge Alice Bob)
(edge Carol Bob)
(edge Alice Dave)
(edge Eve Frank)
(note Bob Alice)
"#,
            )
            .unwrap();

        let mut sidecar = TermIdentitySidecar::new();
        sidecar.extend_from_pathmap(&space.btm).unwrap();
        let edge = sidecar
            .term_id_for_encoded(&encoded_expr(&mut space, "edge"))
            .unwrap();
        let bob = sidecar
            .term_id_for_encoded(&encoded_expr(&mut space, "Bob"))
            .unwrap();
        let alice = sidecar
            .term_id_for_encoded(&encoded_expr(&mut space, "Alice"))
            .unwrap();

        let descriptor = ArrangementDescriptor::new(edge, 2, [1, 0]).unwrap();
        let mut arrangement = ArrangementIndex::build(&sidecar, descriptor).unwrap();
        let bob_rows = arrangement.seek_prefix(&[bob]);
        let exact_rows = arrangement.get_exact(&[bob, alice]);

        let product_pattern = crate::expr!(space, "[2] , [3] edge $ Bob");
        let mut product_roots = BTreeSet::new();
        let product_count = Space::query_multi(&space.btm, product_pattern, |_, loc| {
            let span = unsafe { loc.span().as_ref().unwrap() };
            product_roots.insert(span.to_vec());
            true
        });

        assert_eq!(product_count, 2);
        assert_eq!(encoded_roots(&sidecar, bob_rows), product_roots);
        assert_eq!(exact_rows.len(), 1);

        let stats = arrangement.stats();
        assert_eq!(stats.rows, 4);
        assert_eq!(stats.prefix_lookups, 1);
        assert_eq!(stats.prefix_rows_returned, 2);
    }

    #[test]
    fn descriptor_rejects_invalid_key_orders() {
        assert_eq!(
            ArrangementDescriptor::new(TermId(0), 2, [2]),
            Err(ArrangementError::InvalidKeyPosition {
                position: 2,
                argument_count: 2,
            })
        );
        assert_eq!(
            ArrangementDescriptor::new(TermId(0), 2, [1, 1]),
            Err(ArrangementError::DuplicateKeyPosition { position: 1 })
        );
    }
}
