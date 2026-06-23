use std::collections::{BTreeMap, BTreeSet};

use crate::term_identity::TermId;

/// Query variable identifier used by BindingSpace sidecars.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct BindingVar(pub u8);

/// Compact binding row.
pub type BindingRow = Box<[TermId]>;

/// Signed relation over canonical term bindings.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct BindingRelation {
    schema: Box<[BindingVar]>,
    weights: BTreeMap<BindingRow, i64>,
}

/// Errors from relation operations.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BindingRelationError {
    /// Row width did not match relation schema.
    ArityMismatch { expected: usize, actual: usize },
    /// Operation requires equal schemas.
    SchemaMismatch,
    /// Variable was not present in the schema.
    UnknownVariable { variable: BindingVar },
    /// Variable order does not contain exactly the variables in the input.
    InvalidVariableOrder,
}

impl BindingRelation {
    /// Creates an empty relation with the given schema.
    pub fn new(schema: impl Into<Box<[BindingVar]>>) -> Self {
        Self {
            schema: schema.into(),
            weights: BTreeMap::new(),
        }
    }

    /// Relation schema.
    pub fn schema(&self) -> &[BindingVar] {
        &self.schema
    }

    /// Number of retained non-zero rows.
    pub fn len(&self) -> usize {
        self.weights.len()
    }

    /// Returns true when no non-zero rows remain.
    pub fn is_empty(&self) -> bool {
        self.weights.is_empty()
    }

    /// Adds a signed row weight, removing the row when the total reaches zero.
    pub fn add(
        &mut self,
        row: impl Into<BindingRow>,
        weight: i64,
    ) -> Result<(), BindingRelationError> {
        let row = row.into();
        if row.len() != self.schema.len() {
            return Err(BindingRelationError::ArityMismatch {
                expected: self.schema.len(),
                actual: row.len(),
            });
        }

        let entry = self.weights.entry(row).or_default();
        *entry = entry.saturating_add(weight);
        if *entry == 0 {
            self.weights.retain(|_, value| *value != 0);
        }
        Ok(())
    }

    /// Returns the signed weight for `row`, or zero if absent.
    pub fn weight(&self, row: &[TermId]) -> i64 {
        self.weights.get(row).copied().unwrap_or(0)
    }

    /// Iterates all retained rows and weights.
    pub fn rows(&self) -> impl Iterator<Item = (&[TermId], i64)> + '_ {
        self.weights
            .iter()
            .map(|(row, &weight)| (row.as_ref(), weight))
    }

    /// Iterates rows with positive visible weight.
    pub fn positive_rows(&self) -> impl Iterator<Item = &[TermId]> + '_ {
        self.rows()
            .filter_map(|(row, weight)| (weight > 0).then_some(row))
    }

    /// Adds every row from `other`.
    pub fn union_assign(&mut self, other: &Self) -> Result<(), BindingRelationError> {
        if self.schema != other.schema {
            return Err(BindingRelationError::SchemaMismatch);
        }
        for (row, weight) in &other.weights {
            self.add(row.clone(), *weight)?;
        }
        Ok(())
    }

    /// Presence difference: positive rows from `self` that are not visible in
    /// `other`.
    pub fn difference_presence(&self, other: &Self) -> Result<Self, BindingRelationError> {
        if self.schema != other.schema {
            return Err(BindingRelationError::SchemaMismatch);
        }

        let visible_other = other
            .rows()
            .filter_map(|(row, weight)| (weight > 0).then_some(row.to_vec()))
            .collect::<BTreeSet<_>>();
        let mut out = Self::new(self.schema.clone());
        for (row, weight) in self.rows() {
            if weight > 0 && !visible_other.contains(row) {
                out.add(row.to_vec(), weight)?;
            }
        }
        Ok(out)
    }

    fn schema_index(&self, variable: BindingVar) -> Option<usize> {
        self.schema.iter().position(|&value| value == variable)
    }
}

/// Reference natural join over signed relations.
pub fn natural_join(
    left: &BindingRelation,
    right: &BindingRelation,
) -> Result<BindingRelation, BindingRelationError> {
    let common = left
        .schema()
        .iter()
        .copied()
        .filter(|variable| right.schema().contains(variable))
        .collect::<Vec<_>>();
    let right_new = right
        .schema()
        .iter()
        .copied()
        .filter(|variable| !left.schema().contains(variable))
        .collect::<Vec<_>>();

    let mut out_schema = left.schema().to_vec();
    out_schema.extend_from_slice(&right_new);
    let mut out = BindingRelation::new(out_schema);

    let left_common = indexes(left, &common)?;
    let right_common = indexes(right, &common)?;
    let right_new_indexes = indexes(right, &right_new)?;

    let mut right_index: BTreeMap<Vec<TermId>, Vec<(&[TermId], i64)>> = BTreeMap::new();
    for (row, weight) in right.rows() {
        let key = project_key(row, &right_common);
        right_index.entry(key).or_default().push((row, weight));
    }

    for (left_row, left_weight) in left.rows() {
        let key = project_key(left_row, &left_common);
        for (right_row, right_weight) in right_index.get(&key).into_iter().flatten() {
            let mut output = left_row.to_vec();
            output.extend(right_new_indexes.iter().map(|&index| right_row[index]));
            out.add(output, left_weight.saturating_mul(*right_weight))?;
        }
    }

    Ok(out)
}

/// Reference variable-at-a-time Generic Join using leapfrog-style domain
/// intersection. This is a semantic oracle, not a production kernel.
pub fn generic_join(
    relations: &[BindingRelation],
    variable_order: &[BindingVar],
) -> Result<BindingRelation, BindingRelationError> {
    validate_variable_order(relations, variable_order)?;

    let mut out = BindingRelation::new(variable_order.to_vec());
    let mut binding = BTreeMap::<BindingVar, TermId>::new();
    generic_join_recurse(relations, variable_order, 0, &mut binding, &mut out)?;
    Ok(out)
}

/// Result of executing a trie-backed variable-at-a-time join.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TrieJoinResult {
    /// Flat relation in the requested variable order.
    pub relation: BindingRelation,
    /// Physical work counters for the trie-backed executor.
    pub stats: TrieJoinStats,
}

/// Counters from the trie-backed variable-at-a-time join.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct TrieJoinStats {
    /// Input relation indexes constructed for the join.
    pub relation_indexes: usize,
    /// Positive rows retained across all relation indexes.
    pub indexed_rows: usize,
    /// Distinct trie prefixes with outgoing children across all indexes.
    pub trie_nodes: usize,
    /// Variable-domain intersections performed during traversal.
    pub domain_intersections: usize,
    /// Relation domains participating in those intersections.
    pub domain_sources: usize,
    /// Domain values presented to leapfrog intersection.
    pub domain_values: usize,
    /// LFTJ-style domain cursors opened for variable intersections.
    pub domain_cursor_opens: usize,
    /// Monotone seek calls issued against domain cursors.
    pub domain_cursor_seeks: usize,
    /// Next calls issued after a cursor-aligned result is emitted.
    pub domain_cursor_nexts: usize,
    /// Final relation row-weight probes.
    pub weight_lookups: usize,
    /// Positive rows emitted by the join.
    pub output_rows: usize,
}

/// Minimal LFTJ-style cursor over one ordered variable domain.
///
/// This is the physical contract for PathMap/ReadZipper-backed factors:
/// ordered current key, monotone `seek`, linear `next`, and an end marker. The
/// current implementation below adapts in-memory relation trie domains to the
/// same contract.
pub trait BindingDomainCursor {
    /// Current key at this trie depth, or `None` at end.
    fn key(&self) -> Option<TermId>;
    /// Whether the cursor has exhausted its current domain.
    fn at_end(&self) -> bool;
    /// Advance to the next key in the current domain.
    fn next(&mut self);
    /// Advance to the least key greater than or equal to `target`.
    fn seek(&mut self, target: TermId);
}

/// Trie-backed variable-at-a-time join over positive BindingSpace rows.
///
/// This is the first physical LFTJ-style sidecar kernel: each input relation is
/// re-keyed as a trie compatible with the global `variable_order`, then the
/// executor synchronizes the current variable's sorted domains and recurses.
pub fn trie_join(
    relations: &[BindingRelation],
    variable_order: &[BindingVar],
) -> Result<TrieJoinResult, BindingRelationError> {
    validate_variable_order(relations, variable_order)?;

    let mut stats = TrieJoinStats {
        relation_indexes: relations.len(),
        ..TrieJoinStats::default()
    };
    let indexes = relations
        .iter()
        .map(|relation| RelationTrieIndex::build(relation, variable_order))
        .collect::<Result<Vec<_>, _>>()?;
    for index in &indexes {
        stats.indexed_rows += index.weights.len();
        stats.trie_nodes += index.children_by_prefix.len();
    }

    let mut relation = BindingRelation::new(variable_order.to_vec());
    let mut binding = BTreeMap::<BindingVar, TermId>::new();
    trie_join_recurse(
        &indexes,
        variable_order,
        0,
        &mut binding,
        &mut relation,
        &mut stats,
    )?;
    stats.output_rows = relation.positive_rows().count();

    Ok(TrieJoinResult { relation, stats })
}

fn generic_join_recurse(
    relations: &[BindingRelation],
    variable_order: &[BindingVar],
    level: usize,
    binding: &mut BTreeMap<BindingVar, TermId>,
    out: &mut BindingRelation,
) -> Result<(), BindingRelationError> {
    if level == variable_order.len() {
        let mut weight = 1i64;
        for relation in relations {
            let row = relation
                .schema()
                .iter()
                .map(|variable| binding[variable])
                .collect::<Vec<_>>();
            weight = weight.saturating_mul(relation.weight(&row));
        }
        if weight != 0 {
            out.add(
                variable_order
                    .iter()
                    .map(|variable| binding[variable])
                    .collect::<Vec<_>>(),
                weight,
            )?;
        }
        return Ok(());
    }

    let variable = variable_order[level];
    let mut domains = Vec::new();
    for relation in relations {
        let Some(variable_index) = relation.schema_index(variable) else {
            continue;
        };
        let mut domain = relation
            .rows()
            .filter(|(_, weight)| *weight > 0)
            .filter(|(row, _)| {
                relation
                    .schema()
                    .iter()
                    .enumerate()
                    .all(|(index, relation_var)| {
                        binding
                            .get(relation_var)
                            .is_none_or(|bound| row[index] == *bound)
                    })
            })
            .map(|(row, _)| row[variable_index])
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        domain.sort_unstable();
        domains.push(domain);
    }

    for value in leapfrog_intersection(&domains) {
        binding.insert(variable, value);
        generic_join_recurse(relations, variable_order, level + 1, binding, out)?;
    }
    binding.remove(&variable);
    Ok(())
}

#[derive(Clone, Debug)]
struct RelationTrieIndex {
    schema: Box<[BindingVar]>,
    positions: BTreeMap<BindingVar, usize>,
    children_by_prefix: BTreeMap<BindingRow, Box<[TermId]>>,
    weights: BTreeMap<BindingRow, i64>,
}

impl RelationTrieIndex {
    fn build(
        relation: &BindingRelation,
        variable_order: &[BindingVar],
    ) -> Result<Self, BindingRelationError> {
        if has_duplicates(relation.schema()) {
            return Err(BindingRelationError::InvalidVariableOrder);
        }

        let schema = variable_order
            .iter()
            .copied()
            .filter(|variable| relation.schema().contains(variable))
            .collect::<Vec<_>>();
        let source_indexes = indexes(relation, &schema)?;

        let mut child_sets = BTreeMap::<Vec<TermId>, BTreeSet<TermId>>::new();
        let mut weights = BTreeMap::<BindingRow, i64>::new();
        for (row, weight) in relation.rows() {
            if weight <= 0 {
                continue;
            }

            let ordered_row = source_indexes
                .iter()
                .map(|&index| row[index])
                .collect::<Vec<_>>();
            let entry = weights
                .entry(ordered_row.clone().into_boxed_slice())
                .or_default();
            *entry = entry.saturating_add(weight);

            for depth in 0..ordered_row.len() {
                child_sets
                    .entry(ordered_row[..depth].to_vec())
                    .or_default()
                    .insert(ordered_row[depth]);
            }
        }

        let positions = schema
            .iter()
            .copied()
            .enumerate()
            .map(|(index, variable)| (variable, index))
            .collect::<BTreeMap<_, _>>();
        let children_by_prefix = child_sets
            .into_iter()
            .map(|(prefix, children)| {
                (
                    prefix.into_boxed_slice(),
                    children.into_iter().collect::<Vec<_>>().into_boxed_slice(),
                )
            })
            .collect::<BTreeMap<_, _>>();

        Ok(Self {
            schema: schema.into_boxed_slice(),
            positions,
            children_by_prefix,
            weights,
        })
    }

    fn domain(
        &self,
        variable: BindingVar,
        binding: &BTreeMap<BindingVar, TermId>,
    ) -> Option<&[TermId]> {
        let position = *self.positions.get(&variable)?;
        let mut prefix = Vec::with_capacity(position);
        for &prefix_variable in &self.schema[..position] {
            let value = binding.get(&prefix_variable)?;
            prefix.push(*value);
        }

        Some(
            self.children_by_prefix
                .get(prefix.as_slice())
                .map_or(&[], Box::as_ref),
        )
    }

    fn weight(&self, binding: &BTreeMap<BindingVar, TermId>) -> i64 {
        let row = self
            .schema
            .iter()
            .map(|variable| binding[variable])
            .collect::<Vec<_>>();
        self.weights.get(row.as_slice()).copied().unwrap_or(0)
    }
}

#[derive(Clone, Copy, Debug)]
struct SliceDomainCursor<'a> {
    domain: &'a [TermId],
    position: usize,
}

impl<'a> SliceDomainCursor<'a> {
    fn new(domain: &'a [TermId]) -> Self {
        Self {
            domain,
            position: 0,
        }
    }
}

impl BindingDomainCursor for SliceDomainCursor<'_> {
    fn key(&self) -> Option<TermId> {
        self.domain.get(self.position).copied()
    }

    fn at_end(&self) -> bool {
        self.position >= self.domain.len()
    }

    fn next(&mut self) {
        if !self.at_end() {
            self.position += 1;
        }
    }

    fn seek(&mut self, target: TermId) {
        if self.at_end() {
            return;
        }

        self.position += self.domain[self.position..].partition_point(|&value| value < target);
    }
}

fn trie_join_recurse(
    indexes: &[RelationTrieIndex],
    variable_order: &[BindingVar],
    level: usize,
    binding: &mut BTreeMap<BindingVar, TermId>,
    out: &mut BindingRelation,
    stats: &mut TrieJoinStats,
) -> Result<(), BindingRelationError> {
    if level == variable_order.len() {
        let mut weight = 1i64;
        for index in indexes {
            stats.weight_lookups += 1;
            weight = weight.saturating_mul(index.weight(binding));
        }
        if weight != 0 {
            out.add(
                variable_order
                    .iter()
                    .map(|variable| binding[variable])
                    .collect::<Vec<_>>(),
                weight,
            )?;
        }
        return Ok(());
    }

    let variable = variable_order[level];
    let domains = indexes
        .iter()
        .filter_map(|index| index.domain(variable, binding))
        .collect::<Vec<_>>();
    if domains.is_empty() {
        return Err(BindingRelationError::InvalidVariableOrder);
    }

    for value in leapfrog_intersection_slices(&domains, stats) {
        binding.insert(variable, value);
        trie_join_recurse(indexes, variable_order, level + 1, binding, out, stats)?;
    }
    binding.remove(&variable);
    Ok(())
}

/// Factorized binary equijoin grouped by shared variables.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FactorizedJoin {
    /// Shared variables.
    pub shared_schema: Box<[BindingVar]>,
    /// Variables only on the left input.
    pub left_only_schema: Box<[BindingVar]>,
    /// Variables only on the right input.
    pub right_only_schema: Box<[BindingVar]>,
    /// Groups keyed by shared assignment.
    pub groups: Box<[FactorGroup]>,
}

/// One factorized group.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FactorGroup {
    /// Shared assignment.
    pub key: BindingRow,
    /// Distinct left residual assignments.
    pub left_residuals: Box<[BindingRow]>,
    /// Distinct right residual assignments.
    pub right_residuals: Box<[BindingRow]>,
}

impl FactorGroup {
    /// Number of flat rows represented by this group.
    pub fn row_count(&self) -> usize {
        self.left_residuals.len() * self.right_residuals.len()
    }
}

impl FactorizedJoin {
    /// Builds a factorized set join from positive rows in both relations.
    pub fn from_relations(
        left: &BindingRelation,
        right: &BindingRelation,
    ) -> Result<Self, BindingRelationError> {
        let shared_schema = left
            .schema()
            .iter()
            .copied()
            .filter(|variable| right.schema().contains(variable))
            .collect::<Vec<_>>();
        let left_only_schema = left
            .schema()
            .iter()
            .copied()
            .filter(|variable| !shared_schema.contains(variable))
            .collect::<Vec<_>>();
        let right_only_schema = right
            .schema()
            .iter()
            .copied()
            .filter(|variable| !shared_schema.contains(variable))
            .collect::<Vec<_>>();

        let left_shared = indexes(left, &shared_schema)?;
        let right_shared = indexes(right, &shared_schema)?;
        let left_only = indexes(left, &left_only_schema)?;
        let right_only = indexes(right, &right_only_schema)?;

        let mut left_groups: BTreeMap<Vec<TermId>, BTreeSet<Vec<TermId>>> = BTreeMap::new();
        let mut right_groups: BTreeMap<Vec<TermId>, BTreeSet<Vec<TermId>>> = BTreeMap::new();

        for row in left.positive_rows() {
            left_groups
                .entry(project_key(row, &left_shared))
                .or_default()
                .insert(project_key(row, &left_only));
        }
        for row in right.positive_rows() {
            right_groups
                .entry(project_key(row, &right_shared))
                .or_default()
                .insert(project_key(row, &right_only));
        }

        let groups = left_groups
            .keys()
            .filter(|key| right_groups.contains_key(*key))
            .map(|key| FactorGroup {
                key: key.clone().into_boxed_slice(),
                left_residuals: rows_from_set(&left_groups[key]),
                right_residuals: rows_from_set(&right_groups[key]),
            })
            .collect::<Vec<_>>()
            .into_boxed_slice();

        Ok(Self {
            shared_schema: shared_schema.into_boxed_slice(),
            left_only_schema: left_only_schema.into_boxed_slice(),
            right_only_schema: right_only_schema.into_boxed_slice(),
            groups,
        })
    }

    /// Number of flat rows represented by the factorized join.
    pub fn count(&self) -> usize {
        self.groups.iter().map(FactorGroup::row_count).sum()
    }

    /// Rough structural node count for comparing factorization to flat rows.
    pub fn factorized_node_count(&self) -> usize {
        1 + self
            .groups
            .iter()
            .map(|group| 1 + group.left_residuals.len() + group.right_residuals.len())
            .sum::<usize>()
    }

    /// Enumerates flat rows in schema order: shared + left-only + right-only.
    pub fn rows(&self) -> impl Iterator<Item = Vec<TermId>> + '_ {
        self.groups.iter().flat_map(|group| {
            group.left_residuals.iter().flat_map(move |left| {
                group.right_residuals.iter().map(move |right| {
                    let mut row = group.key.to_vec();
                    row.extend_from_slice(left);
                    row.extend_from_slice(right);
                    row
                })
            })
        })
    }
}

fn indexes(
    relation: &BindingRelation,
    variables: &[BindingVar],
) -> Result<Vec<usize>, BindingRelationError> {
    variables
        .iter()
        .map(|&variable| {
            relation
                .schema_index(variable)
                .ok_or(BindingRelationError::UnknownVariable { variable })
        })
        .collect()
}

fn project_key(row: &[TermId], indexes: &[usize]) -> Vec<TermId> {
    indexes.iter().map(|&index| row[index]).collect()
}

fn rows_from_set(rows: &BTreeSet<Vec<TermId>>) -> Box<[BindingRow]> {
    rows.iter()
        .cloned()
        .map(Vec::into_boxed_slice)
        .collect::<Vec<_>>()
        .into_boxed_slice()
}

fn validate_variable_order(
    relations: &[BindingRelation],
    variable_order: &[BindingVar],
) -> Result<(), BindingRelationError> {
    if has_duplicates(variable_order)
        || relations
            .iter()
            .any(|relation| has_duplicates(relation.schema()))
    {
        return Err(BindingRelationError::InvalidVariableOrder);
    }

    let all_variables = relations
        .iter()
        .flat_map(|relation| relation.schema().iter().copied())
        .collect::<BTreeSet<_>>();
    let ordered = variable_order.iter().copied().collect::<BTreeSet<_>>();
    if all_variables != ordered {
        return Err(BindingRelationError::InvalidVariableOrder);
    }

    Ok(())
}

fn has_duplicates(variables: &[BindingVar]) -> bool {
    let mut seen = BTreeSet::new();
    variables
        .iter()
        .copied()
        .any(|variable| !seen.insert(variable))
}

fn leapfrog_intersection(domains: &[Vec<TermId>]) -> Vec<TermId> {
    let domains = domains.iter().map(Vec::as_slice).collect::<Vec<_>>();
    let mut stats = TrieJoinStats::default();
    leapfrog_intersection_inner(&domains, &mut stats)
}

fn leapfrog_intersection_slices(domains: &[&[TermId]], stats: &mut TrieJoinStats) -> Vec<TermId> {
    stats.domain_intersections += 1;
    stats.domain_sources += domains.len();
    stats.domain_values += domains.iter().map(|domain| domain.len()).sum::<usize>();

    leapfrog_intersection_inner(domains, stats)
}

fn leapfrog_intersection_inner(domains: &[&[TermId]], stats: &mut TrieJoinStats) -> Vec<TermId> {
    if domains.is_empty() || domains.iter().any(|domain| domain.is_empty()) {
        return Vec::new();
    }

    let mut cursors = domains
        .iter()
        .map(|&domain| SliceDomainCursor::new(domain))
        .collect::<Vec<_>>();

    leapfrog_intersection_cursors(&mut cursors, stats)
}

fn leapfrog_intersection_cursors<C: BindingDomainCursor>(
    cursors: &mut [C],
    stats: &mut TrieJoinStats,
) -> Vec<TermId> {
    stats.domain_cursor_opens += cursors.len();

    if cursors.is_empty() || cursors.iter().any(BindingDomainCursor::at_end) {
        return Vec::new();
    }

    let mut target = cursors
        .iter()
        .filter_map(BindingDomainCursor::key)
        .max()
        .expect("non-empty cursors have keys");
    let mut out = Vec::new();

    loop {
        let mut changed = false;
        for cursor in cursors.iter_mut() {
            stats.domain_cursor_seeks += 1;
            cursor.seek(target);
            if cursor.at_end() {
                return out;
            }
            let Some(key) = cursor.key() else {
                return out;
            };
            if key > target {
                target = key;
                changed = true;
            }
        }
        if !changed {
            out.push(target);
            stats.domain_cursor_nexts += 1;
            cursors[0].next();
            if cursors[0].at_end() {
                return out;
            }
            target = cursors[0].key().expect("cursor just checked as not at end");
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn t(id: u64) -> TermId {
        TermId(id)
    }

    fn v(id: u8) -> BindingVar {
        BindingVar(id)
    }

    fn relation(schema: &[u8], rows: &[&[u64]]) -> BindingRelation {
        let mut relation =
            BindingRelation::new(schema.iter().copied().map(BindingVar).collect::<Vec<_>>());
        for row in rows {
            relation
                .add(row.iter().copied().map(TermId).collect::<Vec<_>>(), 1)
                .unwrap();
        }
        relation
    }

    #[test]
    fn natural_and_generic_join_agree_on_variable_order() {
        let left = relation(&[0, 1], &[&[1, 10], &[2, 10], &[3, 20]]);
        let right = relation(&[1, 2], &[&[10, 100], &[10, 101], &[30, 300]]);

        let natural = natural_join(&left, &right).unwrap();
        let generic = generic_join(&[left, right], &[v(1), v(0), v(2)]).unwrap();
        let normalized_natural = natural
            .positive_rows()
            .map(|row| vec![row[1], row[0], row[2]])
            .collect::<BTreeSet<_>>();
        let generic_rows = generic
            .positive_rows()
            .map(Vec::from)
            .collect::<BTreeSet<_>>();

        assert_eq!(generic_rows, normalized_natural);
        assert_eq!(generic_rows.len(), 4);
    }

    #[test]
    fn trie_join_matches_generic_join_with_index_counters() {
        let left = relation(&[0, 1], &[&[1, 10], &[2, 10], &[3, 20]]);
        let right = relation(&[1, 2], &[&[10, 100], &[10, 101], &[30, 300]]);

        let generic = generic_join(&[left.clone(), right.clone()], &[v(1), v(0), v(2)]).unwrap();
        let trie = trie_join(&[left, right], &[v(1), v(0), v(2)]).unwrap();

        assert_eq!(trie.relation, generic);
        assert_eq!(
            trie.stats,
            TrieJoinStats {
                relation_indexes: 2,
                indexed_rows: 6,
                trie_nodes: 6,
                domain_intersections: 4,
                domain_sources: 5,
                domain_values: 10,
                domain_cursor_opens: 5,
                domain_cursor_seeks: 11,
                domain_cursor_nexts: 7,
                weight_lookups: 8,
                output_rows: 4,
            }
        );
    }

    #[test]
    fn cursor_leapfrog_intersection_uses_monotone_seek_contract() {
        let left = [t(1), t(3), t(5), t(8)];
        let right = [t(2), t(3), t(5), t(9)];
        let guard = [t(3), t(4), t(5), t(10)];
        let mut cursors = [
            SliceDomainCursor::new(&left),
            SliceDomainCursor::new(&right),
            SliceDomainCursor::new(&guard),
        ];
        let mut stats = TrieJoinStats::default();

        let intersection = leapfrog_intersection_cursors(&mut cursors, &mut stats);

        assert_eq!(intersection, vec![t(3), t(5)]);
        assert_eq!(stats.domain_cursor_opens, 3);
        assert_eq!(stats.domain_cursor_nexts, 2);
        assert!(stats.domain_cursor_seeks >= stats.domain_cursor_opens);
    }

    #[test]
    fn trie_join_handles_cyclic_triangle_without_binary_intermediate() {
        let xy = relation(&[0, 1], &[&[1, 2], &[1, 3], &[2, 3], &[3, 1]]);
        let yz = relation(&[1, 2], &[&[2, 3], &[3, 1], &[3, 4], &[1, 2]]);
        let zx = relation(&[2, 0], &[&[3, 1], &[1, 2], &[2, 3], &[4, 1]]);

        let generic =
            generic_join(&[xy.clone(), yz.clone(), zx.clone()], &[v(0), v(1), v(2)]).unwrap();
        let trie = trie_join(&[xy, yz, zx], &[v(0), v(1), v(2)]).unwrap();

        assert_eq!(trie.relation, generic);
        assert_eq!(
            trie.relation
                .positive_rows()
                .map(Vec::from)
                .collect::<BTreeSet<_>>(),
            BTreeSet::from([
                vec![t(1), t(2), t(3)],
                vec![t(1), t(3), t(4)],
                vec![t(2), t(3), t(1)],
                vec![t(3), t(1), t(2)],
            ])
        );
        assert_eq!(trie.stats.output_rows, 4);
        assert!(trie.stats.domain_intersections < 10);
    }

    #[test]
    fn factorized_join_counts_without_flattening() {
        let left = relation(&[0, 1], &[&[1, 10], &[2, 10]]);
        let right = relation(&[1, 2], &[&[10, 100], &[10, 101], &[10, 102]]);

        let factorized = FactorizedJoin::from_relations(&left, &right).unwrap();

        assert_eq!(factorized.count(), 6);
        assert_eq!(factorized.rows().count(), 6);
        assert!(factorized.factorized_node_count() < factorized.count() + 6);
    }

    #[test]
    fn signed_rows_cancel_and_participate_in_joins() {
        let mut left = BindingRelation::new([v(0)]);
        left.add(vec![t(1)], 2).unwrap();
        left.add(vec![t(1)], -2).unwrap();
        assert!(left.is_empty());

        left.add(vec![t(1)], -1).unwrap();
        let right = relation(&[0], &[&[1]]);
        let joined = natural_join(&left, &right).unwrap();

        assert_eq!(joined.weight(&[t(1)]), -1);
    }

    #[test]
    fn presence_difference_uses_positive_visibility() {
        let left = relation(&[0], &[&[1], &[2]]);
        let mut right = BindingRelation::new([v(0)]);
        right.add(vec![t(1)], -1).unwrap();
        right.add(vec![t(2)], 1).unwrap();

        let diff = left.difference_presence(&right).unwrap();

        assert_eq!(diff.weight(&[t(1)]), 1);
        assert_eq!(diff.weight(&[t(2)]), 0);
    }
}
