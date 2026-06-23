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

/// Non-materializing trace of a trie-backed variable-at-a-time join.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TrieJoinTrace {
    /// Variable order used by the traced traversal.
    pub variable_order: Box<[BindingVar]>,
    /// Input relation indexes constructed for the trace.
    pub relation_indexes: usize,
    /// Positive rows retained across all relation indexes.
    pub indexed_rows: usize,
    /// Distinct trie prefixes with outgoing children across all indexes.
    pub trie_nodes: usize,
    /// Domain-intersection contexts visited in traversal order.
    pub steps: Box<[TrieJoinTraceStep]>,
    /// Complete satisfying bindings reached by domain traversal before relation
    /// materialization or row-weight probing.
    pub candidate_bindings: usize,
}

/// Aggregate counters and shape facts derived from a trie-join trace.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct TrieJoinTraceSummary {
    /// Input relation indexes constructed for the trace.
    pub relation_indexes: usize,
    /// Positive rows retained across all relation indexes.
    pub indexed_rows: usize,
    /// Distinct trie prefixes with outgoing children across all indexes.
    pub trie_nodes: usize,
    /// Domain-intersection contexts visited in traversal order.
    pub steps: usize,
    /// Complete satisfying bindings reached by the traced traversal.
    pub candidate_bindings: usize,
    /// Variable-domain intersections represented by the trace.
    pub domain_intersections: usize,
    /// Relation domains participating in those intersections.
    pub domain_sources: usize,
    /// Domain values presented to leapfrog intersection.
    pub domain_values: usize,
    /// Values that survived all recorded intersections.
    pub intersection_values: usize,
    /// Intersections whose survivor set was empty.
    pub empty_intersections: usize,
    /// Largest bound-prefix depth represented by one step.
    pub max_bound_prefix_len: usize,
    /// Largest relation-domain fan-in represented by one step.
    pub max_participating_relations: usize,
    /// Largest survivor set represented by one step.
    pub max_intersection_len: usize,
    /// Cursor opens recorded across all trace steps.
    pub cursor_opens: usize,
    /// Cursor seeks recorded across all trace steps.
    pub cursor_seeks: usize,
    /// Cursor next calls recorded across all trace steps.
    pub cursor_nexts: usize,
}

/// Replayable prefix tree reconstructed from a trie-join trace.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TrieJoinTraceReplayShape {
    /// Locally validated aggregate trace summary.
    pub summary: TrieJoinTraceSummary,
    /// Root variable-depth context, absent only for zero-variable traces.
    pub root: Option<TrieJoinTraceReplayNode>,
}

/// Trace-local work affected by replaying from one bound-prefix context.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct TrieJoinTraceImpact {
    /// Bound-prefix context whose replay subtree was found.
    pub bound_prefix: BindingRow,
    /// Original trace step indexes covered by this replay subtree.
    pub step_indexes: Box<[usize]>,
    /// Domain-intersection steps covered by this replay subtree.
    pub steps: usize,
    /// Complete satisfying bindings below this replay subtree.
    pub candidate_bindings: usize,
    /// Relation domains participating below this replay subtree.
    pub domain_sources: usize,
    /// Domain values exposed before leapfrog intersection below this subtree.
    pub domain_values: usize,
    /// Values that survived intersection below this replay subtree.
    pub intersection_values: usize,
    /// Deepest variable-order level reached by this replay subtree.
    pub max_level: usize,
}

/// One bound-prefix context changed between two replay shapes.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TrieJoinTraceReplayDiffEntry {
    /// Bound-prefix context compared between replay shapes.
    pub bound_prefix: BindingRow,
    /// Kind of replay-shape change at this exact context.
    pub kind: TrieJoinTraceReplayDiffKind,
    /// Previous trace-local impact, absent for newly added contexts.
    pub old_impact: Option<TrieJoinTraceImpact>,
    /// New trace-local impact, absent for removed contexts.
    pub new_impact: Option<TrieJoinTraceImpact>,
}

/// Replay-shape change kind for one bound-prefix context.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TrieJoinTraceReplayDiffKind {
    /// Context exists only in the new replay shape.
    Added,
    /// Context exists only in the old replay shape.
    Removed,
    /// Context exists in both shapes but its local intersection metadata changed.
    Changed,
}

/// Trace-local diff between two replay shapes.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct TrieJoinTraceReplayDiff {
    /// Bound-prefix contexts present in both shapes with identical local metadata.
    pub unchanged_contexts: usize,
    /// Bound-prefix contexts present in both shapes with changed local metadata.
    pub changed_contexts: usize,
    /// Bound-prefix contexts present only in the new shape.
    pub added_contexts: usize,
    /// Bound-prefix contexts present only in the old shape.
    pub removed_contexts: usize,
    /// Non-overlapping changed-context roots used for touched-work estimates.
    pub frontier_contexts: usize,
    /// Old replay steps under the non-overlapping change frontier.
    pub old_replay_steps_touched: usize,
    /// New replay steps under the non-overlapping change frontier.
    pub new_replay_steps_touched: usize,
    /// Old candidate bindings under the non-overlapping change frontier.
    pub old_candidate_bindings_touched: usize,
    /// New candidate bindings under the non-overlapping change frontier.
    pub new_candidate_bindings_touched: usize,
    /// Exact changed, added, and removed contexts.
    pub entries: Box<[TrieJoinTraceReplayDiffEntry]>,
}

impl TrieJoinTraceReplayDiff {
    /// Returns true when the two replay shapes expose the same local contexts.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
}

/// One replay node for a variable-depth domain intersection.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TrieJoinTraceReplayNode {
    /// Original trace step index.
    pub step_index: usize,
    /// Depth in the global variable order.
    pub level: usize,
    /// Variable intersected at this depth.
    pub variable: BindingVar,
    /// Values already bound before this depth.
    pub bound_prefix: BindingRow,
    /// Relation index numbers whose trie domains constrained this variable.
    pub participating_relations: Box<[usize]>,
    /// Domain length contributed by each participating relation.
    pub relation_domain_lens: Box<[usize]>,
    /// Values that survived the intersection at this context.
    pub intersection: Box<[TermId]>,
    /// Per-survivor continuation in traversal order.
    pub branches: Box<[TrieJoinTraceReplayBranch]>,
}

/// One survivor from a replay node's domain intersection.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TrieJoinTraceReplayBranch {
    /// Bound value for the node variable.
    pub value: TermId,
    /// Child context after binding `value`, or `None` at leaf depth.
    pub child: Option<Box<TrieJoinTraceReplayNode>>,
}

impl TrieJoinTraceReplayShape {
    /// Returns the replay subtree affected at `bound_prefix`, if this trace
    /// visited that exact variable-prefix context.
    ///
    /// This is a trace-local sensitivity summary. It identifies the existing
    /// replay work under a bound prefix, but it does not maintain or recompute
    /// join answers for a changed relation.
    pub fn impact_for_bound_prefix(&self, bound_prefix: &[TermId]) -> Option<TrieJoinTraceImpact> {
        if bound_prefix.is_empty() && self.root.is_none() {
            return Some(TrieJoinTraceImpact {
                bound_prefix: Vec::new().into_boxed_slice(),
                candidate_bindings: self.summary.candidate_bindings,
                ..TrieJoinTraceImpact::default()
            });
        }

        self.root
            .as_ref()?
            .find_bound_prefix(bound_prefix)
            .map(TrieJoinTraceReplayNode::impact)
    }

    /// Compares two replay shapes at exact bound-prefix contexts.
    ///
    /// This is an edit-distance-style diagnostic for traces. It does not apply
    /// deltas or decide semantic equivalence of the underlying relations.
    pub fn diff(&self, newer: &Self) -> TrieJoinTraceReplayDiff {
        let mut old_nodes = BTreeMap::new();
        let mut new_nodes = BTreeMap::new();
        self.collect_nodes(&mut old_nodes);
        newer.collect_nodes(&mut new_nodes);

        let prefixes = old_nodes
            .keys()
            .chain(new_nodes.keys())
            .cloned()
            .collect::<BTreeSet<_>>();
        let mut entries = Vec::new();
        let mut diff = TrieJoinTraceReplayDiff::default();

        for prefix in prefixes {
            match (old_nodes.get(&prefix), new_nodes.get(&prefix)) {
                (Some(old), Some(new)) if old.local_context_eq(new) => {
                    diff.unchanged_contexts += 1;
                }
                (Some(old), Some(new)) => {
                    diff.changed_contexts += 1;
                    entries.push(TrieJoinTraceReplayDiffEntry {
                        bound_prefix: prefix,
                        kind: TrieJoinTraceReplayDiffKind::Changed,
                        old_impact: Some(old.impact()),
                        new_impact: Some(new.impact()),
                    });
                }
                (Some(old), None) => {
                    diff.removed_contexts += 1;
                    entries.push(TrieJoinTraceReplayDiffEntry {
                        bound_prefix: prefix,
                        kind: TrieJoinTraceReplayDiffKind::Removed,
                        old_impact: Some(old.impact()),
                        new_impact: None,
                    });
                }
                (None, Some(new)) => {
                    diff.added_contexts += 1;
                    entries.push(TrieJoinTraceReplayDiffEntry {
                        bound_prefix: prefix,
                        kind: TrieJoinTraceReplayDiffKind::Added,
                        old_impact: None,
                        new_impact: Some(new.impact()),
                    });
                }
                (None, None) => {}
            }
        }

        entries.sort_by(|left, right| {
            left.bound_prefix
                .len()
                .cmp(&right.bound_prefix.len())
                .then_with(|| left.bound_prefix.as_ref().cmp(right.bound_prefix.as_ref()))
        });
        diff.add_frontier_estimate(&entries);
        diff.entries = entries.into_boxed_slice();
        diff
    }

    fn collect_nodes<'a>(&'a self, nodes: &mut BTreeMap<BindingRow, &'a TrieJoinTraceReplayNode>) {
        if let Some(root) = &self.root {
            root.collect_nodes(nodes);
        }
    }
}

impl TrieJoinTraceReplayNode {
    fn find_bound_prefix(&self, bound_prefix: &[TermId]) -> Option<&TrieJoinTraceReplayNode> {
        if self.bound_prefix.as_ref() == bound_prefix {
            return Some(self);
        }
        if bound_prefix.len() <= self.bound_prefix.len()
            || !bound_prefix.starts_with(self.bound_prefix.as_ref())
        {
            return None;
        }

        let next_value = bound_prefix[self.bound_prefix.len()];
        self.branches
            .iter()
            .find(|branch| branch.value == next_value)?
            .child
            .as_deref()?
            .find_bound_prefix(bound_prefix)
    }

    fn impact(&self) -> TrieJoinTraceImpact {
        let mut impact = TrieJoinTraceImpact {
            bound_prefix: self.bound_prefix.clone(),
            max_level: self.level,
            ..TrieJoinTraceImpact::default()
        };
        let mut step_indexes = Vec::new();
        self.accumulate_impact(&mut impact, &mut step_indexes);
        impact.steps = step_indexes.len();
        impact.step_indexes = step_indexes.into_boxed_slice();
        impact
    }

    fn accumulate_impact(&self, impact: &mut TrieJoinTraceImpact, step_indexes: &mut Vec<usize>) {
        step_indexes.push(self.step_index);
        impact.domain_sources += self.participating_relations.len();
        impact.domain_values += self.relation_domain_lens.iter().sum::<usize>();
        impact.intersection_values += self.intersection.len();
        impact.max_level = impact.max_level.max(self.level);

        for branch in self.branches.iter() {
            if let Some(child) = branch.child.as_deref() {
                child.accumulate_impact(impact, step_indexes);
            } else {
                impact.candidate_bindings += 1;
            }
        }
    }

    fn collect_nodes<'a>(&'a self, nodes: &mut BTreeMap<BindingRow, &'a TrieJoinTraceReplayNode>) {
        nodes.insert(self.bound_prefix.clone(), self);
        for branch in self.branches.iter() {
            if let Some(child) = branch.child.as_deref() {
                child.collect_nodes(nodes);
            }
        }
    }

    fn local_context_eq(&self, other: &Self) -> bool {
        self.level == other.level
            && self.variable == other.variable
            && self.participating_relations == other.participating_relations
            && self.relation_domain_lens == other.relation_domain_lens
            && self.intersection == other.intersection
    }
}

impl TrieJoinTraceReplayDiff {
    fn add_frontier_estimate(&mut self, entries: &[TrieJoinTraceReplayDiffEntry]) {
        let mut frontier_prefixes = Vec::<BindingRow>::new();
        for entry in entries {
            if frontier_prefixes
                .iter()
                .any(|prefix| entry.bound_prefix.starts_with(prefix.as_ref()))
            {
                continue;
            }

            frontier_prefixes.push(entry.bound_prefix.clone());
            self.frontier_contexts += 1;
            if let Some(impact) = &entry.old_impact {
                self.old_replay_steps_touched += impact.steps;
                self.old_candidate_bindings_touched += impact.candidate_bindings;
            }
            if let Some(impact) = &entry.new_impact {
                self.new_replay_steps_touched += impact.steps;
                self.new_candidate_bindings_touched += impact.candidate_bindings;
            }
        }
    }
}

/// Shape error found while summarizing a trie-join trace.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TrieJoinTraceShapeError {
    /// A step refers past the configured variable order.
    InvalidStepLevel {
        step: usize,
        level: usize,
        variable_count: usize,
    },
    /// A step variable does not match the trace's variable order at its level.
    VariableMismatch {
        step: usize,
        expected: BindingVar,
        actual: BindingVar,
    },
    /// Bound-prefix length must equal the variable depth.
    BoundPrefixLengthMismatch {
        step: usize,
        expected: usize,
        actual: usize,
    },
    /// A participating relation index is outside the trace relation set.
    UnknownParticipatingRelation {
        step: usize,
        relation_index: usize,
        relation_indexes: usize,
    },
    /// Participating relation IDs and domain lengths must align one-for-one.
    ParticipationLengthMismatch {
        step: usize,
        participating_relations: usize,
        relation_domain_lens: usize,
    },
    /// Aggregate domain-source count must match participating relation IDs.
    DomainSourceMismatch {
        step: usize,
        expected: usize,
        actual: usize,
    },
    /// Aggregate domain-value count must match summed relation-domain lengths.
    DomainValueMismatch {
        step: usize,
        expected: usize,
        actual: usize,
    },
    /// Non-empty domains open one cursor per participating relation.
    CursorOpenMismatch {
        step: usize,
        expected: usize,
        actual: usize,
    },
    /// A replay step appears at a different variable depth than traversal order expects.
    ReplayLevelMismatch {
        step: usize,
        expected: usize,
        actual: usize,
    },
    /// A replay step is missing for a reachable bound prefix.
    MissingReplayStep {
        level: usize,
        bound_prefix_len: usize,
    },
    /// A locally valid step belongs to a different bound-prefix branch.
    BoundPrefixValueMismatch {
        step: usize,
        position: usize,
        expected: TermId,
        actual: TermId,
    },
    /// Steps remain after replaying every reachable branch.
    TrailingReplayStep { step: usize },
    /// Leaf replay count disagrees with the trace candidate total.
    CandidateBindingMismatch { expected: usize, actual: usize },
}

/// One variable-depth domain intersection observed while tracing LFTJ traversal.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TrieJoinTraceStep {
    /// Depth in the global variable order.
    pub level: usize,
    /// Variable intersected at this depth.
    pub variable: BindingVar,
    /// Values already bound for variables before `level`, in variable-order
    /// prefix order.
    pub bound_prefix: BindingRow,
    /// Relation index numbers whose trie domains constrained this variable at
    /// the current bound prefix.
    pub participating_relations: Box<[usize]>,
    /// Domain length contributed by each participating relation, in
    /// `participating_relations` order.
    pub relation_domain_lens: Box<[usize]>,
    /// Relation domains that constrained this variable in the current context.
    pub domain_sources: usize,
    /// Total values exposed by those relation domains before intersection.
    pub domain_values: usize,
    /// Values that survived leapfrog intersection at this context.
    pub intersection: Box<[TermId]>,
    /// Cursor opens issued for this intersection.
    pub cursor_opens: usize,
    /// Cursor seeks issued for this intersection.
    pub cursor_seeks: usize,
    /// Cursor next calls issued after aligned values.
    pub cursor_nexts: usize,
}

impl TrieJoinTrace {
    /// Validates step-local trace shape and returns aggregate replay counters.
    pub fn summarize(&self) -> Result<TrieJoinTraceSummary, TrieJoinTraceShapeError> {
        let mut summary = TrieJoinTraceSummary {
            relation_indexes: self.relation_indexes,
            indexed_rows: self.indexed_rows,
            trie_nodes: self.trie_nodes,
            steps: self.steps.len(),
            candidate_bindings: self.candidate_bindings,
            ..TrieJoinTraceSummary::default()
        };

        for (step_index, step) in self.steps.iter().enumerate() {
            let Some(&expected_variable) = self.variable_order.get(step.level) else {
                return Err(TrieJoinTraceShapeError::InvalidStepLevel {
                    step: step_index,
                    level: step.level,
                    variable_count: self.variable_order.len(),
                });
            };

            if step.variable != expected_variable {
                return Err(TrieJoinTraceShapeError::VariableMismatch {
                    step: step_index,
                    expected: expected_variable,
                    actual: step.variable,
                });
            }

            if step.bound_prefix.len() != step.level {
                return Err(TrieJoinTraceShapeError::BoundPrefixLengthMismatch {
                    step: step_index,
                    expected: step.level,
                    actual: step.bound_prefix.len(),
                });
            }

            for &relation_index in step.participating_relations.iter() {
                if relation_index >= self.relation_indexes {
                    return Err(TrieJoinTraceShapeError::UnknownParticipatingRelation {
                        step: step_index,
                        relation_index,
                        relation_indexes: self.relation_indexes,
                    });
                }
            }

            if step.participating_relations.len() != step.relation_domain_lens.len() {
                return Err(TrieJoinTraceShapeError::ParticipationLengthMismatch {
                    step: step_index,
                    participating_relations: step.participating_relations.len(),
                    relation_domain_lens: step.relation_domain_lens.len(),
                });
            }

            if step.domain_sources != step.participating_relations.len() {
                return Err(TrieJoinTraceShapeError::DomainSourceMismatch {
                    step: step_index,
                    expected: step.participating_relations.len(),
                    actual: step.domain_sources,
                });
            }

            let domain_values = step.relation_domain_lens.iter().sum::<usize>();
            if step.domain_values != domain_values {
                return Err(TrieJoinTraceShapeError::DomainValueMismatch {
                    step: step_index,
                    expected: domain_values,
                    actual: step.domain_values,
                });
            }

            let expected_cursor_opens = if step.relation_domain_lens.iter().any(|&len| len == 0) {
                0
            } else {
                step.participating_relations.len()
            };
            if step.cursor_opens != expected_cursor_opens {
                return Err(TrieJoinTraceShapeError::CursorOpenMismatch {
                    step: step_index,
                    expected: expected_cursor_opens,
                    actual: step.cursor_opens,
                });
            }

            summary.domain_intersections += 1;
            summary.domain_sources += step.domain_sources;
            summary.domain_values += step.domain_values;
            summary.intersection_values += step.intersection.len();
            summary.empty_intersections += usize::from(step.intersection.is_empty());
            summary.max_bound_prefix_len =
                summary.max_bound_prefix_len.max(step.bound_prefix.len());
            summary.max_participating_relations = summary
                .max_participating_relations
                .max(step.participating_relations.len());
            summary.max_intersection_len =
                summary.max_intersection_len.max(step.intersection.len());
            summary.cursor_opens += step.cursor_opens;
            summary.cursor_seeks += step.cursor_seeks;
            summary.cursor_nexts += step.cursor_nexts;
        }

        Ok(summary)
    }

    /// Reconstructs the variable-prefix replay tree represented by this trace.
    ///
    /// `summarize` checks each step independently. This method additionally
    /// checks that the steps form the preorder traversal that an LFTJ-style
    /// cursor would replay: each survivor at a non-leaf depth must be followed
    /// by exactly one child context whose bound prefix extends the parent.
    pub fn replay_shape(&self) -> Result<TrieJoinTraceReplayShape, TrieJoinTraceShapeError> {
        let summary = self.summarize()?;

        if self.variable_order.is_empty() {
            if !self.steps.is_empty() {
                return Err(TrieJoinTraceShapeError::TrailingReplayStep { step: 0 });
            }
            if self.candidate_bindings != 1 {
                return Err(TrieJoinTraceShapeError::CandidateBindingMismatch {
                    expected: self.candidate_bindings,
                    actual: 1,
                });
            }
            return Ok(TrieJoinTraceReplayShape {
                summary,
                root: None,
            });
        }

        let mut step_index = 0;
        let mut candidate_bindings = 0;
        let root = self.replay_node(0, &[], &mut step_index, &mut candidate_bindings)?;

        if step_index != self.steps.len() {
            return Err(TrieJoinTraceShapeError::TrailingReplayStep { step: step_index });
        }
        if candidate_bindings != self.candidate_bindings {
            return Err(TrieJoinTraceShapeError::CandidateBindingMismatch {
                expected: self.candidate_bindings,
                actual: candidate_bindings,
            });
        }

        Ok(TrieJoinTraceReplayShape {
            summary,
            root: Some(root),
        })
    }

    fn replay_node(
        &self,
        level: usize,
        expected_prefix: &[TermId],
        step_index: &mut usize,
        candidate_bindings: &mut usize,
    ) -> Result<TrieJoinTraceReplayNode, TrieJoinTraceShapeError> {
        let current_step = *step_index;
        let Some(step) = self.steps.get(current_step) else {
            return Err(TrieJoinTraceShapeError::MissingReplayStep {
                level,
                bound_prefix_len: expected_prefix.len(),
            });
        };

        if step.level != level {
            return Err(TrieJoinTraceShapeError::ReplayLevelMismatch {
                step: current_step,
                expected: level,
                actual: step.level,
            });
        }

        for (position, (&expected, &actual)) in expected_prefix
            .iter()
            .zip(step.bound_prefix.iter())
            .enumerate()
        {
            if expected != actual {
                return Err(TrieJoinTraceShapeError::BoundPrefixValueMismatch {
                    step: current_step,
                    position,
                    expected,
                    actual,
                });
            }
        }

        *step_index += 1;
        let leaf = level + 1 == self.variable_order.len();
        let mut branches = Vec::with_capacity(step.intersection.len());
        for &value in step.intersection.iter() {
            let child = if leaf {
                *candidate_bindings += 1;
                None
            } else {
                let mut child_prefix = Vec::with_capacity(expected_prefix.len() + 1);
                child_prefix.extend_from_slice(expected_prefix);
                child_prefix.push(value);
                Some(Box::new(self.replay_node(
                    level + 1,
                    &child_prefix,
                    step_index,
                    candidate_bindings,
                )?))
            };
            branches.push(TrieJoinTraceReplayBranch { value, child });
        }

        Ok(TrieJoinTraceReplayNode {
            step_index: current_step,
            level: step.level,
            variable: step.variable,
            bound_prefix: step.bound_prefix.clone(),
            participating_relations: step.participating_relations.clone(),
            relation_domain_lens: step.relation_domain_lens.clone(),
            intersection: step.intersection.clone(),
            branches: branches.into_boxed_slice(),
        })
    }
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

/// Traces the trie-backed variable-at-a-time traversal without materializing
/// the final joined relation.
///
/// The trace records each variable-depth domain intersection a cursor-backed
/// factor must reproduce: bound prefix, constraining domain count, presented
/// domain values, surviving intersection values, and cursor operation counts.
pub fn trie_join_trace(
    relations: &[BindingRelation],
    variable_order: &[BindingVar],
) -> Result<TrieJoinTrace, BindingRelationError> {
    validate_variable_order(relations, variable_order)?;

    let indexes = relations
        .iter()
        .map(|relation| RelationTrieIndex::build(relation, variable_order))
        .collect::<Result<Vec<_>, _>>()?;
    let indexed_rows = indexes.iter().map(|index| index.weights.len()).sum();
    let trie_nodes = indexes
        .iter()
        .map(|index| index.children_by_prefix.len())
        .sum();

    let mut binding = BTreeMap::<BindingVar, TermId>::new();
    let mut steps = Vec::new();
    let mut candidate_bindings = 0;
    trie_join_trace_recurse(
        &indexes,
        variable_order,
        0,
        &mut binding,
        &mut steps,
        &mut candidate_bindings,
    )?;

    Ok(TrieJoinTrace {
        variable_order: variable_order.to_vec().into_boxed_slice(),
        relation_indexes: indexes.len(),
        indexed_rows,
        trie_nodes,
        steps: steps.into_boxed_slice(),
        candidate_bindings,
    })
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

fn trie_join_trace_recurse(
    indexes: &[RelationTrieIndex],
    variable_order: &[BindingVar],
    level: usize,
    binding: &mut BTreeMap<BindingVar, TermId>,
    steps: &mut Vec<TrieJoinTraceStep>,
    candidate_bindings: &mut usize,
) -> Result<(), BindingRelationError> {
    if level == variable_order.len() {
        *candidate_bindings += 1;
        return Ok(());
    }

    let variable = variable_order[level];
    let domain_entries = indexes
        .iter()
        .enumerate()
        .filter_map(|(relation_index, index)| {
            index
                .domain(variable, binding)
                .map(|domain| (relation_index, domain))
        })
        .collect::<Vec<_>>();
    let domains = domain_entries
        .iter()
        .map(|(_, domain)| *domain)
        .collect::<Vec<_>>();
    if domains.is_empty() {
        return Err(BindingRelationError::InvalidVariableOrder);
    }

    let mut stats = TrieJoinStats::default();
    let intersection = leapfrog_intersection_slices(&domains, &mut stats);
    let bound_prefix = variable_order[..level]
        .iter()
        .map(|variable| binding[variable])
        .collect::<Vec<_>>();

    steps.push(TrieJoinTraceStep {
        level,
        variable,
        bound_prefix: bound_prefix.into_boxed_slice(),
        participating_relations: domain_entries
            .iter()
            .map(|(relation_index, _)| *relation_index)
            .collect::<Vec<_>>()
            .into_boxed_slice(),
        relation_domain_lens: domain_entries
            .iter()
            .map(|(_, domain)| domain.len())
            .collect::<Vec<_>>()
            .into_boxed_slice(),
        domain_sources: domains.len(),
        domain_values: domains.iter().map(|domain| domain.len()).sum(),
        intersection: intersection.clone().into_boxed_slice(),
        cursor_opens: stats.domain_cursor_opens,
        cursor_seeks: stats.domain_cursor_seeks,
        cursor_nexts: stats.domain_cursor_nexts,
    });

    for value in intersection {
        binding.insert(variable, value);
        trie_join_trace_recurse(
            indexes,
            variable_order,
            level + 1,
            binding,
            steps,
            candidate_bindings,
        )?;
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
    fn trie_join_trace_records_variable_depth_domain_contexts_without_materializing() {
        let left = relation(&[0, 1], &[&[1, 10], &[2, 10], &[3, 20]]);
        let right = relation(&[1, 2], &[&[10, 100], &[10, 101], &[30, 300]]);
        let variable_order = [v(1), v(0), v(2)];

        let trace = trie_join_trace(&[left.clone(), right.clone()], &variable_order).unwrap();
        let trie = trie_join(&[left, right], &variable_order).unwrap();

        assert_eq!(trace.variable_order.as_ref(), variable_order);
        assert_eq!(
            trace.candidate_bindings,
            trie.relation.positive_rows().count()
        );
        assert_eq!(trace.steps.len(), 4);
        assert_eq!(trace.relation_indexes, 2);
        assert_eq!(trace.indexed_rows, 6);
        assert_eq!(trace.trie_nodes, 6);
        assert_eq!(
            trace.summarize().unwrap(),
            TrieJoinTraceSummary {
                relation_indexes: 2,
                indexed_rows: 6,
                trie_nodes: 6,
                steps: 4,
                candidate_bindings: 4,
                domain_intersections: 4,
                domain_sources: 5,
                domain_values: 10,
                intersection_values: 7,
                empty_intersections: 0,
                max_bound_prefix_len: 2,
                max_participating_relations: 2,
                max_intersection_len: 2,
                cursor_opens: 5,
                cursor_seeks: 11,
                cursor_nexts: 7,
            }
        );

        let root = &trace.steps[0];
        assert_eq!(root.level, 0);
        assert_eq!(root.variable, v(1));
        assert!(root.bound_prefix.is_empty());
        assert_eq!(root.participating_relations.as_ref(), [0, 1]);
        assert_eq!(root.relation_domain_lens.as_ref(), [2, 2]);
        assert_eq!(root.domain_sources, 2);
        assert_eq!(root.domain_values, 4);
        assert_eq!(root.intersection.as_ref(), [t(10)]);
        assert_eq!(root.cursor_opens, 2);
        assert!(root.cursor_seeks >= root.cursor_opens);
        assert_eq!(root.cursor_nexts, 1);

        assert_eq!(
            trace
                .steps
                .iter()
                .filter(|step| step.variable == v(2))
                .count(),
            2
        );
        assert!(trace
            .steps
            .iter()
            .filter(|step| step.variable == v(2))
            .all(|step| step.bound_prefix.len() == 2
                && step.participating_relations.as_ref() == [1]
                && step.relation_domain_lens.as_ref() == [2]
                && step.intersection.as_ref() == [t(100), t(101)]));

        let replay = trace.replay_shape().unwrap();
        assert_eq!(replay.summary, trace.summarize().unwrap());
        let root = replay.root.as_ref().unwrap();
        assert_eq!(root.step_index, 0);
        assert_eq!(root.variable, v(1));
        assert_eq!(root.intersection.as_ref(), [t(10)]);
        assert_eq!(root.branches.len(), 1);
        assert_eq!(root.branches[0].value, t(10));

        let x_node = root.branches[0].child.as_ref().unwrap();
        assert_eq!(x_node.step_index, 1);
        assert_eq!(x_node.variable, v(0));
        assert_eq!(x_node.bound_prefix.as_ref(), [t(10)]);
        assert_eq!(x_node.intersection.as_ref(), [t(1), t(2)]);
        assert_eq!(x_node.branches.len(), 2);

        for branch in x_node.branches.iter() {
            let z_node = branch.child.as_ref().unwrap();
            assert_eq!(z_node.variable, v(2));
            assert_eq!(z_node.bound_prefix.as_ref(), [t(10), branch.value]);
            assert_eq!(z_node.intersection.as_ref(), [t(100), t(101)]);
            assert!(z_node.branches.iter().all(|leaf| leaf.child.is_none()));
        }

        let root_impact = replay.impact_for_bound_prefix(&[]).unwrap();
        assert_eq!(root_impact.bound_prefix.as_ref(), []);
        assert_eq!(root_impact.step_indexes.as_ref(), [0, 1, 2, 3]);
        assert_eq!(root_impact.steps, 4);
        assert_eq!(root_impact.candidate_bindings, 4);
        assert_eq!(root_impact.domain_sources, 5);
        assert_eq!(root_impact.domain_values, 10);
        assert_eq!(root_impact.intersection_values, 7);
        assert_eq!(root_impact.max_level, 2);

        let y10_impact = replay.impact_for_bound_prefix(&[t(10)]).unwrap();
        assert_eq!(y10_impact.bound_prefix.as_ref(), [t(10)]);
        assert_eq!(y10_impact.step_indexes.as_ref(), [1, 2, 3]);
        assert_eq!(y10_impact.steps, 3);
        assert_eq!(y10_impact.candidate_bindings, 4);
        assert_eq!(y10_impact.domain_sources, 3);
        assert_eq!(y10_impact.domain_values, 6);
        assert_eq!(y10_impact.intersection_values, 6);
        assert_eq!(y10_impact.max_level, 2);

        let x1_impact = replay.impact_for_bound_prefix(&[t(10), t(1)]).unwrap();
        assert_eq!(x1_impact.bound_prefix.as_ref(), [t(10), t(1)]);
        assert_eq!(x1_impact.step_indexes.as_ref(), [2]);
        assert_eq!(x1_impact.steps, 1);
        assert_eq!(x1_impact.candidate_bindings, 2);
        assert_eq!(x1_impact.domain_sources, 1);
        assert_eq!(x1_impact.domain_values, 2);
        assert_eq!(x1_impact.intersection_values, 2);
        assert_eq!(x1_impact.max_level, 2);

        assert_eq!(replay.impact_for_bound_prefix(&[t(20)]), None);
        assert_eq!(replay.impact_for_bound_prefix(&[t(10), t(3)]), None);
    }

    #[test]
    fn trie_join_trace_replay_diff_reports_context_edits_without_nested_double_counting() {
        let old_left = relation(&[0, 1], &[&[1, 10], &[2, 10]]);
        let new_left = relation(&[0, 1], &[&[1, 10], &[2, 10], &[3, 10]]);
        let right = relation(&[1, 2], &[&[10, 100], &[10, 101]]);
        let variable_order = [v(1), v(0), v(2)];

        let old_replay = trie_join_trace(&[old_left, right.clone()], &variable_order)
            .unwrap()
            .replay_shape()
            .unwrap();
        let new_replay = trie_join_trace(&[new_left, right], &variable_order)
            .unwrap()
            .replay_shape()
            .unwrap();

        let diff = old_replay.diff(&new_replay);

        assert!(!diff.is_empty());
        assert_eq!(diff.unchanged_contexts, 3);
        assert_eq!(diff.changed_contexts, 1);
        assert_eq!(diff.added_contexts, 1);
        assert_eq!(diff.removed_contexts, 0);
        assert_eq!(diff.frontier_contexts, 1);
        assert_eq!(diff.old_replay_steps_touched, 3);
        assert_eq!(diff.new_replay_steps_touched, 4);
        assert_eq!(diff.old_candidate_bindings_touched, 4);
        assert_eq!(diff.new_candidate_bindings_touched, 6);
        assert_eq!(diff.entries.len(), 2);

        let changed_x = &diff.entries[0];
        assert_eq!(changed_x.kind, TrieJoinTraceReplayDiffKind::Changed);
        assert_eq!(changed_x.bound_prefix.as_ref(), [t(10)]);
        assert_eq!(
            changed_x.old_impact.as_ref().unwrap().step_indexes.as_ref(),
            [1, 2, 3]
        );
        assert_eq!(
            changed_x.new_impact.as_ref().unwrap().step_indexes.as_ref(),
            [1, 2, 3, 4]
        );

        let added_x3 = &diff.entries[1];
        assert_eq!(added_x3.kind, TrieJoinTraceReplayDiffKind::Added);
        assert_eq!(added_x3.bound_prefix.as_ref(), [t(10), t(3)]);
        assert_eq!(added_x3.old_impact, None);
        assert_eq!(added_x3.new_impact.as_ref().unwrap().candidate_bindings, 2);

        let reverse = new_replay.diff(&old_replay);
        assert_eq!(reverse.added_contexts, 0);
        assert_eq!(reverse.removed_contexts, 1);
        assert_eq!(reverse.changed_contexts, 1);
        assert_eq!(reverse.frontier_contexts, 1);
        assert_eq!(reverse.old_candidate_bindings_touched, 6);
        assert_eq!(reverse.new_candidate_bindings_touched, 4);
    }

    #[test]
    fn trie_join_trace_summary_rejects_inconsistent_domain_metadata() {
        let left = relation(&[0, 1], &[&[1, 10], &[2, 10]]);
        let right = relation(&[1, 2], &[&[10, 100], &[10, 101]]);
        let variable_order = [v(1), v(0), v(2)];
        let mut trace = trie_join_trace(&[left, right], &variable_order).unwrap();

        trace.steps[0].domain_values += 1;

        assert_eq!(
            trace.summarize().unwrap_err(),
            TrieJoinTraceShapeError::DomainValueMismatch {
                step: 0,
                expected: 2,
                actual: 3,
            }
        );
    }

    #[test]
    fn trie_join_trace_replay_rejects_missing_child_context() {
        let left = relation(&[0, 1], &[&[1, 10], &[2, 10]]);
        let right = relation(&[1, 2], &[&[10, 100], &[10, 101]]);
        let variable_order = [v(1), v(0), v(2)];
        let mut trace = trie_join_trace(&[left, right], &variable_order).unwrap();

        trace.steps = trace.steps[..trace.steps.len() - 1]
            .to_vec()
            .into_boxed_slice();

        assert_eq!(
            trace.replay_shape().unwrap_err(),
            TrieJoinTraceShapeError::MissingReplayStep {
                level: 2,
                bound_prefix_len: 2,
            }
        );
    }

    #[test]
    fn trie_join_trace_replay_rejects_wrong_bound_prefix_branch() {
        let left = relation(&[0, 1], &[&[1, 10], &[2, 10]]);
        let right = relation(&[1, 2], &[&[10, 100], &[10, 101]]);
        let variable_order = [v(1), v(0), v(2)];
        let mut trace = trie_join_trace(&[left, right], &variable_order).unwrap();
        trace.steps[2].bound_prefix[1] = t(2);

        assert_eq!(
            trace.replay_shape().unwrap_err(),
            TrieJoinTraceShapeError::BoundPrefixValueMismatch {
                step: 2,
                position: 1,
                expected: t(1),
                actual: t(2),
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
