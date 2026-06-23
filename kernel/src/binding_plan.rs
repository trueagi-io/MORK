use std::collections::{BTreeMap, BTreeSet};

use crate::arrangements::{
    ArrangementDescriptor, ArrangementError, ArrangementIndex, ArrangementProjection,
};
use crate::binding_env::MAX_BINDING_SLOTS;
use crate::binding_space::{
    generic_join, trie_join, trie_join_trace, BindingRelation, BindingRelationError, BindingVar,
    TrieJoinStats, TrieJoinTrace, TrieJoinTraceReplayDiff, TrieJoinTraceShapeError,
};
use crate::expression_trie::{ExpressionTrieError, ExpressionTrieIndex};
use crate::term_identity::{TermId, TermIdentitySidecar};

/// Physical BindingSpace access selected by a compiled sidecar plan.
///
/// This describes derived access over the term snapshot. It does not change
/// the canonical PathMap/ACT pathspace semantics.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum BindingAccessPlan {
    /// Build or use an argument-order arrangement, then project it into a
    /// BindingSpace relation.
    Arrangement {
        descriptor: ArrangementDescriptor,
        projection: ArrangementProjection,
    },
    /// Use the typed expression trie to retrieve candidate facts for one
    /// pattern, exact-filter them, then project user-visible slots into a
    /// BindingSpace relation.
    Pattern {
        pattern: TermId,
        projection: PatternProjection,
    },
}

/// Projection from a matched pattern row into a BindingSpace relation schema.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PatternProjection {
    /// Output BindingSpace schema.
    pub schema: Box<[BindingVar]>,
    /// User-visible pattern slots for each schema variable.
    pub user_slots: Box<[u8]>,
}

impl PatternProjection {
    /// Creates a projection after validating arity and six-bit slot bounds.
    pub fn new(
        schema: impl Into<Box<[BindingVar]>>,
        user_slots: impl Into<Box<[u8]>>,
    ) -> Result<Self, BindingSidecarPlanError> {
        let schema = schema.into();
        let user_slots = user_slots.into();
        if schema.len() != user_slots.len() {
            return Err(BindingSidecarPlanError::PatternProjectionArityMismatch {
                schema_len: schema.len(),
                slots_len: user_slots.len(),
            });
        }
        for &slot in user_slots.iter() {
            if usize::from(slot) >= MAX_BINDING_SLOTS {
                return Err(BindingSidecarPlanError::InvalidPatternSlot { slot });
            }
        }

        Ok(Self { schema, user_slots })
    }
}

/// Sidecar join plan over derived BindingSpace relations.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BindingSidecarPlan {
    factors: Box<[BindingAccessPlan]>,
    variable_order: Box<[BindingVar]>,
}

/// Result of executing a sidecar join plan.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BindingSidecarResult {
    /// Flat relation returned by the current reference Generic Join oracle.
    pub relation: BindingRelation,
    /// Execution counters for checking that the sidecar plan shape is visible.
    pub stats: BindingSidecarStats,
}

/// Result of executing a sidecar plan with the trie-backed join kernel.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BindingSidecarTrieJoinResult {
    /// Flat relation returned by the trie-backed variable-at-a-time join.
    pub relation: BindingRelation,
    /// Variable order used by the trie-backed join.
    pub variable_order: Box<[BindingVar]>,
    /// Execution counters for physical factor opening.
    pub stats: BindingSidecarStats,
    /// Execution counters for the trie-backed join itself.
    pub trie_stats: TrieJoinStats,
}

/// Kernel selected for one sidecar execution.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BindingSidecarExecutionKernel {
    /// Reference variable-at-a-time Generic Join over opened relations.
    GenericJoin,
    /// Trie-backed LFTJ-style join using the root-domain suggested order.
    TrieJoinSuggested,
}

/// Why the sidecar planner selected an execution kernel.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BindingSidecarExecutionReason {
    /// A single factor does not need a multiway trie join.
    SingleFactor,
    /// No variable occurs in more than one factor, so there is no domain
    /// intersection to exploit before producing the Cartesian product.
    NoSharedVariables,
    /// The explicit opened sidecar input is too small to justify building
    /// trie indexes for this experimental kernel.
    SmallExplicitInput,
    /// Shared-variable domains are visible and the opened input is large
    /// enough that LFTJ-style pruning is the better physical experiment.
    SharedVariablePruning,
}

/// Planner-visible sidecar execution choice.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BindingSidecarExecutionChoice {
    /// Selected physical kernel.
    pub kernel: BindingSidecarExecutionKernel,
    /// Human-readable planner reason encoded as a stable enum.
    pub reason: BindingSidecarExecutionReason,
    /// Variable order consumed by the selected kernel.
    pub variable_order: Box<[BindingVar]>,
    /// Positive rows available across opened factor projections.
    pub projected_rows: usize,
    /// Variables appearing in more than one factor.
    pub shared_variables: usize,
    /// Smallest root-domain intersection across shared variables.
    pub min_shared_root_domain_len: Option<usize>,
}

/// Result of executing the sidecar plan through its selected kernel.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BindingSidecarSelectedResult {
    /// Flat relation returned by the selected kernel.
    pub relation: BindingRelation,
    /// Planner choice used for this execution.
    pub choice: BindingSidecarExecutionChoice,
    /// Execution counters for physical factor opening.
    pub stats: BindingSidecarStats,
    /// Trie counters when the trie-backed kernel was selected.
    pub trie_stats: Option<TrieJoinStats>,
}

/// Explain-only sidecar execution report.
///
/// This reports the physical kernel choice and the opened-factor statistics
/// used to choose it, but deliberately does not execute the final join.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BindingSidecarExecutionReport {
    /// Root-domain and factor statistics gathered while opening the plan.
    pub analysis: BindingSidecarAnalysis,
    /// Planner choice derived from the analysis.
    pub choice: BindingSidecarExecutionChoice,
}

/// Non-materializing trace for the selected trie-backed sidecar execution.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BindingSidecarTrieTraceReport {
    /// Planner analysis and selected execution kernel.
    pub execution: BindingSidecarExecutionReport,
    /// BindingRelation trie traversal trace when the selected kernel is
    /// trie-backed; `None` when the selector conservatively keeps Generic Join.
    pub trie_trace: Option<TrieJoinTrace>,
}

/// Explain-only diff between selected trie traces for two sidecar snapshots.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BindingSidecarTrieTraceDiffReport {
    /// Selected trace report for the previous snapshot.
    pub old: BindingSidecarTrieTraceReport,
    /// Selected trace report for the newer snapshot.
    pub new: BindingSidecarTrieTraceReport,
    /// Replay-shape diff when both snapshots select the trie-backed kernel.
    pub replay_diff: Option<TrieJoinTraceReplayDiff>,
}

/// Analysis of a sidecar join plan before choosing a production join kernel.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BindingSidecarAnalysis {
    /// Counters collected while opening the planned sidecar factors.
    pub stats: BindingSidecarStats,
    /// Root-level variable domains visible before any binding is chosen.
    pub variables: Box<[BindingVariableDomainStats]>,
    /// Heuristic variable order suitable for Generic Join and trie cursors.
    pub suggested_variable_order: Box<[BindingVar]>,
}

/// Root-level domain statistics for one BindingSpace variable.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct BindingVariableDomainStats {
    /// Query variable.
    pub variable: BindingVar,
    /// Number of factors containing this variable.
    pub factor_count: usize,
    /// Size of the intersection of positive domains from all containing
    /// factors, before any earlier variable is bound.
    pub root_domain_len: usize,
    /// Smallest positive domain contributed by one containing factor.
    pub min_factor_domain_len: usize,
    /// Largest positive domain contributed by one containing factor.
    pub max_factor_domain_len: usize,
}

/// Coarse execution counters for sidecar plans.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct BindingSidecarStats {
    /// Number of physical factor accesses opened by the plan.
    pub factors: usize,
    /// Complete fact roots inspected while constructing arrangements.
    pub facts_scanned: usize,
    /// Rows retained by constructed arrangements.
    pub arrangement_rows: usize,
    /// Expression-trie indexes built while opening this plan.
    pub expression_trie_builds: usize,
    /// Complete facts indexed into expression tries.
    pub expression_trie_facts_indexed: usize,
    /// Candidate facts returned by expression-trie prefix retrieval.
    pub expression_trie_candidates: usize,
    /// Application atoms checked by exact relationalized pattern filters.
    pub pattern_app_atoms_checked: usize,
    /// Exact pattern matches before BindingSpace projection.
    pub pattern_matches: usize,
    /// Positive BindingSpace rows produced by factor projections.
    pub projected_rows: usize,
    /// Positive rows emitted by the final join.
    pub output_rows: usize,
}

const MIN_TRIE_SIDE_INPUT_ROWS: usize = 8;

/// Error from sidecar plan execution.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BindingSidecarPlanError {
    /// A physical arrangement could not be built or projected.
    Arrangement(ArrangementError),
    /// Expression-trie candidate retrieval or exact filtering failed.
    ExpressionTrie(ExpressionTrieError),
    /// A BindingSpace relation operation failed.
    Binding(BindingRelationError),
    /// A generated trie trace failed replay-shape validation.
    TraceShape(TrieJoinTraceShapeError),
    /// Pattern projection schema and user-slot list have different lengths.
    PatternProjectionArityMismatch { schema_len: usize, slots_len: usize },
    /// Pattern projection requested a slot outside MORK's six-bit domain.
    InvalidPatternSlot { slot: u8 },
    /// Exact pattern matching did not bind a projected user slot.
    MissingPatternBinding { slot: u8 },
}

impl BindingSidecarPlan {
    /// Creates a sidecar plan from factor accesses and a variable order.
    pub fn new(
        factors: impl Into<Box<[BindingAccessPlan]>>,
        variable_order: impl Into<Box<[BindingVar]>>,
    ) -> Self {
        Self {
            factors: factors.into(),
            variable_order: variable_order.into(),
        }
    }

    /// Planned factor accesses.
    pub fn factors(&self) -> &[BindingAccessPlan] {
        &self.factors
    }

    /// Variable order consumed by Generic Join and trie-backed kernels.
    pub fn variable_order(&self) -> &[BindingVar] {
        &self.variable_order
    }

    /// Executes the plan against one term snapshot.
    pub fn execute(
        &self,
        sidecar: &TermIdentitySidecar,
    ) -> Result<BindingSidecarResult, BindingSidecarPlanError> {
        let (relations, mut stats) = self.open_relations(sidecar)?;

        let relation = generic_join(&relations, &self.variable_order)
            .map_err(BindingSidecarPlanError::Binding)?;
        stats.output_rows = relation.positive_rows().count();

        Ok(BindingSidecarResult { relation, stats })
    }

    /// Executes the plan using the trie-backed variable-at-a-time join kernel.
    ///
    /// The opened factors are still derived sidecars over the term snapshot;
    /// this does not change the canonical PathMap/ACT pathspace semantics.
    pub fn execute_trie_join(
        &self,
        sidecar: &TermIdentitySidecar,
    ) -> Result<BindingSidecarTrieJoinResult, BindingSidecarPlanError> {
        let (relations, mut stats) = self.open_relations(sidecar)?;

        let joined = trie_join(&relations, &self.variable_order)
            .map_err(BindingSidecarPlanError::Binding)?;
        stats.output_rows = joined.relation.positive_rows().count();

        Ok(BindingSidecarTrieJoinResult {
            relation: joined.relation,
            variable_order: self.variable_order.clone(),
            stats,
            trie_stats: joined.stats,
        })
    }

    /// Executes the plan with a root-domain heuristic variable order.
    ///
    /// This is still a sidecar experiment over opened `BindingRelation`s, not a
    /// replacement for the live ProductZipper matcher. It removes the need for
    /// tests and prototypes to hand-author the global LFTJ order when the plan
    /// already has exact root-domain evidence.
    pub fn execute_trie_join_suggested(
        &self,
        sidecar: &TermIdentitySidecar,
    ) -> Result<BindingSidecarTrieJoinResult, BindingSidecarPlanError> {
        let (relations, mut stats) = self.open_relations(sidecar)?;
        let variable_stats = variable_domain_stats(&relations);
        let variable_order = suggest_variable_order(&relations, &variable_stats);

        let joined =
            trie_join(&relations, &variable_order).map_err(BindingSidecarPlanError::Binding)?;
        stats.output_rows = joined.relation.positive_rows().count();

        Ok(BindingSidecarTrieJoinResult {
            relation: joined.relation,
            variable_order: variable_order.into_boxed_slice(),
            stats,
            trie_stats: joined.stats,
        })
    }

    /// Chooses the physical sidecar kernel from opened-factor statistics.
    ///
    /// This selection is deliberately conservative. It keeps the reference
    /// Generic Join for one-factor, disconnected, and tiny sidecar inputs, and
    /// only selects the trie-backed LFTJ-style kernel when shared-variable
    /// domain pruning can pay for query-specific index construction.
    pub fn choose_execution(
        &self,
        sidecar: &TermIdentitySidecar,
    ) -> Result<BindingSidecarExecutionChoice, BindingSidecarPlanError> {
        Ok(self.explain_execution(sidecar)?.choice)
    }

    /// Executes the sidecar plan through the selected physical kernel.
    ///
    /// This is still a derived sidecar path over the immutable term snapshot;
    /// it does not alter the canonical PathMap/ACT matching semantics.
    pub fn execute_selected(
        &self,
        sidecar: &TermIdentitySidecar,
    ) -> Result<BindingSidecarSelectedResult, BindingSidecarPlanError> {
        let (relations, stats) = self.open_relations(sidecar)?;
        let report = explain_execution_choice(&relations, &self.variable_order, stats);
        let choice = report.choice;
        let mut stats = report.analysis.stats;

        match choice.kernel {
            BindingSidecarExecutionKernel::GenericJoin => {
                let relation = generic_join(&relations, &choice.variable_order)
                    .map_err(BindingSidecarPlanError::Binding)?;
                stats.output_rows = relation.positive_rows().count();

                Ok(BindingSidecarSelectedResult {
                    relation,
                    choice,
                    stats,
                    trie_stats: None,
                })
            }
            BindingSidecarExecutionKernel::TrieJoinSuggested => {
                let joined = trie_join(&relations, &choice.variable_order)
                    .map_err(BindingSidecarPlanError::Binding)?;
                stats.output_rows = joined.relation.positive_rows().count();

                Ok(BindingSidecarSelectedResult {
                    relation: joined.relation,
                    choice,
                    stats,
                    trie_stats: Some(joined.stats),
                })
            }
        }
    }

    /// Explains the selected physical sidecar kernel without running the join.
    ///
    /// This is the BindingSidecar analogue of an optimizer explain plan: it
    /// opens the immutable snapshot factors to gather estimated/cardinality
    /// evidence, but leaves `output_rows` at zero because no result is emitted.
    pub fn explain_execution(
        &self,
        sidecar: &TermIdentitySidecar,
    ) -> Result<BindingSidecarExecutionReport, BindingSidecarPlanError> {
        let (relations, stats) = self.open_relations(sidecar)?;
        Ok(explain_execution_choice(
            &relations,
            &self.variable_order,
            stats,
        ))
    }

    /// Explains the selected execution and, when applicable, traces the
    /// trie-backed variable-domain traversal without materializing join rows.
    pub fn explain_selected_trie_trace(
        &self,
        sidecar: &TermIdentitySidecar,
    ) -> Result<BindingSidecarTrieTraceReport, BindingSidecarPlanError> {
        let (relations, stats) = self.open_relations(sidecar)?;
        let execution = explain_execution_choice(&relations, &self.variable_order, stats);
        let trie_trace = match execution.choice.kernel {
            BindingSidecarExecutionKernel::GenericJoin => None,
            BindingSidecarExecutionKernel::TrieJoinSuggested => Some(
                trie_join_trace(&relations, &execution.choice.variable_order)
                    .map_err(BindingSidecarPlanError::Binding)?,
            ),
        };

        Ok(BindingSidecarTrieTraceReport {
            execution,
            trie_trace,
        })
    }

    /// Explains and diffs selected trie traces across two immutable snapshots.
    ///
    /// The final join is still not executed. If either snapshot keeps the
    /// Generic Join kernel, `replay_diff` is `None` because there is no trie
    /// replay shape to compare.
    pub fn explain_selected_trie_trace_diff(
        &self,
        old_sidecar: &TermIdentitySidecar,
        new_sidecar: &TermIdentitySidecar,
    ) -> Result<BindingSidecarTrieTraceDiffReport, BindingSidecarPlanError> {
        let old = self.explain_selected_trie_trace(old_sidecar)?;
        let new = self.explain_selected_trie_trace(new_sidecar)?;

        let replay_diff = match (&old.trie_trace, &new.trie_trace) {
            (Some(old_trace), Some(new_trace)) => {
                let old_shape = old_trace
                    .replay_shape()
                    .map_err(BindingSidecarPlanError::TraceShape)?;
                let new_shape = new_trace
                    .replay_shape()
                    .map_err(BindingSidecarPlanError::TraceShape)?;
                Some(old_shape.diff(&new_shape))
            }
            _ => None,
        };

        Ok(BindingSidecarTrieTraceDiffReport {
            old,
            new,
            replay_diff,
        })
    }

    /// Opens all sidecar factors and reports root-domain statistics. This is a
    /// planning aid; it does not mutate the canonical PathMap/ACT storage.
    pub fn analyze(
        &self,
        sidecar: &TermIdentitySidecar,
    ) -> Result<BindingSidecarAnalysis, BindingSidecarPlanError> {
        let (relations, stats) = self.open_relations(sidecar)?;
        Ok(analyze_relations(&relations, stats))
    }

    fn open_relations(
        &self,
        sidecar: &TermIdentitySidecar,
    ) -> Result<(Vec<BindingRelation>, BindingSidecarStats), BindingSidecarPlanError> {
        let mut stats = BindingSidecarStats::default();
        let mut context = BindingOpenContext::default();
        let mut relations = Vec::with_capacity(self.factors.len());

        for factor in self.factors.iter() {
            stats.factors += 1;
            let relation = factor.open(sidecar, &mut stats, &mut context)?;
            stats.projected_rows += relation.positive_rows().count();
            relations.push(relation);
        }

        Ok((relations, stats))
    }
}

fn explain_execution_choice(
    relations: &[BindingRelation],
    planned_order: &[BindingVar],
    stats: BindingSidecarStats,
) -> BindingSidecarExecutionReport {
    let analysis = analyze_relations(relations, stats);
    let choice = select_execution_choice(relations.len(), planned_order, &analysis);

    BindingSidecarExecutionReport { analysis, choice }
}

fn select_execution_choice(
    relation_count: usize,
    planned_order: &[BindingVar],
    analysis: &BindingSidecarAnalysis,
) -> BindingSidecarExecutionChoice {
    let shared_variables = analysis
        .variables
        .iter()
        .filter(|stats| stats.factor_count > 1)
        .count();
    let min_shared_root_domain_len = analysis
        .variables
        .iter()
        .filter(|stats| stats.factor_count > 1)
        .map(|stats| stats.root_domain_len)
        .min();

    let (kernel, reason, variable_order) = if relation_count <= 1 {
        (
            BindingSidecarExecutionKernel::GenericJoin,
            BindingSidecarExecutionReason::SingleFactor,
            planned_order.to_vec(),
        )
    } else if shared_variables == 0 {
        (
            BindingSidecarExecutionKernel::GenericJoin,
            BindingSidecarExecutionReason::NoSharedVariables,
            planned_order.to_vec(),
        )
    } else if analysis.stats.projected_rows <= MIN_TRIE_SIDE_INPUT_ROWS {
        (
            BindingSidecarExecutionKernel::GenericJoin,
            BindingSidecarExecutionReason::SmallExplicitInput,
            planned_order.to_vec(),
        )
    } else {
        (
            BindingSidecarExecutionKernel::TrieJoinSuggested,
            BindingSidecarExecutionReason::SharedVariablePruning,
            analysis.suggested_variable_order.to_vec(),
        )
    };

    BindingSidecarExecutionChoice {
        kernel,
        reason,
        variable_order: variable_order.into_boxed_slice(),
        projected_rows: analysis.stats.projected_rows,
        shared_variables,
        min_shared_root_domain_len,
    }
}

impl BindingAccessPlan {
    fn open(
        &self,
        sidecar: &TermIdentitySidecar,
        stats: &mut BindingSidecarStats,
        context: &mut BindingOpenContext,
    ) -> Result<BindingRelation, BindingSidecarPlanError> {
        match self {
            BindingAccessPlan::Arrangement {
                descriptor,
                projection,
            } => {
                let arrangement = ArrangementIndex::build(sidecar, descriptor.clone())
                    .map_err(BindingSidecarPlanError::Arrangement)?;
                let arrangement_stats = arrangement.stats();
                stats.facts_scanned += arrangement_stats.facts_scanned;
                stats.arrangement_rows += arrangement_stats.rows;
                arrangement
                    .project_bindings(sidecar, projection)
                    .map_err(BindingSidecarPlanError::Arrangement)
            }
            BindingAccessPlan::Pattern {
                pattern,
                projection,
            } => {
                let index = context.expression_trie(sidecar, stats)?;
                let matches = index
                    .match_pattern(sidecar, *pattern)
                    .map_err(BindingSidecarPlanError::ExpressionTrie)?;
                stats.expression_trie_candidates += matches.candidates.facts.len();
                stats.pattern_app_atoms_checked += matches.exact.stats.app_atoms_checked;
                stats.pattern_matches += matches.exact.stats.matches;

                let mut relation = BindingRelation::new(projection.schema.clone());
                for row in matches.exact.rows {
                    let binding_row = projection
                        .user_slots
                        .iter()
                        .map(|&slot| {
                            row.user_bindings
                                .iter()
                                .find_map(|&(binding_slot, term)| {
                                    (binding_slot == slot).then_some(term)
                                })
                                .ok_or(BindingSidecarPlanError::MissingPatternBinding { slot })
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    relation
                        .add(binding_row, 1)
                        .map_err(BindingSidecarPlanError::Binding)?;
                }
                Ok(relation)
            }
        }
    }
}

#[derive(Default)]
struct BindingOpenContext {
    expression_trie: Option<ExpressionTrieIndex>,
}

impl BindingOpenContext {
    fn expression_trie<'a>(
        &'a mut self,
        sidecar: &TermIdentitySidecar,
        stats: &mut BindingSidecarStats,
    ) -> Result<&'a ExpressionTrieIndex, BindingSidecarPlanError> {
        if self.expression_trie.is_none() {
            let index = ExpressionTrieIndex::build(sidecar)
                .map_err(BindingSidecarPlanError::ExpressionTrie)?;
            stats.expression_trie_builds += 1;
            stats.expression_trie_facts_indexed += index.stats().facts_indexed;
            self.expression_trie = Some(index);
        }

        Ok(self
            .expression_trie
            .as_ref()
            .expect("expression trie was initialized above"))
    }
}

fn analyze_relations(
    relations: &[BindingRelation],
    stats: BindingSidecarStats,
) -> BindingSidecarAnalysis {
    let variable_stats = variable_domain_stats(relations);
    let suggested_variable_order = suggest_variable_order(relations, &variable_stats);

    BindingSidecarAnalysis {
        stats,
        variables: variable_stats.into_boxed_slice(),
        suggested_variable_order: suggested_variable_order.into_boxed_slice(),
    }
}

fn variable_domain_stats(relations: &[BindingRelation]) -> Vec<BindingVariableDomainStats> {
    let mut domains_by_variable = BTreeMap::<BindingVar, Vec<BTreeSet<_>>>::new();

    for relation in relations {
        for (index, &variable) in relation.schema().iter().enumerate() {
            let domain = relation
                .positive_rows()
                .map(|row| row[index])
                .collect::<BTreeSet<_>>();
            domains_by_variable
                .entry(variable)
                .or_default()
                .push(domain);
        }
    }

    domains_by_variable
        .into_iter()
        .map(|(variable, domains)| {
            let root_domain_len = intersect_domain_len(&domains);
            let min_factor_domain_len = domains.iter().map(BTreeSet::len).min().unwrap_or(0);
            let max_factor_domain_len = domains.iter().map(BTreeSet::len).max().unwrap_or(0);

            BindingVariableDomainStats {
                variable,
                factor_count: domains.len(),
                root_domain_len,
                min_factor_domain_len,
                max_factor_domain_len,
            }
        })
        .collect()
}

fn intersect_domain_len(domains: &[BTreeSet<crate::term_identity::TermId>]) -> usize {
    let Some((first, rest)) = domains.split_first() else {
        return 0;
    };

    let mut intersection = first.clone();
    for domain in rest {
        intersection = intersection
            .intersection(domain)
            .copied()
            .collect::<BTreeSet<_>>();
    }
    intersection.len()
}

fn suggest_variable_order(
    relations: &[BindingRelation],
    stats: &[BindingVariableDomainStats],
) -> Vec<BindingVar> {
    let stats_by_variable = stats
        .iter()
        .map(|stats| (stats.variable, *stats))
        .collect::<BTreeMap<_, _>>();
    let factor_schemas = relations
        .iter()
        .map(|relation| relation.schema().iter().copied().collect::<BTreeSet<_>>())
        .collect::<Vec<_>>();
    let mut remaining = stats.iter().map(|stats| stats.variable).collect::<Vec<_>>();
    let mut order = Vec::with_capacity(remaining.len());

    while !remaining.is_empty() {
        let has_connected = !order.is_empty()
            && remaining
                .iter()
                .any(|&variable| variable_connects_to_bound(variable, &order, &factor_schemas));
        let has_non_lonely = remaining
            .iter()
            .any(|variable| stats_by_variable[variable].factor_count > 1);

        remaining.sort_by(|&left, &right| {
            let left_connected = variable_connects_to_bound(left, &order, &factor_schemas);
            let right_connected = variable_connects_to_bound(right, &order, &factor_schemas);
            if has_connected && left_connected != right_connected {
                return right_connected.cmp(&left_connected);
            }

            let left_stats = stats_by_variable[&left];
            let right_stats = stats_by_variable[&right];
            let left_lonely = left_stats.factor_count == 1;
            let right_lonely = right_stats.factor_count == 1;
            if has_non_lonely && left_lonely != right_lonely {
                return left_lonely.cmp(&right_lonely);
            }

            left_stats
                .root_domain_len
                .cmp(&right_stats.root_domain_len)
                .then_with(|| right_stats.factor_count.cmp(&left_stats.factor_count))
                .then_with(|| left.cmp(&right))
        });

        order.push(remaining.remove(0));
    }

    order
}

fn variable_connects_to_bound(
    variable: BindingVar,
    bound: &[BindingVar],
    factor_schemas: &[BTreeSet<BindingVar>],
) -> bool {
    factor_schemas.iter().any(|schema| {
        schema.contains(&variable)
            && bound
                .iter()
                .any(|bound_variable| schema.contains(bound_variable))
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::space::Space;
    use crate::test_sidecar_queries::{
        encoded_expr, transitive_edge_product_count, transitive_edge_sidecar,
    };

    fn transitive_edge_plan(
        edge: crate::term_identity::TermId,
        variable_order: impl Into<Box<[BindingVar]>>,
    ) -> BindingSidecarPlan {
        let descriptor = ArrangementDescriptor::new(edge, 2, [0, 1]).unwrap();
        let xy = BindingAccessPlan::Arrangement {
            descriptor: descriptor.clone(),
            projection: ArrangementProjection::new(2, [BindingVar(0), BindingVar(1)], [0, 1])
                .unwrap(),
        };
        let yz = BindingAccessPlan::Arrangement {
            descriptor,
            projection: ArrangementProjection::new(2, [BindingVar(1), BindingVar(2)], [0, 1])
                .unwrap(),
        };

        BindingSidecarPlan::new([xy, yz], variable_order)
    }

    fn small_edge_sidecar() -> (Space, TermIdentitySidecar, crate::term_identity::TermId) {
        let mut space = Space::new();
        space
            .add_all_sexpr(
                br#"
(edge Alice Bob)
(edge Bob Carol)
"#,
            )
            .unwrap();

        let mut sidecar = TermIdentitySidecar::new();
        sidecar.extend_from_pathmap(&space.btm).unwrap();
        let edge = sidecar
            .term_id_for_encoded(&encoded_expr(&mut space, "edge"))
            .unwrap();

        (space, sidecar, edge)
    }

    fn colored_function_edges_sidecar() -> (
        Space,
        TermIdentitySidecar,
        crate::term_identity::TermId,
        crate::term_identity::TermId,
        crate::term_identity::TermId,
    ) {
        let mut space = Space::new();
        space
            .add_all_sexpr(
                br#"
(edge Alice (f Alice))
(edge Bob (f Bob))
(edge Carol (f Carol))
(edge Dave (f Eve))
(color Alice red)
(color Bob blue)
(color Carol red)
(color Eve red)
"#,
            )
            .unwrap();

        let mut sidecar = TermIdentitySidecar::new();
        let edge_pattern = sidecar
            .insert_term(&encoded_expr(&mut space, "[3] edge $ [2] f _1"))
            .unwrap();
        let color_pattern = sidecar
            .insert_term(&encoded_expr(&mut space, "[3] color $ $"))
            .unwrap();
        sidecar.extend_from_pathmap(&space.btm).unwrap();
        let color = sidecar
            .term_id_for_encoded(&encoded_expr(&mut space, "color"))
            .unwrap();

        (space, sidecar, edge_pattern, color, color_pattern)
    }

    fn rows_in_order(relation: &BindingRelation, order: &[BindingVar]) -> BTreeSet<Vec<TermId>> {
        let positions = order
            .iter()
            .map(|variable| {
                relation
                    .schema()
                    .iter()
                    .position(|candidate| candidate == variable)
                    .expect("requested variable should be present in relation schema")
            })
            .collect::<Vec<_>>();

        relation
            .positive_rows()
            .map(|row| positions.iter().map(|&position| row[position]).collect())
            .collect()
    }

    #[test]
    fn arrangement_sidecar_plan_matches_transitive_product_query() {
        let (mut space, sidecar, edge) = transitive_edge_sidecar();
        let plan = transitive_edge_plan(edge, [BindingVar(1), BindingVar(0), BindingVar(2)]);

        let result = plan.execute(&sidecar).unwrap();
        let product_count = transitive_edge_product_count(&mut space);

        assert_eq!(product_count, 4);
        assert_eq!(result.relation.positive_rows().count(), product_count);
        assert_eq!(
            result.stats,
            BindingSidecarStats {
                factors: 2,
                facts_scanned: 12,
                arrangement_rows: 12,
                projected_rows: 12,
                output_rows: 4,
                ..BindingSidecarStats::default()
            }
        );
    }

    #[test]
    fn trie_sidecar_plan_matches_generic_and_product_query() {
        let (mut space, sidecar, edge) = transitive_edge_sidecar();
        let plan = transitive_edge_plan(edge, [BindingVar(1), BindingVar(0), BindingVar(2)]);

        let generic = plan.execute(&sidecar).unwrap();
        let trie = plan.execute_trie_join(&sidecar).unwrap();
        let product_count = transitive_edge_product_count(&mut space);

        assert_eq!(trie.relation, generic.relation);
        assert_eq!(trie.relation.positive_rows().count(), product_count);
        assert_eq!(trie.trie_stats.output_rows, product_count);
        assert_eq!(trie.trie_stats.relation_indexes, 2);
        assert_eq!(trie.trie_stats.indexed_rows, 12);
        assert_eq!(trie.trie_stats.domain_intersections, 8);
        assert_eq!(
            trie.trie_stats.domain_cursor_opens,
            trie.trie_stats.domain_sources
        );
        assert!(trie.trie_stats.domain_cursor_seeks >= trie.trie_stats.domain_cursor_opens);
    }

    #[test]
    fn suggested_trie_join_order_preserves_rows_and_uses_small_shared_domain() {
        let (mut space, sidecar, edge) = transitive_edge_sidecar();
        let plan = transitive_edge_plan(edge, [BindingVar(0), BindingVar(1), BindingVar(2)]);

        let manual = plan.execute_trie_join(&sidecar).unwrap();
        let suggested = plan.execute_trie_join_suggested(&sidecar).unwrap();
        let product_count = transitive_edge_product_count(&mut space);

        assert_eq!(
            suggested.variable_order.as_ref(),
            [BindingVar(1), BindingVar(0), BindingVar(2)]
        );
        assert_eq!(manual.variable_order.as_ref(), plan.variable_order());
        assert_eq!(suggested.relation.positive_rows().count(), product_count);
        assert_eq!(suggested.trie_stats.output_rows, product_count);
        assert_eq!(
            rows_in_order(&suggested.relation, plan.variable_order()),
            rows_in_order(&manual.relation, plan.variable_order())
        );
    }

    #[test]
    fn selected_execution_uses_suggested_trie_join_for_shared_domains() {
        let (mut space, sidecar, edge) = transitive_edge_sidecar();
        let plan = transitive_edge_plan(edge, [BindingVar(0), BindingVar(1), BindingVar(2)]);

        let selected = plan.execute_selected(&sidecar).unwrap();
        let product_count = transitive_edge_product_count(&mut space);

        assert_eq!(
            selected.choice.kernel,
            BindingSidecarExecutionKernel::TrieJoinSuggested
        );
        assert_eq!(
            selected.choice.reason,
            BindingSidecarExecutionReason::SharedVariablePruning
        );
        assert_eq!(
            selected.choice.variable_order.as_ref(),
            [BindingVar(1), BindingVar(0), BindingVar(2)]
        );
        assert_eq!(selected.choice.projected_rows, 12);
        assert_eq!(selected.choice.shared_variables, 1);
        assert_eq!(selected.choice.min_shared_root_domain_len, Some(3));
        assert_eq!(selected.relation.positive_rows().count(), product_count);
        assert_eq!(selected.trie_stats.unwrap().output_rows, product_count);
    }

    #[test]
    fn execution_report_explains_selected_kernel_without_joining() {
        let (_, sidecar, edge) = transitive_edge_sidecar();
        let plan = transitive_edge_plan(edge, [BindingVar(0), BindingVar(1), BindingVar(2)]);

        let report = plan.explain_execution(&sidecar).unwrap();

        assert_eq!(
            report.choice.kernel,
            BindingSidecarExecutionKernel::TrieJoinSuggested
        );
        assert_eq!(
            report.choice.variable_order.as_ref(),
            [BindingVar(1), BindingVar(0), BindingVar(2)]
        );
        assert_eq!(report.analysis.stats.projected_rows, 12);
        assert_eq!(report.analysis.stats.output_rows, 0);
        assert_eq!(
            report.analysis.suggested_variable_order.as_ref(),
            report.choice.variable_order.as_ref()
        );
    }

    #[test]
    fn selected_trie_trace_matches_product_query_count_without_materializing_relation() {
        let (mut space, sidecar, edge) = transitive_edge_sidecar();
        let plan = transitive_edge_plan(edge, [BindingVar(0), BindingVar(1), BindingVar(2)]);

        let report = plan.explain_selected_trie_trace(&sidecar).unwrap();
        let product_count = transitive_edge_product_count(&mut space);
        let trace = report.trie_trace.unwrap();
        let summary = trace.summarize().unwrap();

        assert_eq!(
            report.execution.choice.kernel,
            BindingSidecarExecutionKernel::TrieJoinSuggested
        );
        assert_eq!(report.execution.analysis.stats.output_rows, 0);
        assert_eq!(
            trace.variable_order.as_ref(),
            [BindingVar(1), BindingVar(0), BindingVar(2)]
        );
        assert_eq!(trace.candidate_bindings, product_count);
        assert_eq!(trace.relation_indexes, 2);
        assert_eq!(trace.steps[0].variable, BindingVar(1));
        assert_eq!(trace.steps[0].participating_relations.as_ref(), [0, 1]);
        assert_eq!(trace.steps[0].relation_domain_lens.len(), 2);
        assert_eq!(trace.steps[0].domain_sources, 2);
        assert_eq!(trace.steps[0].intersection.len(), 3);
        assert_eq!(summary.candidate_bindings, product_count);
        assert_eq!(summary.max_participating_relations, 2);
        assert_eq!(summary.empty_intersections, 0);
    }

    #[test]
    fn selected_trie_trace_diff_compares_sidecar_snapshots_without_joining() {
        let (mut space, old_sidecar, edge) = transitive_edge_sidecar();
        let alice = old_sidecar
            .term_id_for_encoded(&encoded_expr(&mut space, "Alice"))
            .unwrap();
        let bob = old_sidecar
            .term_id_for_encoded(&encoded_expr(&mut space, "Bob"))
            .unwrap();

        let mut new_sidecar = old_sidecar.clone();
        new_sidecar
            .insert_fact(&encoded_expr(&mut space, "[3] edge Bob Erin"))
            .unwrap();

        let plan = transitive_edge_plan(edge, [BindingVar(0), BindingVar(1), BindingVar(2)]);

        let report = plan
            .explain_selected_trie_trace_diff(&old_sidecar, &new_sidecar)
            .unwrap();
        let diff = report.replay_diff.as_ref().unwrap();

        assert_eq!(
            report.old.execution.choice.kernel,
            BindingSidecarExecutionKernel::TrieJoinSuggested
        );
        assert_eq!(
            report.new.execution.choice.kernel,
            BindingSidecarExecutionKernel::TrieJoinSuggested
        );
        assert_eq!(report.old.execution.analysis.stats.output_rows, 0);
        assert_eq!(report.new.execution.analysis.stats.output_rows, 0);
        assert!(!diff.is_empty());
        assert_eq!(diff.changed_contexts, 1);
        assert_eq!(diff.added_contexts, 0);
        assert_eq!(diff.removed_contexts, 0);
        assert_eq!(diff.frontier_contexts, 1);
        assert_eq!(diff.old_replay_steps_touched, 1);
        assert_eq!(diff.new_replay_steps_touched, 1);
        assert_eq!(diff.old_candidate_bindings_touched, 1);
        assert_eq!(diff.new_candidate_bindings_touched, 2);
        assert_eq!(diff.entries.len(), 1);
        assert_eq!(diff.entries[0].bound_prefix.as_ref(), [bob, alice]);
    }

    #[test]
    fn execution_report_keeps_generic_join_for_tiny_shared_input() {
        let (_, sidecar, edge) = small_edge_sidecar();
        let plan = transitive_edge_plan(edge, [BindingVar(0), BindingVar(1), BindingVar(2)]);

        let report = plan.explain_execution(&sidecar).unwrap();

        assert_eq!(
            report.choice.kernel,
            BindingSidecarExecutionKernel::GenericJoin
        );
        assert_eq!(
            report.choice.reason,
            BindingSidecarExecutionReason::SmallExplicitInput
        );
        assert_eq!(report.choice.projected_rows, 4);
        assert_eq!(report.choice.shared_variables, 1);
        assert_eq!(report.choice.min_shared_root_domain_len, Some(1));
    }

    #[test]
    fn selected_trie_trace_is_absent_when_selector_keeps_generic_join() {
        let (_, sidecar, edge) = small_edge_sidecar();
        let plan = transitive_edge_plan(edge, [BindingVar(0), BindingVar(1), BindingVar(2)]);

        let report = plan.explain_selected_trie_trace(&sidecar).unwrap();

        assert_eq!(
            report.execution.choice.kernel,
            BindingSidecarExecutionKernel::GenericJoin
        );
        assert_eq!(
            report.execution.choice.reason,
            BindingSidecarExecutionReason::SmallExplicitInput
        );
        assert_eq!(report.trie_trace, None);
    }

    #[test]
    fn selected_execution_keeps_generic_join_for_single_factor() {
        let (_, sidecar, edge) = small_edge_sidecar();
        let descriptor = ArrangementDescriptor::new(edge, 2, [0, 1]).unwrap();
        let plan = BindingSidecarPlan::new(
            [BindingAccessPlan::Arrangement {
                descriptor,
                projection: ArrangementProjection::new(2, [BindingVar(0), BindingVar(1)], [0, 1])
                    .unwrap(),
            }],
            [BindingVar(0), BindingVar(1)],
        );

        let choice = plan.choose_execution(&sidecar).unwrap();
        let selected = plan.execute_selected(&sidecar).unwrap();

        assert_eq!(choice.kernel, BindingSidecarExecutionKernel::GenericJoin);
        assert_eq!(choice.reason, BindingSidecarExecutionReason::SingleFactor);
        assert_eq!(choice.variable_order.as_ref(), plan.variable_order());
        assert_eq!(selected.choice, choice);
        assert_eq!(selected.relation.positive_rows().count(), 2);
        assert_eq!(selected.trie_stats, None);
    }

    #[test]
    fn analysis_suggests_selective_connected_variable_order() {
        let (_, sidecar, edge) = transitive_edge_sidecar();
        let plan = transitive_edge_plan(edge, [BindingVar(0), BindingVar(1), BindingVar(2)]);

        let analysis = plan.analyze(&sidecar).unwrap();

        assert_eq!(
            analysis.suggested_variable_order.as_ref(),
            [BindingVar(1), BindingVar(0), BindingVar(2)]
        );
        assert_eq!(
            analysis.variables.as_ref(),
            [
                BindingVariableDomainStats {
                    variable: BindingVar(0),
                    factor_count: 1,
                    root_domain_len: 5,
                    min_factor_domain_len: 5,
                    max_factor_domain_len: 5,
                },
                BindingVariableDomainStats {
                    variable: BindingVar(1),
                    factor_count: 2,
                    root_domain_len: 3,
                    min_factor_domain_len: 5,
                    max_factor_domain_len: 5,
                },
                BindingVariableDomainStats {
                    variable: BindingVar(2),
                    factor_count: 1,
                    root_domain_len: 5,
                    min_factor_domain_len: 5,
                    max_factor_domain_len: 5,
                },
            ]
        );
    }

    #[test]
    fn expression_trie_pattern_factor_projects_repeated_variable_bindings() {
        let mut space = Space::new();
        space
            .add_all_sexpr(
                br#"
(edge Alice (f Alice))
(edge Alice (f Bob))
(edge Bob (f Bob))
(edge Carol (g Carol))
(edge Dave (f Eve))
(node Alice)
(tag Bob)
"#,
            )
            .unwrap();

        let mut sidecar = TermIdentitySidecar::new();
        let pattern = sidecar
            .insert_term(&encoded_expr(&mut space, "[3] edge $ [2] f _1"))
            .unwrap();
        sidecar.extend_from_pathmap(&space.btm).unwrap();
        let plan = BindingSidecarPlan::new(
            [BindingAccessPlan::Pattern {
                pattern,
                projection: PatternProjection::new([BindingVar(0)], [0]).unwrap(),
            }],
            [BindingVar(0)],
        );

        let result = plan.execute_trie_join(&sidecar).unwrap();
        let product_pattern = crate::expr!(space, "[2] , [3] edge $ [2] f _1");
        let product_count = Space::query_multi(&space.btm, product_pattern, |_, _| true);
        let alice = sidecar
            .term_id_for_encoded(&encoded_expr(&mut space, "Alice"))
            .unwrap();
        let bob = sidecar
            .term_id_for_encoded(&encoded_expr(&mut space, "Bob"))
            .unwrap();
        let projected = result
            .relation
            .positive_rows()
            .map(|row| row[0])
            .collect::<BTreeSet<_>>();

        assert_eq!(product_count, 2);
        assert_eq!(result.relation.positive_rows().count(), product_count);
        assert_eq!(projected, BTreeSet::from([alice, bob]));
        assert_eq!(result.stats.factors, 1);
        assert_eq!(result.stats.expression_trie_builds, 1);
        assert_eq!(result.stats.expression_trie_facts_indexed, 7);
        assert_eq!(result.stats.expression_trie_candidates, 5);
        assert_eq!(result.stats.pattern_matches, 2);
        assert_eq!(result.stats.projected_rows, 2);
        assert_eq!(result.trie_stats.output_rows, 2);
    }

    #[test]
    fn expression_trie_pattern_factor_joins_with_arrangement_factor() {
        let (mut space, sidecar, pattern, color, _) = colored_function_edges_sidecar();
        let descriptor = ArrangementDescriptor::new(color, 2, [0, 1]).unwrap();
        let plan = BindingSidecarPlan::new(
            [
                BindingAccessPlan::Pattern {
                    pattern,
                    projection: PatternProjection::new([BindingVar(0)], [0]).unwrap(),
                },
                BindingAccessPlan::Arrangement {
                    descriptor,
                    projection: ArrangementProjection::new(
                        2,
                        [BindingVar(0), BindingVar(1)],
                        [0, 1],
                    )
                    .unwrap(),
                },
            ],
            [BindingVar(0), BindingVar(1)],
        );

        let generic = plan.execute(&sidecar).unwrap();
        let trie = plan.execute_trie_join(&sidecar).unwrap();
        let product_pattern = crate::expr!(space, "[3] , [3] edge $ [2] f _1 [3] color _1 $");
        let product_count = Space::query_multi(&space.btm, product_pattern, |_, _| true);

        assert_eq!(product_count, 3);
        assert_eq!(trie.relation, generic.relation);
        assert_eq!(trie.relation.positive_rows().count(), product_count);
        assert_eq!(trie.stats.expression_trie_builds, 1);
        assert_eq!(trie.stats.expression_trie_candidates, 4);
        assert_eq!(trie.stats.pattern_matches, 3);
        assert_eq!(trie.stats.arrangement_rows, 4);
        assert_eq!(trie.trie_stats.output_rows, product_count);
    }

    #[test]
    fn expression_trie_pattern_factors_share_one_index_build() {
        let (mut space, sidecar, edge_pattern, _, color_pattern) = colored_function_edges_sidecar();
        let plan = BindingSidecarPlan::new(
            [
                BindingAccessPlan::Pattern {
                    pattern: edge_pattern,
                    projection: PatternProjection::new([BindingVar(0)], [0]).unwrap(),
                },
                BindingAccessPlan::Pattern {
                    pattern: color_pattern,
                    projection: PatternProjection::new([BindingVar(0), BindingVar(1)], [0, 1])
                        .unwrap(),
                },
            ],
            [BindingVar(0), BindingVar(1)],
        );

        let result = plan.execute_trie_join(&sidecar).unwrap();
        let product_pattern = crate::expr!(space, "[3] , [3] edge $ [2] f _1 [3] color _1 $");
        let product_count = Space::query_multi(&space.btm, product_pattern, |_, _| true);

        assert_eq!(product_count, 3);
        assert_eq!(result.relation.positive_rows().count(), product_count);
        assert_eq!(result.stats.factors, 2);
        assert_eq!(result.stats.expression_trie_builds, 1);
        assert_eq!(result.stats.expression_trie_facts_indexed, 8);
        assert_eq!(result.stats.expression_trie_candidates, 8);
        assert_eq!(result.stats.pattern_matches, 7);
        assert_eq!(result.stats.projected_rows, 7);
        assert_eq!(result.trie_stats.output_rows, product_count);
    }
}
