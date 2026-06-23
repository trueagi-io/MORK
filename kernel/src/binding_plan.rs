use std::collections::{BTreeMap, BTreeSet};

use crate::arrangements::{
    ArrangementDescriptor, ArrangementError, ArrangementIndex, ArrangementProjection,
};
use crate::binding_env::MAX_BINDING_SLOTS;
use crate::binding_space::{
    generic_join, trie_join, BindingRelation, BindingRelationError, BindingVar, TrieJoinStats,
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

/// Error from sidecar plan execution.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BindingSidecarPlanError {
    /// A physical arrangement could not be built or projected.
    Arrangement(ArrangementError),
    /// Expression-trie candidate retrieval or exact filtering failed.
    ExpressionTrie(ExpressionTrieError),
    /// A BindingSpace relation operation failed.
    Binding(BindingRelationError),
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
