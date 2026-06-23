use std::collections::{BTreeMap, BTreeSet};

use crate::arrangements::{
    ArrangementDescriptor, ArrangementError, ArrangementIndex, ArrangementProjection,
};
use crate::binding_space::{
    generic_join, trie_join, BindingRelation, BindingRelationError, BindingVar, TrieJoinStats,
};
use crate::term_identity::TermIdentitySidecar;

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
    /// A BindingSpace relation operation failed.
    Binding(BindingRelationError),
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
        let mut relations = Vec::with_capacity(self.factors.len());

        for factor in self.factors.iter() {
            stats.factors += 1;
            let relation = factor.open(sidecar, &mut stats)?;
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
        }
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
    use crate::test_sidecar_queries::{transitive_edge_product_count, transitive_edge_sidecar};

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
}
