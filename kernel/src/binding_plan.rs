use crate::arrangements::{
    ArrangementDescriptor, ArrangementError, ArrangementIndex, ArrangementProjection,
};
use crate::binding_space::{generic_join, BindingRelation, BindingRelationError, BindingVar};
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

    /// Variable order consumed by Generic Join / future LFTJ kernels.
    pub fn variable_order(&self) -> &[BindingVar] {
        &self.variable_order
    }

    /// Executes the plan against one term snapshot.
    pub fn execute(
        &self,
        sidecar: &TermIdentitySidecar,
    ) -> Result<BindingSidecarResult, BindingSidecarPlanError> {
        let mut stats = BindingSidecarStats::default();
        let mut relations = Vec::with_capacity(self.factors.len());

        for factor in self.factors.iter() {
            stats.factors += 1;
            let relation = factor.open(sidecar, &mut stats)?;
            stats.projected_rows += relation.positive_rows().count();
            relations.push(relation);
        }

        let relation = generic_join(&relations, &self.variable_order)
            .map_err(BindingSidecarPlanError::Binding)?;
        stats.output_rows = relation.positive_rows().count();

        Ok(BindingSidecarResult { relation, stats })
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_sidecar_queries::{transitive_edge_product_count, transitive_edge_sidecar};

    #[test]
    fn arrangement_sidecar_plan_matches_transitive_product_query() {
        let (mut space, sidecar, edge) = transitive_edge_sidecar();
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
        let plan = BindingSidecarPlan::new([xy, yz], [BindingVar(1), BindingVar(0), BindingVar(2)]);

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
}
