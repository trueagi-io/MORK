use crate::binding_env::MAX_BINDING_SLOTS;
use crate::term_identity::{FactId, TermId, TermIdentitySidecar, TermKind};

/// Query-planner variable identity produced by relationalized pattern lowering.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct PlanVariable(pub u16);

/// Origin of a lowered query-planner variable.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PlanVariableKind {
    /// User-visible encoded variable slot.
    UserSlot(u8),
    /// Planner-created variable for an application parent.
    Internal,
}

/// Metadata for one lowered planner variable.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PlanVariableRecord {
    /// Stable variable identity within the lowered pattern.
    pub id: PlanVariable,
    /// Variable origin.
    pub kind: PlanVariableKind,
}

/// Value appearing in a lowered application atom.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub enum PlanValue {
    /// Exact canonical term constant.
    Constant(TermId),
    /// Planner variable.
    Variable(PlanVariable),
}

/// Relationalized application constraint:
/// `App_n(parent, child0, child1, ...)`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ApplicationAtom {
    /// Encoded application arity.
    pub arity: u8,
    /// Parent term variable.
    pub parent: PlanVariable,
    /// Child constants or variables.
    pub children: Box<[PlanValue]>,
}

/// Sidecar lowering of one encoded MORK pattern into structural constraints.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PatternRelationPlan {
    root: PlanValue,
    atoms: Box<[ApplicationAtom]>,
    variables: Box<[PlanVariableRecord]>,
    user_slots: [Option<PlanVariable>; MAX_BINDING_SLOTS],
}

impl PatternRelationPlan {
    /// Root value that should be constrained by the fact-root relation.
    pub fn root(&self) -> PlanValue {
        self.root
    }

    /// Lowered application atoms.
    pub fn atoms(&self) -> &[ApplicationAtom] {
        &self.atoms
    }

    /// Planner variable metadata.
    pub fn variables(&self) -> &[PlanVariableRecord] {
        &self.variables
    }

    /// Returns the planner variable for a user-visible slot, if the slot occurs.
    pub fn user_slot(&self, slot: u8) -> Option<PlanVariable> {
        self.user_slots.get(usize::from(slot)).copied().flatten()
    }

    /// Number of distinct user-visible slots referenced by the pattern.
    pub fn user_slot_count(&self) -> usize {
        self.user_slots.iter().flatten().count()
    }
}

/// Errors from relationalized pattern lowering.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PatternLoweringError {
    /// The supplied root or one of its children is absent from the term sidecar.
    UnknownTerm { term: TermId },
    /// The pattern contains more than the six-bit variable-slot domain permits.
    TooManyUserSlots,
    /// More planner variables were needed than fit in the compact identifier.
    TooManyPlanVariables,
}

/// One row matched by a relationalized pattern plan.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PatternRelationRow {
    /// Complete fact root that matched the pattern.
    pub root: TermId,
    /// User-visible bindings in ascending slot order.
    pub user_bindings: Box<[(u8, TermId)]>,
}

/// Counters from sidecar-only pattern matching.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct PatternRelationMatchStats {
    /// Complete fact roots examined.
    pub facts_scanned: usize,
    /// Application atoms checked against candidate terms.
    pub app_atoms_checked: usize,
    /// Successful rows emitted.
    pub matches: usize,
}

/// Matched rows and counters.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct PatternRelationMatches {
    /// Matching rows.
    pub rows: Vec<PatternRelationRow>,
    /// Work counters.
    pub stats: PatternRelationMatchStats,
}

/// Errors from executing a relationalized sidecar plan.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PatternRelationMatchError {
    /// The sidecar is missing a requested complete fact record.
    UnknownFact { fact: FactId },
    /// The plan refers to a variable outside its variable table.
    UnknownVariable { variable: PlanVariable },
    /// The sidecar is missing a candidate term referenced by a fact or binding.
    UnknownTerm { term: TermId },
    /// More than one application atom used the same parent variable.
    DuplicateParentAtom { variable: PlanVariable },
}

/// Lowers one canonical term into a sidecar relational query plan.
///
/// This is not wired into the live matcher yet. It provides the measured
/// `App_n(parent, children...)` shape needed for the next BindingSpace/LFTJ
/// prototype while keeping PathMap byte semantics authoritative.
pub fn lower_pattern(
    sidecar: &TermIdentitySidecar,
    root: TermId,
) -> Result<PatternRelationPlan, PatternLoweringError> {
    let mut ctx = LoweringContext::new(sidecar);
    let root = ctx.lower(root)?;

    Ok(PatternRelationPlan {
        root,
        atoms: ctx.atoms.into_boxed_slice(),
        variables: ctx.variables.into_boxed_slice(),
        user_slots: ctx.user_slots,
    })
}

/// Executes a lowered pattern against complete fact roots in the term sidecar.
///
/// This is a comparison substrate for ground and repeated-variable facts. It
/// uses canonical `TermId` equality only and never invokes general unification.
pub fn match_facts(
    sidecar: &TermIdentitySidecar,
    plan: &PatternRelationPlan,
) -> Result<PatternRelationMatches, PatternRelationMatchError> {
    match_fact_ids(sidecar, plan, sidecar.facts().iter().map(|fact| fact.id))
}

/// Executes a lowered pattern against an explicit candidate set of fact IDs.
///
/// This is the exact filtering boundary used by derived indexes. Candidate
/// generation may be approximate, but every emitted row still passes through the
/// same canonical `TermId` equality checks as [`match_facts`].
pub fn match_fact_ids(
    sidecar: &TermIdentitySidecar,
    plan: &PatternRelationPlan,
    facts: impl IntoIterator<Item = FactId>,
) -> Result<PatternRelationMatches, PatternRelationMatchError> {
    let mut matcher = FactMatcher::new(sidecar, plan)?;
    let mut result = PatternRelationMatches::default();

    for fact_id in facts {
        let Some(fact) = sidecar.get_fact(fact_id) else {
            return Err(PatternRelationMatchError::UnknownFact { fact: fact_id });
        };
        result.stats.facts_scanned += 1;
        let mut state = MatchState::new(plan.variables.len(), plan.atoms.len());
        if matcher.match_root(&mut state, fact.root, &mut result.stats)? {
            result.stats.matches += 1;
            result.rows.push(PatternRelationRow {
                root: fact.root,
                user_bindings: state.user_bindings(plan).into_boxed_slice(),
            });
        }
    }

    Ok(result)
}

struct LoweringContext<'a> {
    sidecar: &'a TermIdentitySidecar,
    atoms: Vec<ApplicationAtom>,
    variables: Vec<PlanVariableRecord>,
    user_slots: [Option<PlanVariable>; MAX_BINDING_SLOTS],
    next_newvar_slot: u8,
}

impl<'a> LoweringContext<'a> {
    fn new(sidecar: &'a TermIdentitySidecar) -> Self {
        Self {
            sidecar,
            atoms: Vec::new(),
            variables: Vec::new(),
            user_slots: [None; MAX_BINDING_SLOTS],
            next_newvar_slot: 0,
        }
    }

    fn lower(&mut self, term: TermId) -> Result<PlanValue, PatternLoweringError> {
        let Some(record) = self.sidecar.get_term(term) else {
            return Err(PatternLoweringError::UnknownTerm { term });
        };

        match record.kind {
            TermKind::Symbol => Ok(PlanValue::Constant(term)),
            TermKind::NewVar => {
                let slot = self.next_newvar_slot;
                self.next_newvar_slot = self
                    .next_newvar_slot
                    .checked_add(1)
                    .ok_or(PatternLoweringError::TooManyUserSlots)?;
                Ok(PlanValue::Variable(self.user_slot(slot)?))
            }
            TermKind::VarRef(slot) => Ok(PlanValue::Variable(self.user_slot(slot)?)),
            TermKind::Application { arity } => {
                let parent = self.fresh_variable(PlanVariableKind::Internal)?;
                let children = record
                    .children()
                    .iter()
                    .copied()
                    .map(|child| self.lower(child))
                    .collect::<Result<Vec<_>, _>>()?;

                self.atoms.push(ApplicationAtom {
                    arity,
                    parent,
                    children: children.into_boxed_slice(),
                });

                Ok(PlanValue::Variable(parent))
            }
        }
    }

    fn user_slot(&mut self, slot: u8) -> Result<PlanVariable, PatternLoweringError> {
        let index = usize::from(slot);
        if index >= MAX_BINDING_SLOTS {
            return Err(PatternLoweringError::TooManyUserSlots);
        }

        if let Some(variable) = self.user_slots[index] {
            return Ok(variable);
        }

        let variable = self.fresh_variable(PlanVariableKind::UserSlot(slot))?;
        self.user_slots[index] = Some(variable);
        Ok(variable)
    }

    fn fresh_variable(
        &mut self,
        kind: PlanVariableKind,
    ) -> Result<PlanVariable, PatternLoweringError> {
        let id = u16::try_from(self.variables.len())
            .map_err(|_| PatternLoweringError::TooManyPlanVariables)?;
        let variable = PlanVariable(id);
        self.variables
            .push(PlanVariableRecord { id: variable, kind });
        Ok(variable)
    }
}

struct FactMatcher<'a> {
    sidecar: &'a TermIdentitySidecar,
    plan: &'a PatternRelationPlan,
    atom_by_parent: Vec<Option<usize>>,
}

impl<'a> FactMatcher<'a> {
    fn new(
        sidecar: &'a TermIdentitySidecar,
        plan: &'a PatternRelationPlan,
    ) -> Result<Self, PatternRelationMatchError> {
        let mut atom_by_parent = vec![None; plan.variables.len()];
        for (index, atom) in plan.atoms.iter().enumerate() {
            let parent = usize::from(atom.parent.0);
            let Some(slot) = atom_by_parent.get_mut(parent) else {
                return Err(PatternRelationMatchError::UnknownVariable {
                    variable: atom.parent,
                });
            };
            if slot.replace(index).is_some() {
                return Err(PatternRelationMatchError::DuplicateParentAtom {
                    variable: atom.parent,
                });
            }
        }

        Ok(Self {
            sidecar,
            plan,
            atom_by_parent,
        })
    }

    fn match_root(
        &mut self,
        state: &mut MatchState,
        root: TermId,
        stats: &mut PatternRelationMatchStats,
    ) -> Result<bool, PatternRelationMatchError> {
        self.match_value(state, self.plan.root, root, stats)
    }

    fn match_value(
        &mut self,
        state: &mut MatchState,
        value: PlanValue,
        term: TermId,
        stats: &mut PatternRelationMatchStats,
    ) -> Result<bool, PatternRelationMatchError> {
        match value {
            PlanValue::Constant(expected) => Ok(expected == term),
            PlanValue::Variable(variable) => self.bind_variable(state, variable, term, stats),
        }
    }

    fn bind_variable(
        &mut self,
        state: &mut MatchState,
        variable: PlanVariable,
        term: TermId,
        stats: &mut PatternRelationMatchStats,
    ) -> Result<bool, PatternRelationMatchError> {
        let index = usize::from(variable.0);
        let Some(binding) = state.bindings.get_mut(index) else {
            return Err(PatternRelationMatchError::UnknownVariable { variable });
        };

        if let Some(existing) = *binding {
            return Ok(existing == term);
        }

        *binding = Some(term);
        self.check_variable_atom(state, variable, stats)
    }

    fn check_variable_atom(
        &mut self,
        state: &mut MatchState,
        variable: PlanVariable,
        stats: &mut PatternRelationMatchStats,
    ) -> Result<bool, PatternRelationMatchError> {
        let variable_index = usize::from(variable.0);
        let Some(&maybe_atom) = self.atom_by_parent.get(variable_index) else {
            return Err(PatternRelationMatchError::UnknownVariable { variable });
        };
        let Some(atom_index) = maybe_atom else {
            return Ok(true);
        };
        if state.checked_atoms[atom_index] {
            return Ok(true);
        }

        let term = state.bindings[variable_index]
            .expect("variable should be bound before checking its application atom");
        let Some(record) = self.sidecar.get_term(term) else {
            return Err(PatternRelationMatchError::UnknownTerm { term });
        };
        let atom = &self.plan.atoms[atom_index];

        let TermKind::Application { arity } = record.kind else {
            return Ok(false);
        };
        if arity != atom.arity || record.children().len() != atom.children.len() {
            return Ok(false);
        }

        state.checked_atoms[atom_index] = true;
        stats.app_atoms_checked += 1;

        for (&child_value, &child_term) in atom.children.iter().zip(record.children()) {
            if !self.match_value(state, child_value, child_term, stats)? {
                return Ok(false);
            }
        }

        Ok(true)
    }
}

struct MatchState {
    bindings: Vec<Option<TermId>>,
    checked_atoms: Vec<bool>,
}

impl MatchState {
    fn new(variables: usize, atoms: usize) -> Self {
        Self {
            bindings: vec![None; variables],
            checked_atoms: vec![false; atoms],
        }
    }

    fn user_bindings(&self, plan: &PatternRelationPlan) -> Vec<(u8, TermId)> {
        plan.user_slots
            .iter()
            .enumerate()
            .filter_map(|(slot, variable)| {
                let variable = (*variable)?;
                let term = self.bindings[usize::from(variable.0)]?;
                Some((
                    u8::try_from(slot).expect("binding slot is within 0..64"),
                    term,
                ))
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::space::Space;
    use crate::term_identity::TermIdentitySidecar;
    use crate::test_exprs::{
        add_repeated_edge_facts, app, repeated_edge_pattern, repeated_edge_product_roots, sym, var,
        var_ref,
    };
    use std::collections::BTreeSet;

    fn lower_fact_pattern(
        pattern: Vec<u8>,
    ) -> (TermIdentitySidecar, PatternRelationPlan, PlanVariable) {
        let mut sidecar = TermIdentitySidecar::new();
        let fact = sidecar.insert_fact(&pattern).unwrap();
        let root = sidecar.get_fact(fact).unwrap().root;
        let plan = lower_pattern(&sidecar, root).unwrap();
        let PlanValue::Variable(root_variable) = plan.root() else {
            panic!("application root should lower to an internal variable");
        };
        (sidecar, plan, root_variable)
    }

    #[test]
    fn repeated_variable_pattern_lowers_to_shared_user_slot() {
        let inner = app(&[sym(b"f"), var_ref(0)]);
        let pattern = app(&[sym(b"edge"), var(), inner]);
        let (sidecar, plan, root_variable) = lower_fact_pattern(pattern);
        let user_slot = plan.user_slot(0).unwrap();
        let edge = sidecar.term_id_for_encoded(&sym(b"edge")).unwrap();

        assert_eq!(plan.user_slot_count(), 1);
        assert_eq!(
            plan.variables()[usize::from(root_variable.0)].kind,
            PlanVariableKind::Internal
        );
        assert_eq!(
            plan.variables()[usize::from(user_slot.0)].kind,
            PlanVariableKind::UserSlot(0)
        );

        let root_atom = plan
            .atoms()
            .iter()
            .find(|atom| atom.parent == root_variable)
            .unwrap();
        assert_eq!(root_atom.arity, 3);
        assert_eq!(root_atom.children[0], PlanValue::Constant(edge));
        assert_eq!(root_atom.children[1], PlanValue::Variable(user_slot));

        let PlanValue::Variable(inner_variable) = root_atom.children[2] else {
            panic!("nested application child should lower to an internal variable");
        };
        let inner_atom = plan
            .atoms()
            .iter()
            .find(|atom| atom.parent == inner_variable)
            .unwrap();
        assert_eq!(inner_atom.arity, 2);
        assert_eq!(inner_atom.children[1], PlanValue::Variable(user_slot));
    }

    #[test]
    fn ground_application_uses_constants_for_children() {
        let pattern = app(&[sym(b"edge"), sym(b"Alice"), sym(b"Bob")]);
        let (_, plan, root_variable) = lower_fact_pattern(pattern);
        let root_atom = plan
            .atoms()
            .iter()
            .find(|atom| atom.parent == root_variable)
            .unwrap();

        assert_eq!(plan.user_slot_count(), 0);
        assert!(root_atom
            .children
            .iter()
            .all(|value| matches!(value, PlanValue::Constant(_))));
    }

    #[test]
    fn unknown_term_returns_error() {
        let sidecar = TermIdentitySidecar::new();

        assert_eq!(
            lower_pattern(&sidecar, TermId(7)),
            Err(PatternLoweringError::UnknownTerm { term: TermId(7) })
        );
    }

    #[test]
    fn sidecar_matcher_preserves_product_query_roots_for_repeated_variable_pattern() {
        let mut space = Space::new();
        add_repeated_edge_facts(&mut space, b"");

        let pattern = repeated_edge_pattern();
        let mut sidecar = TermIdentitySidecar::new();
        let pattern_root = sidecar.insert_term(&pattern).unwrap();
        sidecar.extend_from_pathmap(&space.btm).unwrap();
        let plan = lower_pattern(&sidecar, pattern_root).unwrap();
        let sidecar_matches = match_facts(&sidecar, &plan).unwrap();

        let (product_count, product_roots) = repeated_edge_product_roots(&space);
        let sidecar_roots = sidecar_matches
            .rows
            .iter()
            .map(|row| sidecar.get_term(row.root).unwrap().encoded().to_vec())
            .collect::<BTreeSet<_>>();

        assert_eq!(product_count, 2);
        assert_eq!(sidecar_matches.stats.matches, product_count);
        assert_eq!(sidecar_matches.stats.facts_scanned, sidecar.stats().facts);
        assert_eq!(sidecar_roots, product_roots);
    }
}
