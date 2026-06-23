use crate::term_identity::{TermId, TermIdentitySidecar, TermKind};

/// Lowered view of one MM2 `exec` expression for semantic planning.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FormalExecPlan {
    /// Complete `exec` root term.
    pub root: TermId,
    /// Priority/location child of the `exec`.
    pub location: TermId,
    /// Pattern-list mode.
    pub source_mode: FormalListMode,
    /// Template-list mode.
    pub template_mode: FormalListMode,
    /// Lowered source factors.
    pub sources: Box<[FormalSourcePlan]>,
    /// Lowered template effects.
    pub effects: Box<[FormalTemplateEffect]>,
    /// Variable holes found inside source and effect terms.
    pub context_holes: Box<[FormalContextHole]>,
    /// Summary counters for optimizer guards.
    pub summary: FormalExecSummary,
}

/// Recognized source/template list mode.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FormalListMode {
    /// Ordinary comma list.
    Conjunction,
    /// `I` source list.
    SourceList,
    /// `O` sink/effect list.
    OutputList,
    /// A list head that is not currently specialized.
    Other(TermId),
}

/// One lowered source factor.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FormalSourcePlan {
    /// Source index in the pattern list.
    pub index: usize,
    /// Original source term.
    pub term: TermId,
    /// Recognized source kind.
    pub kind: FormalSourceKind,
}

/// Recognized source form.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FormalSourceKind {
    /// Direct BTM/pathspace pattern.
    PathPattern { pattern: TermId },
    /// Explicit `BTM` source wrapper.
    Btm { pattern: TermId },
    /// Explicit `ACT` source wrapper.
    Act { name: TermId, pattern: TermId },
    /// Equality source `(== lhs rhs)`.
    Equation { lhs: TermId, rhs: TermId },
    /// Inequality source `(!= lhs rhs)`.
    Inequality { lhs: TermId, rhs: TermId },
    /// External or not-yet-specialized source.
    Other,
}

/// One lowered template effect.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FormalTemplateEffect {
    /// Effect index in the template list.
    pub index: usize,
    /// Original effect term.
    pub term: TermId,
    /// Recognized effect kind.
    pub kind: FormalEffectKind,
    /// True when the emitted payload contains encoded variables.
    pub binding_sensitive: bool,
    /// True when the effect inserts an `exec` that must be observed by a later
    /// machine step, not by the current selected `exec`.
    pub adds_exec: bool,
    /// True when an add effect can only be consumed by a later machine step.
    pub later_step_output: bool,
}

/// Recognized template effect form.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FormalEffectKind {
    /// `(+ term)`.
    Add { term: TermId },
    /// `(- term)`.
    Remove { term: TermId },
    /// Other sink/effect such as ACT, z3, wasm, head/tail, or a compatibility
    /// template.
    Other,
}

/// Variable occurrence inside a source or effect term.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FormalContextHole {
    /// The source or effect that owns this hole.
    pub owner: FormalContextOwner,
    /// Child-index path from the owner term root to the variable item.
    pub path: Box<[u8]>,
    /// Variable occurrence kind.
    pub kind: FormalHoleKind,
}

/// Owner of a context hole.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FormalContextOwner {
    /// Hole inside a source factor.
    Source { index: usize },
    /// Hole inside a template effect payload.
    Effect { index: usize },
}

/// Encoded variable occurrence kind.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FormalHoleKind {
    /// `$` introduction, assigned a source-list slot in encounter order.
    NewVar { slot: u8 },
    /// `_n` reference to an existing source-list slot.
    VarRef { slot: u8 },
}

/// Summary counters for one lowered exec.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct FormalExecSummary {
    /// Number of lowered source factors.
    pub sources: usize,
    /// Number of equality sources.
    pub equation_sources: usize,
    /// Number of path/BTM/ACT pattern sources.
    pub path_sources: usize,
    /// Number of add effects.
    pub add_effects: usize,
    /// Number of remove effects.
    pub remove_effects: usize,
    /// Effects whose payload contains encoded variables.
    pub binding_sensitive_effects: usize,
    /// Effects whose payload is independent of match bindings.
    pub binding_insensitive_effects: usize,
    /// Add effects whose payload is itself an `exec`.
    pub added_execs: usize,
    /// Add effects whose inserted fact is not visible to the current selected
    /// `exec` and is therefore a chain/later-step output.
    pub later_step_outputs: usize,
    /// Number of enumerated variable holes.
    pub context_holes: usize,
}

/// Error while lowering an `exec` term.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FormalLoweringError {
    /// A referenced term is absent from the sidecar.
    UnknownTerm { term: TermId },
    /// A term expected to be an application was not an application.
    ExpectedApplication { term: TermId },
    /// The root was not shaped like `(exec location patterns templates)`.
    ExpectedExec { term: TermId },
    /// The pattern or template list was malformed.
    ExpectedList { term: TermId },
    /// Too many `$` introductions were encountered for the six-bit variable
    /// slot domain.
    TooManyNewVars,
}

/// MeTTa special form recognized without executing the term.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FormalMettaSpecialForm {
    /// Special result/data atom from the MeTTa specification.
    SpecialResult(FormalMettaSpecialResult),
    /// Minimal MeTTa instruction with the exact specified arity.
    MinimalInstruction(FormalMinimalInstruction),
    /// Function definition form `(= call-template body-template)`.
    FunctionDefinition,
    /// Type assignment form `(: atom type)`.
    TypeAssignment,
    /// Function type form `(-> arg-types... ret-type)`.
    FunctionType,
}

/// Special result atoms that must remain distinct during planning.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FormalMettaSpecialResult {
    /// `Empty`: the branch returned no results.
    Empty,
    /// `NotReducible`: the expression cannot reduce further.
    NotReducible,
    /// `()`: unit/side-effect result.
    Unit,
    /// `(Error atom message)`.
    Error { atom: TermId, message: TermId },
}

/// Minimal MeTTa instruction recognized by the interpreter.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FormalMinimalInstruction {
    /// `(eval atom)`.
    Eval,
    /// `(evalc atom context-space)`.
    Evalc,
    /// `(chain atom var template)`.
    Chain,
    /// `(unify atom pattern then else)`.
    Unify,
    /// `(decons-atom expression)`.
    DeconsAtom,
    /// `(cons-atom head tail)`.
    ConsAtom,
    /// `(function body)`.
    Function,
    /// `(return atom)`.
    Return,
    /// `(collapse-bind atom)`.
    CollapseBind,
    /// `(superpose-bind collapsed-results)`.
    SuperposeBind,
    /// `(metta atom type space)`.
    Metta,
    /// `(context-space)`.
    ContextSpace,
    /// `(call-native function-name function-pointer arguments)`.
    CallNative,
}

/// Lowers one canonical `exec` term into source/effect/context metadata.
pub fn lower_exec(
    sidecar: &TermIdentitySidecar,
    root: TermId,
) -> Result<FormalExecPlan, FormalLoweringError> {
    let exec_children = application_children(sidecar, root)?;
    if exec_children.len() != 4 || !symbol_is(sidecar, exec_children[0], b"exec")? {
        return Err(FormalLoweringError::ExpectedExec { term: root });
    }

    let location = exec_children[1];
    let pattern_list = exec_children[2];
    let template_list = exec_children[3];
    let (source_mode, source_terms) = list_terms(sidecar, pattern_list, ListSide::Source)?;
    let (template_mode, template_terms) = list_terms(sidecar, template_list, ListSide::Template)?;

    let mut next_newvar_slot = 0u8;
    let mut context_holes = Vec::new();
    let sources = source_terms
        .iter()
        .copied()
        .enumerate()
        .map(|(index, term)| {
            collect_holes(
                sidecar,
                term,
                FormalContextOwner::Source { index },
                &mut next_newvar_slot,
                &mut context_holes,
            )?;
            Ok(FormalSourcePlan {
                index,
                term,
                kind: source_kind(sidecar, term)?,
            })
        })
        .collect::<Result<Vec<_>, FormalLoweringError>>()?;

    let effects = template_terms
        .iter()
        .copied()
        .enumerate()
        .map(|(index, term)| {
            let kind = effect_kind(sidecar, term)?;
            if let Some(payload) = effect_payload(kind) {
                collect_holes(
                    sidecar,
                    payload,
                    FormalContextOwner::Effect { index },
                    &mut next_newvar_slot,
                    &mut context_holes,
                )?;
            }

            Ok(FormalTemplateEffect {
                index,
                term,
                kind,
                binding_sensitive: effect_payload(kind)
                    .is_some_and(|payload| term_contains_vars(sidecar, payload)),
                adds_exec: matches!(kind, FormalEffectKind::Add { term } if is_exec_term(sidecar, term)),
                later_step_output: matches!(kind, FormalEffectKind::Add { .. }),
            })
        })
        .collect::<Result<Vec<_>, FormalLoweringError>>()?;

    let summary = summarize(&sources, &effects, context_holes.len());

    Ok(FormalExecPlan {
        root,
        location,
        source_mode,
        template_mode,
        sources: sources.into_boxed_slice(),
        effects: effects.into_boxed_slice(),
        context_holes: context_holes.into_boxed_slice(),
        summary,
    })
}

/// Classifies MeTTa special forms without interpreting them.
///
/// Reserved symbols used with non-special arities intentionally return `None`;
/// the MeTTa specification allows those symbols to appear as ordinary data in
/// other contexts.
pub fn metta_special_form(
    sidecar: &TermIdentitySidecar,
    term: TermId,
) -> Result<Option<FormalMettaSpecialForm>, FormalLoweringError> {
    let Some(record) = sidecar.get_term(term) else {
        return Err(FormalLoweringError::UnknownTerm { term });
    };

    match record.kind {
        TermKind::Symbol => match symbol_payload(record.encoded()) {
            Some(b"Empty") => Ok(Some(FormalMettaSpecialForm::SpecialResult(
                FormalMettaSpecialResult::Empty,
            ))),
            Some(b"NotReducible") => Ok(Some(FormalMettaSpecialForm::SpecialResult(
                FormalMettaSpecialResult::NotReducible,
            ))),
            _ => Ok(None),
        },
        TermKind::Application { .. } => {
            let children = record.children();
            let Some((&head, args)) = children.split_first() else {
                return Ok(Some(FormalMettaSpecialForm::SpecialResult(
                    FormalMettaSpecialResult::Unit,
                )));
            };

            let Some(name) = symbol_name(sidecar, head)? else {
                return Ok(None);
            };

            if name == b"Error" && args.len() == 2 {
                return Ok(Some(FormalMettaSpecialForm::SpecialResult(
                    FormalMettaSpecialResult::Error {
                        atom: args[0],
                        message: args[1],
                    },
                )));
            }

            if let Some(instruction) = minimal_instruction(name, args.len()) {
                return Ok(Some(FormalMettaSpecialForm::MinimalInstruction(
                    instruction,
                )));
            }

            match (name, args.len()) {
                (b"=", 2) => Ok(Some(FormalMettaSpecialForm::FunctionDefinition)),
                (b":", 2) => Ok(Some(FormalMettaSpecialForm::TypeAssignment)),
                (b"->", 1..) => Ok(Some(FormalMettaSpecialForm::FunctionType)),
                _ => Ok(None),
            }
        }
        TermKind::NewVar | TermKind::VarRef(_) => Ok(None),
    }
}

fn minimal_instruction(name: &[u8], arity: usize) -> Option<FormalMinimalInstruction> {
    match (name, arity) {
        (b"eval", 1) => Some(FormalMinimalInstruction::Eval),
        (b"evalc", 2) => Some(FormalMinimalInstruction::Evalc),
        (b"chain", 3) => Some(FormalMinimalInstruction::Chain),
        (b"unify", 4) => Some(FormalMinimalInstruction::Unify),
        (b"decons-atom", 1) => Some(FormalMinimalInstruction::DeconsAtom),
        (b"cons-atom", 2) => Some(FormalMinimalInstruction::ConsAtom),
        (b"function", 1) => Some(FormalMinimalInstruction::Function),
        (b"return", 1) => Some(FormalMinimalInstruction::Return),
        (b"collapse-bind", 1) => Some(FormalMinimalInstruction::CollapseBind),
        (b"superpose-bind", 1) => Some(FormalMinimalInstruction::SuperposeBind),
        (b"metta", 3) => Some(FormalMinimalInstruction::Metta),
        (b"context-space", 0) => Some(FormalMinimalInstruction::ContextSpace),
        (b"call-native", 3) => Some(FormalMinimalInstruction::CallNative),
        _ => None,
    }
}

#[derive(Clone, Copy)]
enum ListSide {
    Source,
    Template,
}

fn list_terms(
    sidecar: &TermIdentitySidecar,
    term: TermId,
    side: ListSide,
) -> Result<(FormalListMode, &[TermId]), FormalLoweringError> {
    let children = application_children(sidecar, term)?;
    let Some((&head, rest)) = children.split_first() else {
        return Err(FormalLoweringError::ExpectedList { term });
    };
    let mode = if symbol_is(sidecar, head, b",")? {
        FormalListMode::Conjunction
    } else {
        match side {
            ListSide::Source if symbol_is(sidecar, head, b"I")? => FormalListMode::SourceList,
            ListSide::Template if symbol_is(sidecar, head, b"O")? => FormalListMode::OutputList,
            _ => FormalListMode::Other(head),
        }
    };
    Ok((mode, rest))
}

fn source_kind(
    sidecar: &TermIdentitySidecar,
    term: TermId,
) -> Result<FormalSourceKind, FormalLoweringError> {
    let Ok(children) = application_children(sidecar, term) else {
        return Ok(FormalSourceKind::PathPattern { pattern: term });
    };
    let Some((&head, args)) = children.split_first() else {
        return Ok(FormalSourceKind::Other);
    };

    if symbol_is(sidecar, head, b"==")? && args.len() == 2 {
        return Ok(FormalSourceKind::Equation {
            lhs: args[0],
            rhs: args[1],
        });
    }
    if symbol_is(sidecar, head, b"!=")? && args.len() == 2 {
        return Ok(FormalSourceKind::Inequality {
            lhs: args[0],
            rhs: args[1],
        });
    }
    if symbol_is(sidecar, head, b"BTM")? && args.len() == 1 {
        return Ok(FormalSourceKind::Btm { pattern: args[0] });
    }
    if symbol_is(sidecar, head, b"ACT")? && args.len() == 2 {
        return Ok(FormalSourceKind::Act {
            name: args[0],
            pattern: args[1],
        });
    }

    Ok(FormalSourceKind::PathPattern { pattern: term })
}

fn effect_kind(
    sidecar: &TermIdentitySidecar,
    term: TermId,
) -> Result<FormalEffectKind, FormalLoweringError> {
    let Ok(children) = application_children(sidecar, term) else {
        return Ok(FormalEffectKind::Other);
    };
    let Some((&head, args)) = children.split_first() else {
        return Ok(FormalEffectKind::Other);
    };

    if symbol_is(sidecar, head, b"+")? && args.len() == 1 {
        return Ok(FormalEffectKind::Add { term: args[0] });
    }
    if symbol_is(sidecar, head, b"-")? && args.len() == 1 {
        return Ok(FormalEffectKind::Remove { term: args[0] });
    }

    Ok(FormalEffectKind::Other)
}

fn effect_payload(kind: FormalEffectKind) -> Option<TermId> {
    match kind {
        FormalEffectKind::Add { term } | FormalEffectKind::Remove { term } => Some(term),
        FormalEffectKind::Other => None,
    }
}

fn collect_holes(
    sidecar: &TermIdentitySidecar,
    term: TermId,
    owner: FormalContextOwner,
    next_newvar_slot: &mut u8,
    out: &mut Vec<FormalContextHole>,
) -> Result<(), FormalLoweringError> {
    let mut path = Vec::new();
    collect_holes_at(sidecar, term, owner, next_newvar_slot, &mut path, out)
}

fn collect_holes_at(
    sidecar: &TermIdentitySidecar,
    term: TermId,
    owner: FormalContextOwner,
    next_newvar_slot: &mut u8,
    path: &mut Vec<u8>,
    out: &mut Vec<FormalContextHole>,
) -> Result<(), FormalLoweringError> {
    let Some(record) = sidecar.get_term(term) else {
        return Err(FormalLoweringError::UnknownTerm { term });
    };

    match record.kind {
        TermKind::NewVar => {
            let slot = *next_newvar_slot;
            *next_newvar_slot = next_newvar_slot
                .checked_add(1)
                .ok_or(FormalLoweringError::TooManyNewVars)?;
            out.push(FormalContextHole {
                owner,
                path: path.clone().into_boxed_slice(),
                kind: FormalHoleKind::NewVar { slot },
            });
        }
        TermKind::VarRef(slot) => {
            out.push(FormalContextHole {
                owner,
                path: path.clone().into_boxed_slice(),
                kind: FormalHoleKind::VarRef { slot },
            });
        }
        TermKind::Application { .. } => {
            for (index, child) in record.children().iter().copied().enumerate() {
                let Ok(index) = u8::try_from(index) else {
                    return Err(FormalLoweringError::ExpectedApplication { term });
                };
                path.push(index);
                collect_holes_at(sidecar, child, owner, next_newvar_slot, path, out)?;
                path.pop();
            }
        }
        TermKind::Symbol => {}
    }

    Ok(())
}

fn summarize(
    sources: &[FormalSourcePlan],
    effects: &[FormalTemplateEffect],
    context_holes: usize,
) -> FormalExecSummary {
    let equation_sources = sources
        .iter()
        .filter(|source| matches!(source.kind, FormalSourceKind::Equation { .. }))
        .count();
    let path_sources = sources
        .iter()
        .filter(|source| {
            matches!(
                source.kind,
                FormalSourceKind::PathPattern { .. }
                    | FormalSourceKind::Btm { .. }
                    | FormalSourceKind::Act { .. }
            )
        })
        .count();
    let add_effects = effects
        .iter()
        .filter(|effect| matches!(effect.kind, FormalEffectKind::Add { .. }))
        .count();
    let remove_effects = effects
        .iter()
        .filter(|effect| matches!(effect.kind, FormalEffectKind::Remove { .. }))
        .count();
    let binding_sensitive_effects = effects
        .iter()
        .filter(|effect| effect.binding_sensitive)
        .count();
    let binding_insensitive_effects = effects.len().saturating_sub(binding_sensitive_effects);
    let added_execs = effects.iter().filter(|effect| effect.adds_exec).count();
    let later_step_outputs = effects
        .iter()
        .filter(|effect| effect.later_step_output)
        .count();

    FormalExecSummary {
        sources: sources.len(),
        equation_sources,
        path_sources,
        add_effects,
        remove_effects,
        binding_sensitive_effects,
        binding_insensitive_effects,
        added_execs,
        later_step_outputs,
        context_holes,
    }
}

fn application_children(
    sidecar: &TermIdentitySidecar,
    term: TermId,
) -> Result<&[TermId], FormalLoweringError> {
    let Some(record) = sidecar.get_term(term) else {
        return Err(FormalLoweringError::UnknownTerm { term });
    };
    if !matches!(record.kind, TermKind::Application { .. }) {
        return Err(FormalLoweringError::ExpectedApplication { term });
    }
    Ok(record.children())
}

fn is_exec_term(sidecar: &TermIdentitySidecar, term: TermId) -> bool {
    let Ok(children) = application_children(sidecar, term) else {
        return false;
    };
    children.len() == 4 && symbol_is(sidecar, children[0], b"exec").unwrap_or(false)
}

fn term_contains_vars(sidecar: &TermIdentitySidecar, term: TermId) -> bool {
    sidecar
        .get_term(term)
        .is_some_and(|record| record.flags.contains_vars)
}

fn symbol_is(
    sidecar: &TermIdentitySidecar,
    term: TermId,
    expected: &[u8],
) -> Result<bool, FormalLoweringError> {
    Ok(symbol_name(sidecar, term)? == Some(expected))
}

fn symbol_name<'a>(
    sidecar: &'a TermIdentitySidecar,
    term: TermId,
) -> Result<Option<&'a [u8]>, FormalLoweringError> {
    let Some(record) = sidecar.get_term(term) else {
        return Err(FormalLoweringError::UnknownTerm { term });
    };
    Ok(matches!(record.kind, TermKind::Symbol)
        .then(|| symbol_payload(record.encoded()))
        .flatten())
}

fn symbol_payload(encoded: &[u8]) -> Option<&[u8]> {
    encoded.get(1..)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::space::Space;
    use crate::term_identity::TermIdentitySidecar;

    fn sidecar_for(program: &[u8]) -> (Space, TermIdentitySidecar) {
        let mut space = Space::new();
        space.add_all_sexpr(program).unwrap();
        let mut sidecar = TermIdentitySidecar::new();
        sidecar.extend_from_pathmap(&space.btm).unwrap();
        (space, sidecar)
    }

    fn encoded_expr(space: &mut Space, expr: &'static str) -> Vec<u8> {
        let expr = crate::expr!(space, expr);
        unsafe { expr.span().as_ref().unwrap() }.to_vec()
    }

    fn term_for(space: &mut Space, sidecar: &TermIdentitySidecar, expr: &'static str) -> TermId {
        sidecar
            .term_id_for_encoded(&encoded_expr(space, expr))
            .unwrap_or_else(|| panic!("missing term {expr}"))
    }

    fn exec_by_location(sidecar: &TermIdentitySidecar, name: &[u8]) -> TermId {
        for fact in sidecar.facts() {
            let Ok(children) = application_children(sidecar, fact.root) else {
                continue;
            };
            if children.len() == 4
                && symbol_is(sidecar, children[0], b"exec").unwrap()
                && symbol_is(sidecar, children[1], name).unwrap_or(false)
            {
                return fact.root;
            }
        }
        panic!("missing exec {}", String::from_utf8_lossy(name));
    }

    #[test]
    fn lower_exec_classifies_equation_sources_and_output_effects() {
        let (_space, sidecar) = sidecar_for(
            br#"
(Knowledge (Some input))
(exec formal-query
  (I (== (Knowledge $value) $whole))
  (O (+ (query-result $whole))))
"#,
        );

        let plan = lower_exec(&sidecar, exec_by_location(&sidecar, b"formal-query")).unwrap();

        assert_eq!(plan.source_mode, FormalListMode::SourceList);
        assert_eq!(plan.template_mode, FormalListMode::OutputList);
        assert_eq!(plan.sources.len(), 1);
        assert!(matches!(
            plan.sources[0].kind,
            FormalSourceKind::Equation { .. }
        ));
        assert_eq!(
            plan.summary,
            FormalExecSummary {
                sources: 1,
                equation_sources: 1,
                path_sources: 0,
                add_effects: 1,
                remove_effects: 0,
                binding_sensitive_effects: 1,
                binding_insensitive_effects: 0,
                added_execs: 0,
                later_step_outputs: 1,
                context_holes: 3,
            }
        );
    }

    #[test]
    fn lower_exec_marks_generated_exec_as_later_step() {
        let (_space, sidecar) = sidecar_for(
            br#"
(seed start)
(exec a-stage
  (, (seed start))
  (O (+ (exec generated
           (, (seed start))
           (O (+ (result second-step)))))))
"#,
        );

        let plan = lower_exec(&sidecar, exec_by_location(&sidecar, b"a-stage")).unwrap();

        assert_eq!(plan.effects.len(), 1);
        assert!(plan.effects[0].adds_exec);
        assert!(plan.effects[0].later_step_output);
        assert!(!plan.effects[0].binding_sensitive);
        assert_eq!(plan.summary.added_execs, 1);
        assert_eq!(plan.summary.later_step_outputs, 1);
        assert_eq!(plan.summary.binding_insensitive_effects, 1);
    }

    #[test]
    fn lower_exec_enumerates_nested_context_holes() {
        let (_space, sidecar) = sidecar_for(
            br#"
(Wrapped (Some input))
(exec context-rewrite
  (, (Wrapped (Some $value)))
  (O (+ (Wrapped (Result $value)))))
"#,
        );

        let plan = lower_exec(&sidecar, exec_by_location(&sidecar, b"context-rewrite")).unwrap();

        assert!(plan.context_holes.iter().any(|hole| {
            hole.owner == FormalContextOwner::Source { index: 0 }
                && hole.path.as_ref() == [1, 1]
                && hole.kind == FormalHoleKind::NewVar { slot: 0 }
        }));
        assert!(plan.context_holes.iter().any(|hole| {
            hole.owner == FormalContextOwner::Effect { index: 0 }
                && hole.path.as_ref() == [1, 1]
                && hole.kind == FormalHoleKind::VarRef { slot: 0 }
        }));
    }

    #[test]
    fn metta_special_form_distinguishes_result_atoms_from_unit_and_error() {
        let (mut space, sidecar) = sidecar_for(
            br#"
Empty
NotReducible
()
(Error bad message)
"#,
        );

        assert_eq!(
            metta_special_form(&sidecar, term_for(&mut space, &sidecar, "Empty")).unwrap(),
            Some(FormalMettaSpecialForm::SpecialResult(
                FormalMettaSpecialResult::Empty
            ))
        );
        assert_eq!(
            metta_special_form(&sidecar, term_for(&mut space, &sidecar, "NotReducible")).unwrap(),
            Some(FormalMettaSpecialForm::SpecialResult(
                FormalMettaSpecialResult::NotReducible
            ))
        );
        assert_eq!(
            metta_special_form(&sidecar, term_for(&mut space, &sidecar, "[0]")).unwrap(),
            Some(FormalMettaSpecialForm::SpecialResult(
                FormalMettaSpecialResult::Unit
            ))
        );

        let error = term_for(&mut space, &sidecar, "[3] Error bad message");
        let bad = term_for(&mut space, &sidecar, "bad");
        let message = term_for(&mut space, &sidecar, "message");
        assert_eq!(
            metta_special_form(&sidecar, error).unwrap(),
            Some(FormalMettaSpecialForm::SpecialResult(
                FormalMettaSpecialResult::Error { atom: bad, message }
            ))
        );
    }

    #[test]
    fn metta_special_form_recognizes_exact_arity_minimal_instructions() {
        let (mut space, sidecar) = sidecar_for(
            br#"
(eval target)
(evalc target ctx)
(chain (eval target) $x $x)
(unify $x Empty then else)
(decons-atom (A B))
(cons-atom A (B))
(function (return Done))
(collapse-bind (eval target))
(superpose-bind ((target bindings)))
(metta target Atom space)
(context-space)
(call-native name pointer args)
(eval target extra)
"#,
        );

        for (expr, instruction) in [
            ("[2] eval target", FormalMinimalInstruction::Eval),
            ("[3] evalc target ctx", FormalMinimalInstruction::Evalc),
            (
                "[4] chain [2] eval target $ _1",
                FormalMinimalInstruction::Chain,
            ),
            (
                "[5] unify $ Empty then else",
                FormalMinimalInstruction::Unify,
            ),
            (
                "[2] decons-atom [2] A B",
                FormalMinimalInstruction::DeconsAtom,
            ),
            ("[3] cons-atom A [1] B", FormalMinimalInstruction::ConsAtom),
            (
                "[2] function [2] return Done",
                FormalMinimalInstruction::Function,
            ),
            (
                "[2] collapse-bind [2] eval target",
                FormalMinimalInstruction::CollapseBind,
            ),
            (
                "[2] superpose-bind [1] [2] target bindings",
                FormalMinimalInstruction::SuperposeBind,
            ),
            (
                "[4] metta target Atom space",
                FormalMinimalInstruction::Metta,
            ),
            ("[1] context-space", FormalMinimalInstruction::ContextSpace),
            (
                "[4] call-native name pointer args",
                FormalMinimalInstruction::CallNative,
            ),
        ] {
            let term = term_for(&mut space, &sidecar, expr);
            assert_eq!(
                metta_special_form(&sidecar, term).unwrap(),
                Some(FormalMettaSpecialForm::MinimalInstruction(instruction)),
                "{expr}"
            );
        }

        let return_term = term_for(&mut space, &sidecar, "[2] return Done");
        assert_eq!(
            metta_special_form(&sidecar, return_term).unwrap(),
            Some(FormalMettaSpecialForm::MinimalInstruction(
                FormalMinimalInstruction::Return
            ))
        );

        let wrong_arity = term_for(&mut space, &sidecar, "[3] eval target extra");
        assert_eq!(metta_special_form(&sidecar, wrong_arity).unwrap(), None);
    }

    #[test]
    fn metta_special_form_recognizes_spec_forms_only_at_valid_arity() {
        let (mut space, sidecar) = sidecar_for(
            br#"
(= (id $x) $x)
(: id (-> Atom Atom))
(-> Atom Atom)
(= too many args here)
plain
"#,
        );

        assert_eq!(
            metta_special_form(
                &sidecar,
                term_for(&mut space, &sidecar, "[3] = [2] id $ _1")
            )
            .unwrap(),
            Some(FormalMettaSpecialForm::FunctionDefinition)
        );
        assert_eq!(
            metta_special_form(
                &sidecar,
                term_for(&mut space, &sidecar, "[3] : id [3] -> Atom Atom")
            )
            .unwrap(),
            Some(FormalMettaSpecialForm::TypeAssignment)
        );
        assert_eq!(
            metta_special_form(&sidecar, term_for(&mut space, &sidecar, "[3] -> Atom Atom"))
                .unwrap(),
            Some(FormalMettaSpecialForm::FunctionType)
        );
        assert_eq!(
            metta_special_form(
                &sidecar,
                term_for(&mut space, &sidecar, "[5] = too many args here")
            )
            .unwrap(),
            None
        );
        assert_eq!(
            metta_special_form(&sidecar, term_for(&mut space, &sidecar, "plain")).unwrap(),
            None
        );
    }
}
