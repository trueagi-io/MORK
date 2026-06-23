use std::collections::BTreeSet;

use mork::critical_pairs::{
    Term, ground_facts_from_mm2_program, saturate_additive_state, saturate_additive_state_report,
    state_rule_successors, state_rules_from_mm2_program,
};

fn fact(name: &str, args: &[&str]) -> Term {
    Term::app(name, args.iter().map(|arg| Term::sym(*arg)).collect())
}

fn render_terms(terms: &[Term]) -> String {
    terms
        .iter()
        .map(Term::to_metta)
        .collect::<Vec<_>>()
        .join(", ")
}

#[test]
fn mm2_state_rules_extract_multi_pattern_execs_from_transitive_program() {
    let state_rules = state_rules_from_mm2_program(include_str!("../resources/transitive.mm2"))
        .expect("transitive fixture should parse");

    let rendered = state_rules
        .iter()
        .map(|rule| {
            format!(
                "{}: patterns=[{}] remove=[{}] add=[{}]",
                rule.name,
                render_terms(&rule.patterns),
                render_terms(&rule.remove),
                render_terms(&rule.add)
            )
        })
        .collect::<Vec<_>>();

    assert_eq!(
        rendered,
        vec![
            "0: patterns=[(triangle $x $y $z)] remove=[] add=[(edge $z $x), (edge $y $z), (edge $x $y)]",
            "1: patterns=[(edge $x $y), (edge $y $z)] remove=[] add=[(edge $x $z)]",
            "2: patterns=[(edge $z $x), (edge $y $z), (edge $x $y)] remove=[] add=[(triangle $x $y $z)]",
        ]
    );
}

#[test]
fn mm2_state_rule_successors_share_bindings_across_pattern_conjunctions() {
    let state_rules = state_rules_from_mm2_program(include_str!("../resources/transitive.mm2"))
        .expect("transitive fixture should parse");
    let state = BTreeSet::from([
        fact("edge", &["brussels", "paris"]),
        fact("edge", &["paris", "london"]),
    ]);

    let steps = state_rule_successors(&state, &state_rules[1]);

    assert_eq!(steps.len(), 1);
    assert_eq!(steps[0].rule, "1");
    assert_eq!(steps[0].add, vec![fact("edge", &["brussels", "london"])]);
    assert!(
        steps[0]
            .after
            .contains(&fact("edge", &["brussels", "london"]))
    );
}

#[test]
fn mm2_state_rule_successors_apply_remove_and_add_effects() {
    let program = r#"
(state todo task-1)

(exec move-task
  (, (state todo $task))
  (O (- (state todo $task))
     (+ (state done $task))))
"#;
    let state_rules = state_rules_from_mm2_program(program).expect("program should parse");
    let initial_facts = ground_facts_from_mm2_program(program).expect("initial facts should parse");

    let steps = state_rule_successors(&initial_facts, &state_rules[0]);

    assert_eq!(steps.len(), 1);
    assert_eq!(steps[0].remove, vec![fact("state", &["todo", "task-1"])]);
    assert_eq!(steps[0].add, vec![fact("state", &["done", "task-1"])]);
    assert!(!steps[0].after.contains(&fact("state", &["todo", "task-1"])));
    assert!(steps[0].after.contains(&fact("state", &["done", "task-1"])));
}

#[test]
fn mm2_state_rule_analyzer_saturates_transitive_program_facts() {
    let program = include_str!("../resources/transitive.mm2");
    let state_rules =
        state_rules_from_mm2_program(program).expect("transitive fixture should parse");
    let initial_facts = ground_facts_from_mm2_program(program).expect("initial facts should parse");

    assert_eq!(initial_facts.len(), 2);

    let saturated = saturate_additive_state(initial_facts, &state_rules, 8);

    assert_eq!(saturated.len(), 150);
    assert!(saturated.contains(&fact("edge", &["london", "istanbul"])));
    assert!(saturated.contains(&fact("edge", &["st-petersburg", "paris"])));
    assert!(saturated.contains(&fact("triangle", &["paris", "st-petersburg", "london"],)));
}

#[test]
fn additive_saturation_report_tracks_convergence_and_growth() {
    let program = r#"
(edge a b)
(edge b c)

(exec transitive
  (, (edge $x $y) (edge $y $z))
  (O (+ (edge $x $z))))
"#;
    let rules = state_rules_from_mm2_program(program).expect("program should parse");
    let initial = ground_facts_from_mm2_program(program).expect("initial facts should parse");

    let report = saturate_additive_state_report(initial.clone(), &rules, 4);
    let truncated = saturate_additive_state_report(initial, &rules, 0);

    assert_eq!(report.initial_facts, 2);
    assert_eq!(report.final_facts, 3);
    assert_eq!(report.derived_facts, 1);
    assert_eq!(report.rounds_executed, 2);
    assert!(report.converged);
    assert!(report.state.contains(&fact("edge", &["a", "c"])));

    assert_eq!(truncated.final_facts, 2);
    assert_eq!(truncated.rounds_executed, 0);
    assert!(!truncated.converged);
}
