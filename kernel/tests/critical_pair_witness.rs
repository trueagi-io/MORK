use mork::critical_pairs::{Rule, Term, first_non_joinable_witness, rules_from_mm2_program};
use mork::expr;
use mork::space::Space;
use mork_expr::Expr;

fn dump(space: &Space, pattern: Expr, template: Expr) -> String {
    let mut output = Vec::new();
    space.dump_sexpr(pattern, template, &mut output);
    String::from_utf8(output).unwrap()
}

fn overlapping_rules() -> Vec<Rule> {
    vec![
        Rule::new(
            "outer-rule",
            Term::app(
                "f",
                vec![Term::app("g", vec![Term::var("x")]), Term::var("z")],
            ),
            Term::app("left", vec![Term::var("x"), Term::var("z")]),
        ),
        Rule::new(
            "inner-rule",
            Term::app("g", vec![Term::var("y")]),
            Term::app("right", vec![Term::var("y")]),
        ),
    ]
}

#[test]
fn critical_pair_witness_reports_non_joinable_overlap_as_mork_atom() {
    let witness = first_non_joinable_witness(&overlapping_rules(), 8).unwrap();

    assert_eq!(
        witness.to_metta_atom(),
        "(critical-pair outer-rule inner-rule p0 (f (g a) b) (left a b) (f (right a) b))"
    );

    let mut space = Space::new();
    space
        .add_all_sexpr(witness.to_metta_atom().as_bytes())
        .unwrap();

    assert_eq!(
        dump(
            &space,
            expr!(space, "[7] critical-pair $ $ $ $ $ $"),
            expr!(space, "[7] critical-pair _1 _2 _3 _4 _5 _6"),
        ),
        "(critical-pair outer-rule inner-rule p0 (f (g a) b) (left a b) (f (right a) b))\n"
    );
}

#[test]
fn critical_pair_witness_treats_bounded_joinable_overlap_as_closed() {
    let mut rules = overlapping_rules();
    rules.push(Rule::new(
        "close-rule",
        Term::app(
            "f",
            vec![Term::app("right", vec![Term::var("u")]), Term::var("v")],
        ),
        Term::app("left", vec![Term::var("u"), Term::var("v")]),
    ));

    assert!(first_non_joinable_witness(&rules, 8).is_none());
}

#[test]
fn critical_pair_witness_extracts_rules_from_real_mm2_exec_program_text() {
    let program = r#"
; Only finite first-order, single-pattern execs are extracted.
(exec outer-rule
  (, (f (g $x) $z))
  (O (- (f (g $x) $z))
     (+ (left $x $z))))

(exec inner-rule
  (, (g $y))
  (O (+ (right $y))))

; Multi-pattern execs are ordinary MM2, but not finite first-order rewrite rules.
(exec skipped-rule
  (, (guard $x) (f $x))
  (O (+ (guarded $x))))
"#;

    let rules = rules_from_mm2_program(program).unwrap();
    assert_eq!(rules.len(), 2);

    let witness = first_non_joinable_witness(&rules, 8).unwrap();
    assert_eq!(
        witness.to_metta_atom(),
        "(critical-pair outer-rule inner-rule p0 (f (g a) b) (left a b) (f (right a) b))"
    );
}

#[test]
fn critical_pair_witness_projects_multi_output_single_pattern_execs() {
    let rules = rules_from_mm2_program(include_str!("../resources/transitive.mm2")).unwrap();

    let rendered = rules
        .iter()
        .map(|rule| {
            format!(
                "{}: {} -> {}",
                rule.name,
                rule.lhs.to_metta(),
                rule.rhs.to_metta()
            )
        })
        .collect::<Vec<_>>();

    assert_eq!(
        rendered,
        vec![
            "0-out-0: (triangle $x $y $z) -> (edge $z $x)",
            "0-out-1: (triangle $x $y $z) -> (edge $y $z)",
            "0-out-2: (triangle $x $y $z) -> (edge $x $y)",
        ]
    );
}
