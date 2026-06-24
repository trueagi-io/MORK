use mork::expr;
use mork::space::Space;
use mork_expr::Expr;

fn dump(space: &Space, pattern: Expr, template: Expr) -> String {
    let mut output = Vec::new();
    space.dump_sexpr(pattern, template, &mut output);
    String::from_utf8(output).unwrap()
}

#[test]
fn repeated_variable_query_filters_non_unifying_facts() {
    let mut space = Space::new();
    let program = br#"
(Pair same same)
(Pair left right)

(exec repeated-variable-query
  (, (Pair $value $value))
  (O (+ (same-pair $value))))
"#;

    space.add_all_sexpr(program).unwrap();

    assert_eq!(space.metta_calculus(1), 1);
    let same_pairs = dump(
        &space,
        expr!(space, "[2] same-pair $"),
        expr!(space, "[2] same-pair _1"),
    );

    assert!(same_pairs.contains("(same-pair same)"), "{same_pairs}");
    assert!(!same_pairs.contains("(same-pair left)"), "{same_pairs}");
    assert!(!same_pairs.contains("(same-pair right)"), "{same_pairs}");
}

#[test]
fn equality_source_query_materializes_the_matched_term() {
    let mut space = Space::new();
    let program = br#"
(Knowledge (Some input))

(exec formal-query
  (I (== (Knowledge $value) $whole))
  (O (+ (query-result $whole))))
"#;

    space.add_all_sexpr(program).unwrap();

    assert_eq!(space.metta_calculus(1), 1);
    assert_eq!(
        dump(
            &space,
            expr!(space, "[2] query-result $"),
            expr!(space, "[2] query-result _1"),
        ),
        "(query-result (Knowledge (Some input)))\n"
    );
}

#[test]
fn transform_over_facts_preserves_conjunctive_bindings() {
    let mut space = Space::new();
    let program = br#"
(parent Pam Bob)
(parent Tom Bob)
(female Pam)

(exec transform-parent
  (, (parent $candidate Bob) (female $candidate))
  (O (+ (mother Bob $candidate))))
"#;

    space.add_all_sexpr(program).unwrap();

    assert_eq!(space.metta_calculus(1), 1);
    let mothers = dump(
        &space,
        expr!(space, "[3] mother Bob $"),
        expr!(space, "[3] mother Bob _1"),
    );

    assert!(mothers.contains("(mother Bob Pam)"), "{mothers}");
    assert!(!mothers.contains("Tom"), "{mothers}");
}

#[test]
fn context_rewrite_keeps_the_surrounding_expression_shape() {
    let mut space = Space::new();
    let program = br#"
(Wrapped (Some input))

(exec context-rewrite
  (, (Wrapped (Some $value)))
  (O (+ (Wrapped (Result $value)))))
"#;

    space.add_all_sexpr(program).unwrap();

    assert_eq!(space.metta_calculus(1), 1);
    assert_eq!(
        dump(
            &space,
            expr!(space, "[2] Wrapped [2] Result $"),
            expr!(space, "[2] Wrapped [2] Result _1"),
        ),
        "(Wrapped (Result input))\n"
    );
}

#[test]
fn query_to_chain_output_requires_a_later_machine_step() {
    let mut space = Space::new();
    let program = br#"
(seed start)

(exec a-stage
  (, (seed start))
  (O (+ (working-message (Wrapped input)))))

(exec z-stage
  (, (working-message (Wrapped $value)))
  (O (+ (formal-output (Wrapped $value)))))
"#;

    space.add_all_sexpr(program).unwrap();

    assert_eq!(space.metta_calculus(1), 1);
    assert_eq!(
        dump(
            &space,
            expr!(space, "[2] formal-output $"),
            expr!(space, "[2] formal-output _1"),
        ),
        ""
    );
    assert_eq!(
        dump(
            &space,
            expr!(space, "[2] working-message $"),
            expr!(space, "[2] working-message _1"),
        ),
        "(working-message (Wrapped input))\n"
    );

    assert_eq!(space.metta_calculus(1), 1);
    assert_eq!(
        dump(
            &space,
            expr!(space, "[2] formal-output $"),
            expr!(space, "[2] formal-output _1"),
        ),
        "(formal-output (Wrapped input))\n"
    );
}
