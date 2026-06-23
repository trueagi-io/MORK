use mork::expr;
use mork::space::Space;
use mork_expr::Expr;

fn dump(space: &Space, pattern: Expr, template: Expr) -> String {
    let mut output = Vec::new();
    space.dump_sexpr(pattern, template, &mut output);
    String::from_utf8(output).unwrap()
}

fn space_with(program: &[u8]) -> Space {
    let mut space = Space::new();
    space.add_all_sexpr(program).unwrap();
    space
}

fn dump_execs(space: &Space) -> String {
    dump(
        space,
        expr!(space, "[4] exec $ $ $"),
        expr!(space, "[4] exec _1 _2 _3"),
    )
}

fn dump_state_todo(space: &Space) -> String {
    dump(
        space,
        expr!(space, "[3] state todo $"),
        expr!(space, "[3] state todo _1"),
    )
}

fn dump_state_done(space: &Space) -> String {
    dump(
        space,
        expr!(space, "[3] state done $"),
        expr!(space, "[3] state done _1"),
    )
}

const REWRITE_ONCE_PROGRAM: &[u8] = br#"
(state todo task-1)

(exec rewrite-once
  (, (state todo $task))
  (O (- (state todo $task))
     (+ (state done $task))))
"#;

#[test]
fn rewrite_step_consumes_redex_and_materializes_reduct() {
    let mut space = space_with(REWRITE_ONCE_PROGRAM);

    assert_eq!(space.metta_calculus(1), 1);
    assert_eq!(dump_state_todo(&space), "");
    assert_eq!(dump_state_done(&space), "(state done task-1)\n");
}

#[test]
fn rewrite_step_consumes_exec_even_when_patterns_do_not_match() {
    let mut space = space_with(
        br#"
(state todo task-1)

(exec no-match
  (, (state blocked $task))
  (O (+ (state done $task))))
"#,
    );

    assert_eq!(space.metta_calculus(1), 1);
    assert_eq!(space.metta_calculus(1), 0);
    assert_eq!(dump_execs(&space), "");
    assert_eq!(dump_state_done(&space), "");
}

#[test]
fn rewrite_zero_step_budget_does_not_execute_redex() {
    let mut space = space_with(REWRITE_ONCE_PROGRAM);

    assert_eq!(space.metta_calculus(0), 0);
    assert_eq!(
        dump_execs(&space),
        "(exec rewrite-once (, (state todo $a)) (O (- (state todo $a)) (+ (state done $a))))\n"
    );
    assert_eq!(dump_state_todo(&space), "(state todo task-1)\n");
    assert_eq!(dump_state_done(&space), "");
}

#[test]
fn rewrite_step_uses_one_step_snapshot_before_effects() {
    let mut space = space_with(
        br#"
(state todo task-1)

(exec rewrite-once
  (, (state todo $task))
  (O (- (state todo $task))
     (+ (state done $task))
     (+ (saw-todo $task))))
"#,
    );

    assert_eq!(space.metta_calculus(1), 1);
    assert_eq!(
        dump(
            &space,
            expr!(space, "[2] saw-todo $"),
            expr!(space, "[2] saw-todo _1"),
        ),
        "(saw-todo task-1)\n"
    );
}

#[test]
fn rewrite_step_deduplicates_duplicate_add_templates() {
    let mut space = space_with(
        br#"
(seed item)

(exec duplicate-add
  (, (seed $value))
  (O (+ (out $value))
     (+ (out $value))))
"#,
    );

    assert_eq!(space.metta_calculus(1), 1);
    assert_eq!(
        dump(
            &space,
            expr!(space, "[2] out $"),
            expr!(space, "[2] out _1"),
        ),
        "(out item)\n"
    );
}

#[test]
fn rewrite_step_does_not_execute_generated_exec_until_next_step() {
    let mut space = space_with(
        br#"
(seed start)

(exec spawn-next
  (, (seed start))
  (O (+ (exec generated
           (, (seed start))
           (O (+ (result second-step)))))))
"#,
    );

    assert_eq!(space.metta_calculus(1), 1);
    assert_eq!(
        dump(
            &space,
            expr!(space, "[2] result $"),
            expr!(space, "[2] result _1"),
        ),
        ""
    );
    assert_eq!(
        dump_execs(&space),
        "(exec generated (, (seed start)) (O (+ (result second-step))))\n"
    );

    assert_eq!(space.metta_calculus(1), 1);
    assert_eq!(
        dump(
            &space,
            expr!(space, "[2] result $"),
            expr!(space, "[2] result _1"),
        ),
        "(result second-step)\n"
    );
    assert_eq!(space.metta_calculus(1), 0);
}

#[test]
fn rewrite_step_preserves_critical_alternatives_without_assuming_confluence() {
    let mut space = space_with(
        br#"
(choice seed)

(exec left-rule
  (, (choice seed))
  (O (+ (choice left))))

(exec right-rule
  (, (choice seed))
  (O (+ (choice right))))
"#,
    );

    assert_eq!(space.metta_calculus(2), 2);

    let choices = dump(
        &space,
        expr!(space, "[2] choice $"),
        expr!(space, "[2] choice _1"),
    );
    assert!(choices.contains("(choice seed)"), "{choices}");
    assert!(choices.contains("(choice left)"), "{choices}");
    assert!(choices.contains("(choice right)"), "{choices}");
}
