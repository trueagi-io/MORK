use mork::expr;
use mork::space::Space;
use mork_expr::Expr;

fn dump(space: &Space, pattern: Expr, template: Expr) -> String {
    let mut output = Vec::new();
    space.dump_sexpr(pattern, template, &mut output);
    String::from_utf8(output).unwrap()
}

#[test]
fn equality_source_freshens_variable_bearing_rows() {
    let mut space = Space::new();
    let program = br#"
(E ($x $x $x))

(exec equality-source
  (I (== (E ($x $x $x)) $e))
  (O (+ (seen $e))))
"#;

    space.add_all_sexpr(program).unwrap();

    assert_eq!(space.metta_calculus(1), 1);
    let seen = dump(
        &space,
        expr!(space, "[2] seen $"),
        expr!(space, "[2] seen _1"),
    );

    assert!(seen.contains("(seen (E ($a $a $a)))"), "{seen}");
}

#[test]
fn inequality_source_excludes_self_pairs() {
    let mut space = Space::new();
    let program = br#"
(VAL X)
(VAL Y)

(exec inequality-source
  (I (!= (VAL $x) (VAL $y)))
  (O (+ (neq $x $y))))
"#;

    space.add_all_sexpr(program).unwrap();

    assert_eq!(space.metta_calculus(1), 1);
    let pairs = dump(
        &space,
        expr!(space, "[3] neq $ $"),
        expr!(space, "[3] neq _1 _2"),
    );

    assert!(pairs.contains("(neq X Y)"), "{pairs}");
    assert!(pairs.contains("(neq Y X)"), "{pairs}");
    assert!(!pairs.contains("(neq X X)"), "{pairs}");
    assert!(!pairs.contains("(neq Y Y)"), "{pairs}");
}
