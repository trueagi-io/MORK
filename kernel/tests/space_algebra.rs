use mork::expr;
use mork::space::Space;

fn sorted_atoms(space: &Space) -> Vec<String> {
    let mut output = Vec::new();
    space.dump_all_sexpr(&mut output).unwrap();
    let mut atoms = String::from_utf8(output)
        .unwrap()
        .lines()
        .map(str::to_owned)
        .collect::<Vec<_>>();
    atoms.sort();
    atoms
}

#[test]
fn atom_union_combines_compatible_sexpr_spaces() {
    let root = Space::new();
    let mut left = root.fork_empty();
    let mut right = root.fork_empty();

    left.add_all_sexpr(
        br#"
(A one)
(A shared)
"#,
    )
    .unwrap();
    right
        .add_all_sexpr(
            br#"
(A shared)
(B two)
"#,
        )
        .unwrap();

    let union = left.atom_union(&right).unwrap();

    assert_eq!(
        sorted_atoms(&union),
        vec![
            "(A one)".to_string(),
            "(A shared)".to_string(),
            "(B two)".to_string(),
        ]
    );

    let mut output = Vec::new();
    union.dump_sexpr(
        expr!(union, "[2] A $"),
        expr!(union, "[2] A _1"),
        &mut output,
    );
    let output = String::from_utf8(output).unwrap();
    assert!(output.contains("(A one)"), "{output}");
    assert!(output.contains("(A shared)"), "{output}");
    assert!(!output.contains("(B two)"), "{output}");
}

#[test]
fn atom_intersection_keeps_only_shared_atoms() {
    let root = Space::new();
    let mut left = root.fork_empty();
    let mut right = root.fork_empty();

    left.add_all_sexpr(
        br#"
(A one)
(A shared)
"#,
    )
    .unwrap();
    right
        .add_all_sexpr(
            br#"
(A shared)
(B two)
"#,
        )
        .unwrap();

    let intersection = left.atom_intersection(&right).unwrap();

    assert_eq!(sorted_atoms(&intersection), vec!["(A shared)".to_string()]);
}

#[test]
fn atom_subtract_removes_atoms_present_in_right_space() {
    let root = Space::new();
    let mut left = root.fork_empty();
    let mut right = root.fork_empty();

    left.add_all_sexpr(
        br#"
(A one)
(A shared)
(B keep)
"#,
    )
    .unwrap();
    right
        .add_all_sexpr(
            br#"
(A shared)
(B drop)
"#,
        )
        .unwrap();

    let difference = left.atom_subtract(&right).unwrap();

    assert_eq!(
        sorted_atoms(&difference),
        vec!["(A one)".to_string(), "(B keep)".to_string()]
    );
}

#[test]
fn atom_algebra_rejects_independent_symbol_tables() {
    let mut left = Space::new();
    let mut right = Space::new();

    left.add_all_sexpr(b"(A one)").unwrap();
    right.add_all_sexpr(b"(A one)").unwrap();

    let err = match left.atom_union(&right) {
        Ok(_) => panic!("atom_union unexpectedly accepted independent symbol tables"),
        Err(err) => err,
    };

    assert!(
        err.contains("different symbol tables"),
        "unexpected error: {err}"
    );
}
