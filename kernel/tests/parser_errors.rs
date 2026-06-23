use mork::space::Space;

#[test]
fn add_all_sexpr_reports_too_many_variables_without_panicking() {
    let mut expr = String::from("(TooMany $x0 ");
    for i in 1..65 {
        expr.push_str(&format!("(Tail $x{i} "));
    }
    expr.push_str("end");
    for _ in 1..65 {
        expr.push(')');
    }
    expr.push(')');

    let mut space = Space::new();
    let err = space.add_all_sexpr(expr.as_bytes()).unwrap_err();

    assert!(err.contains("TooManyVars"), "{err}");
}

#[test]
fn add_all_sexpr_reports_too_many_arity_without_panicking() {
    let mut expr = String::from("(TooWide");
    for i in 0..64 {
        expr.push_str(&format!(" arg{i}"));
    }
    expr.push(')');

    let mut space = Space::new();
    let err = space.add_all_sexpr(expr.as_bytes()).unwrap_err();

    assert!(err.contains("TooManyArity"), "{err}");
}
