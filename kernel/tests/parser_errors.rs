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

#[test]
fn add_all_sexpr_accepts_the_widest_legal_form() {
    // 63 children total (head + 62 args) is the widest arity the encoding
    // carries; the guard must fire only on the bump past it.
    let mut expr = String::from("(Widest");
    for i in 0..62 {
        expr.push_str(&format!(" arg{i}"));
    }
    expr.push(')');

    let mut space = Space::new();
    space.add_all_sexpr(expr.as_bytes()).unwrap();

    let mut out = Vec::new();
    space.dump_all_sexpr(&mut out).unwrap();
    let dump = String::from_utf8_lossy(&out);
    assert!(dump.contains("Widest") && dump.contains("arg61"), "widest legal form must round-trip:\n{dump}");
}
