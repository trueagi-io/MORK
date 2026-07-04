use mork::space::Space;
use mork::{expr, prefix};

#[test]
fn prefix_macro_expands_outside_mork_crate_and_matches_expr_prefix() {
    let space = Space::new();

    let prefix = prefix!(space, "[3] fact parent target");
    let expression = expr!(space, "[3] fact parent target");
    let expected = unsafe { expression.prefix_non_proper().as_ref().unwrap() };

    assert_eq!(prefix.path(), expected);

    // Cross-primitive check: the returned path is a non-empty strict prefix of
    // the encoded span, so the macro cannot degenerate to the empty or the full
    // path regardless of how the non-proper offset is derived.
    let span = unsafe { expression.span().as_ref().unwrap() };
    assert!(!prefix.path().is_empty());
    assert!(prefix.path().len() < span.len());
    assert!(span.starts_with(prefix.path()));
}

#[test]
fn prefix_macro_stops_at_the_first_variable() {
    let space = Space::new();

    // A pattern with a variable has a genuinely proper prefix: the bytes up to
    // the variable position, which are exactly the lead-in it shares with the
    // ground expression that instantiates it.
    let var_prefix = prefix!(space, "[3] fact $ target");
    let var_expr = expr!(space, "[3] fact $ target");
    let var_span = unsafe { var_expr.span().as_ref().unwrap() };
    assert!(!var_prefix.path().is_empty());
    assert!(var_prefix.path().len() < var_span.len(), "prefix must stop before the variable");
    assert!(var_span.starts_with(var_prefix.path()));

    let ground_expr = expr!(space, "[3] fact parent target");
    let ground_span = unsafe { ground_expr.span().as_ref().unwrap() };
    assert!(ground_span.starts_with(var_prefix.path()));
}
