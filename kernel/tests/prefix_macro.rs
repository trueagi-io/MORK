use mork::space::Space;
use mork::{expr, prefix};

#[test]
fn prefix_macro_expands_outside_mork_crate_and_matches_expr_prefix() {
    let space = Space::new();

    let prefix = prefix!(space, "[3] fact parent target");
    let expression = expr!(space, "[3] fact parent target");
    let expected = unsafe { expression.prefix_non_proper().as_ref().unwrap() };

    assert_eq!(prefix.path(), expected);
}
