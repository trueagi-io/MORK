use mork_expr::{Expr, parse};

fn expr_from_bytes(bytes: &mut [u8]) -> Expr {
    Expr {
        ptr: bytes.as_mut_ptr(),
    }
}

#[test]
fn serialize_highlight_consumes_single_target_without_panicking() {
    let mut bytes = parse!("[3] f a b");
    let expr = expr_from_bytes(&mut bytes);
    let mut output = Vec::new();

    expr.serialize_highlight(
        &mut output,
        |symbol| std::str::from_utf8(symbol).unwrap(),
        |_, intro| if intro { "$" } else { "_" },
        1,
    );

    let output = String::from_utf8(output).unwrap();
    assert_eq!(output, "(\u{1b}[43mf\u{1b}[0m a b)");
}
