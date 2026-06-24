use mork_expr::{Expr, ExprZipper, parse};

fn expr_from_bytes(bytes: &mut [u8]) -> Expr {
    Expr {
        ptr: bytes.as_mut_ptr(),
    }
}

fn substitute(template: &mut [u8], substitutions: &mut [&mut [u8]]) -> String {
    let template = expr_from_bytes(template);
    let substitutions = substitutions
        .iter_mut()
        .map(|bytes| expr_from_bytes(bytes))
        .collect::<Vec<_>>();
    let mut output = vec![0_u8; 256];
    let mut zipper = ExprZipper::new(expr_from_bytes(&mut output));

    template.substitute_de_bruijn(&substitutions, &mut zipper);

    format!("{:?}", expr_from_bytes(&mut output))
}

fn substitute_first_order(template: &mut [u8], substitutions: &mut [&mut [u8]]) -> Vec<u8> {
    let template = expr_from_bytes(template);
    let substitutions = substitutions
        .iter_mut()
        .map(|bytes| expr_from_bytes(bytes))
        .collect::<Vec<_>>();
    let expected_len = template.substitute_len(&substitutions);
    let mut output = vec![0_u8; expected_len];
    let mut zipper = ExprZipper::new(expr_from_bytes(&mut output));

    template.substitute(&substitutions, &mut zipper);

    assert_eq!(zipper.loc, expected_len);
    output
}

fn expr_from_output_offset(output: &mut [u8], offset: usize) -> Expr {
    Expr {
        ptr: unsafe { output.as_mut_ptr().add(offset) },
    }
}

#[test]
fn substitute_len_matches_first_order_substitution_output() {
    let mut template = parse!("[3] out $ _1");
    let mut substitution = parse!("[3] payload $ value");
    let mut output = substitute_first_order(&mut template, &mut [&mut substitution]);

    assert_eq!(
        format!("{:?}", expr_from_bytes(&mut output)),
        "(out (payload $ value) (payload $ value))"
    );
}

#[test]
fn substitute_de_bruijn_len_matches_shifted_output() {
    let mut template = parse!("[3] apply $ _1");
    let mut substitution = parse!("[3] pair $ $");
    let template_expr = expr_from_bytes(&mut template);
    let substitution_expr = expr_from_bytes(&mut substitution);
    let substitutions = [substitution_expr];
    let expected_len = template_expr.substitute_de_bruijn_len(&substitutions);
    let mut output = vec![0_u8; expected_len];
    let mut zipper = ExprZipper::new(expr_from_bytes(&mut output));

    template_expr.substitute_de_bruijn(&substitutions, &mut zipper);

    assert_eq!(zipper.loc, expected_len);
    assert_eq!(
        format!("{:?}", expr_from_bytes(&mut output)),
        "(apply (pair $ $) (pair _1 _2))"
    );
}

#[test]
fn substitute_one_de_bruijn_len_matches_output() {
    let mut template = parse!("[3] result $ _1");
    let mut replacement = parse!("[2] count 123");
    let template_expr = expr_from_bytes(&mut template);
    let replacement_expr = expr_from_bytes(&mut replacement);
    let expected_len = template_expr.substitute_one_de_bruijn_len(0, replacement_expr);
    let mut output = vec![0_u8; expected_len];
    let mut zipper = ExprZipper::new(expr_from_bytes(&mut output));

    template_expr.substitute_one_de_bruijn(0, replacement_expr, &mut zipper);

    assert_eq!(zipper.loc, expected_len);
    assert_eq!(
        format!("{:?}", expr_from_bytes(&mut output)),
        "(result (count 123) (count 123))"
    );
}

#[test]
fn transform_data_into_writes_exact_vector_length() {
    let mut data = parse!("[2] item [3] payload a b");
    let mut pattern = parse!("[2] item $");
    let mut template = parse!("[2] out _1");
    let mut output = Vec::with_capacity(1);

    expr_from_bytes(&mut data)
        .transformDataInto(
            expr_from_bytes(&mut pattern),
            expr_from_bytes(&mut template),
            &mut output,
        )
        .unwrap();

    assert!(output.capacity() >= output.len());
    assert!(output.len() > 1);
    assert_eq!(
        format!("{:?}", expr_from_bytes(&mut output)),
        "(out (payload a b))"
    );
}

#[test]
fn de_bruijn_substitution_shifts_reused_argument_variables() {
    let mut template = parse!("[3] apply $ _1");
    let mut substitution = parse!("[3] pair $ $");

    let result = substitute(&mut template, &mut [&mut substitution]);

    assert_eq!(result, "(apply (pair $ $) (pair _1 _2))");
}

#[test]
fn de_bruijn_substitution_keeps_distinct_free_slots_distinct() {
    let mut template = parse!("[4] body $ $ _1");
    let mut first = parse!("[2] first $");
    let mut second = parse!("[2] second $");

    let result = substitute(&mut template, &mut [&mut first, &mut second]);

    assert_eq!(result, "(body (first $) (second $) (first _1))");
}

#[test]
fn de_bruijn_substitution_shifts_later_slots_across_prior_binders() {
    let mut template = parse!("[5] body $ $ _2 _1");
    let mut first = parse!("[3] first $ _1");
    let mut second = parse!("[3] second $ _1");

    let result = substitute(&mut template, &mut [&mut first, &mut second]);

    assert_eq!(
        result,
        "(body (first $ _1) (second $ _2) (second _2 _2) (first _1 _1))"
    );
}

#[test]
fn de_bruijn_substitution_preserves_alpha_equivalent_identity_shape() {
    let mut template = parse!("[2] lambda $");
    let mut identity_body = parse!("$");

    let result = substitute(&mut template, &mut [&mut identity_body]);

    assert_eq!(result, "(lambda $)");
}

#[test]
fn de_bruijn_substitution_ivc_preserves_offsets_across_chunks() {
    let mut first_chunk = parse!("[2] left $");
    let mut second_chunk = parse!("[3] right $ _1");
    let mut first = parse!("[2] first $");
    let mut second = parse!("[2] second $");

    let mut output = vec![0_u8; 256];
    let mut zipper = ExprZipper::new(expr_from_bytes(&mut output));
    let substitutions = [expr_from_bytes(&mut first), expr_from_bytes(&mut second)];
    let mut var_count = 0;
    let mut additions = vec![0_u8; substitutions.len()];

    let first_start = zipper.loc;
    expr_from_bytes(&mut first_chunk).substitute_de_bruijn_ivc(
        &substitutions,
        &mut zipper,
        &mut var_count,
        &mut additions,
    );
    let second_start = zipper.loc;
    expr_from_bytes(&mut second_chunk).substitute_de_bruijn_ivc(
        &substitutions,
        &mut zipper,
        &mut var_count,
        &mut additions,
    );

    assert_eq!(
        format!("{:?}", expr_from_output_offset(&mut output, first_start)),
        "(left (first $))"
    );
    assert_eq!(
        format!("{:?}", expr_from_output_offset(&mut output, second_start)),
        "(right (second $) (first _1))"
    );
    assert_eq!(var_count, 2);
    assert_eq!(additions, [0, 1]);
}
