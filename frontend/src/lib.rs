#![feature(gen_blocks)]
#![feature(coroutine_trait)]
#![feature(coroutines)]
#![feature(stmt_expr_attributes)]

pub mod bytestring_parser;
pub mod json_parser;


/*
fn partial_reconstruct_numeric_json() {
    let json_input = r#"{"pos": 42, "neg": -100, "pi": 3.1415926, "winter": -20.5, "google": 1e+100}"#;
    let json_output = r#"{"pos": 42, "neg": -100, "pi": 31415926e-7, "winter": -205e-1, "google": 1e100}"#;

    let mut p = Parser::new(json_input);
    let mut wt = WriteTranscriber{ w: Vec::<u8>::new() };
    p.parse(&mut wt).unwrap();
    assert_eq!(json_output, String::from_utf8(wt.w).unwrap());
}
*/