use mork_frontend::json_parser::{Error, Parser, Transcriber};

#[derive(Default)]
struct EventTranscriber;

impl Transcriber for EventTranscriber {
    fn descend_index(&mut self, _i: usize, _first: bool) {}

    fn ascend_index(&mut self, _i: usize, _last: bool) {}

    fn write_empty_array(&mut self) {}

    fn descend_key(&mut self, _k: &str, _first: bool) {}

    fn ascend_key(&mut self, _k: &str, _last: bool) {}

    fn write_empty_object(&mut self) {}

    fn write_string(&mut self, _s: &str) {}

    fn write_number(&mut self, _negative: bool, _mantissa: u64, _exponent: i16) {}

    fn write_true(&mut self) {}

    fn write_false(&mut self) {}

    fn write_null(&mut self) {}

    fn begin(&mut self) {}

    fn end(&mut self) {}
}

fn parse_error(input: &str) -> Error {
    let mut parser = Parser::new(input);
    let mut transcriber = EventTranscriber;
    parser.parse(&mut transcriber).unwrap_err()
}

#[test]
fn huge_positive_exponent_reports_depth_limit() {
    assert_eq!(parse_error("1e9999999999"), Error::ExceededDepthLimit);
}

#[test]
fn huge_negative_exponent_reports_depth_limit() {
    assert_eq!(parse_error("1e-9999999999"), Error::ExceededDepthLimit);
}

#[test]
fn huge_fractional_exponent_reports_depth_limit() {
    let input = format!("0.{}", "0".repeat(i16::MAX as usize + 2));

    assert_eq!(parse_error(&input), Error::ExceededDepthLimit);
}

fn parse_ok(input: &str) {
    let mut parser = Parser::new(input);
    let mut transcriber = EventTranscriber;
    parser.parse(&mut transcriber).unwrap();
}

#[test]
fn ordinary_large_exponents_still_parse() {
    // The overflow guard must reject only genuine i16-range overflow, not
    // numbers that merely look extreme.
    parse_ok("1e300");
    parse_ok("1.5e-300");
    parse_ok("-2.25e100");
    parse_ok("1e32000");
    parse_ok("1e-32000");
}
