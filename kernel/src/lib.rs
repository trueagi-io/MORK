pub mod space;
mod json_parser;

#[cfg(test)]
mod tests {
    use mork_frontend::bytestring_parser::Parser as SExprParser;
    use mork_bytestring::{Expr, parse, compute_length, ExprZipper, serialize};
    use crate::{expr, sexpr};
    use crate::json_parser::{Parser, DebugTranscriber, WriteTranscriber};
    use crate::space::*;

    #[test]
    fn parse_sexpr() {
        let input = "(foo bar)\n";
        let mut s = Space::new();
        assert_eq!(s.load_sexpr(input.as_bytes()).unwrap(), 1);
        let mut res = Vec::<u8>::new();
        s.dump(&mut res).unwrap();
        assert_eq!(input, String::from_utf8(res).unwrap());
    }

    #[test]
    fn parse_csv() {
        let csv_input = "0,123,foo\n1,321,bar\n";
        let reconstruction = "(0 123 foo)\n(1 321 bar)\n";
        let mut s = Space::new();
        assert_eq!(s.load_csv(csv_input.as_bytes()).unwrap(), 2);
        let mut res = Vec::<u8>::new();
        s.dump(&mut res).unwrap();
        assert_eq!(reconstruction, String::from_utf8(res).unwrap());
    }

    #[test]
    fn reconstruct_json() {
        let json_input = r#"{"first_name": "John", "last_name": "Smith", "is_alive": true, "age": 27, "address": {"street_address": "21 2nd Street", "city": "New York", "state": "NY", "postal_code": "10021-3100"}, "phone_numbers": [{"type": "home", "number": "212 555-1234"}, {"type": "office", "number": "646 555-4567"}], "children": ["Catherine", "Thomas", "Trevor"], "spouse": null}"#;

        let mut p = Parser::new(json_input);
        let mut wt = WriteTranscriber{ w: Vec::<u8>::new() };
        p.parse(&mut wt).unwrap();
        assert_eq!(json_input, String::from_utf8(wt.w).unwrap());
    }

    #[test]
    fn partial_reconstruct_numeric_json() {
        let json_input = r#"{"pos": 42, "neg": -100, "pi": 3.1415926, "winter": -20.5, "google": 1e+100}"#;
        let json_output = r#"{"pos": 42, "neg": -100, "pi": 31415926e-7, "winter": -205e-1, "google": 1e100}"#;

        let mut p = Parser::new(json_input);
        let mut wt = WriteTranscriber{ w: Vec::<u8>::new() };
        p.parse(&mut wt).unwrap();
        assert_eq!(json_output, String::from_utf8(wt.w).unwrap());
    }

    const SEXPRS0: &str = r#"(first_name John)
(last_name Smith)
(is_alive true)
(age 27)
(address (street_address 21 2nd Street))
(address (city New York))
(address (state NY))
(address (postal_code 10021-3100))
(phone_numbers (0 (type home)))
(phone_numbers (0 (number 212 555-1234)))
(phone_numbers (1 (type office)))
(phone_numbers (1 (number 646 555-4567)))
(children (0 Catherine))
(children (1 Thomas))
(children (2 Trevor))
(spouse null)
"#;

    #[test]
    fn parse_json() {
        let json_input = r#"{
"first_name": "John",
"last_name": "Smith",
"is_alive": true,
"age": 27,
"address": {
  "street_address": "21 2nd Street",
  "city": "New York",
  "state": "NY",
  "postal_code": "10021-3100"},
"phone_numbers": [
  {"type": "home", "number": "212 555-1234"},
  {"type": "office", "number": "646 555-4567"}],
"children": ["Catherine", "Thomas", "Trevor"],
"spouse": null}"#;

        let mut s = Space::new();

        assert_eq!(16, s.load_json(json_input.as_bytes()).unwrap());

        let mut res = Vec::<u8>::new();
        s.dump(&mut res).unwrap();
        assert_eq!(SEXPRS0, String::from_utf8(res).unwrap());
    }

    #[test]
    fn query_simple() {
        let mut s = Space::new();
        assert_eq!(16, s.load_sexpr(SEXPRS0.as_bytes()).unwrap());

        let mut i = 0;
        s.query(expr!(s, "[2] children [2] $ $"), |e| {
            match i {
                0 => { assert_eq!(sexpr!(s, e), "(children (0 Catherine))") }
                1 => { assert_eq!(sexpr!(s, e), "(children (1 Thomas))") }
                2 => { assert_eq!(sexpr!(s, e), "(children (2 Trevor))") }
                _ => { assert!(false) }
            }
            i += 1;
        });
    }

    #[test]
    fn transform_simple() {
        let mut s = Space::new();
        assert_eq!(16, s.load_sexpr(SEXPRS0.as_bytes()).unwrap());

        s.transform(expr!(s, "[2] children [2] $ $"), expr!(s, "[2] child_results _2"));
        let mut i = 0;
        s.query(expr!(s, "[2] child_results $"), |e| {
            match i {
                0 => { assert_eq!(sexpr!(s, e), "(child_results Catherine)") }
                1 => { assert_eq!(sexpr!(s, e), "(child_results Thomas)") }
                2 => { assert_eq!(sexpr!(s, e), "(child_results Trevor)") }
                _ => { assert!(false) }
            }
            i += 1;
        });
    }
}
