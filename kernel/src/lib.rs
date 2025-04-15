pub mod space;
mod json_parser;
pub mod prefix;
mod space_temporary;
pub use space_temporary::*;

#[cfg(test)]
mod tests {
    use std::fs::File;
    use std::io::Read;
    use std::str::from_utf8_unchecked;
    use std::time::Instant;
    use mork_frontend::bytestring_parser::Parser as SExprParser;
    use mork_bytestring::{Expr, parse, compute_length, ExprZipper, serialize};
    use crate::{expr, sexpr, prefix};
    use crate::json_parser::{Parser, DebugTranscriber, WriteTranscriber};
    use crate::prefix::Prefix;
    use crate::space::*;

    #[test]
    fn prefix_parse_sexpr() {
        let input = "((nested and) (singleton))\n(foo bar)\n(1 \"test\" 2)\n";
        let mut s = Space::new();
        assert_eq!(s.load_sexpr(prefix!(s, "[2] my [2] prefix"), input).unwrap(), 3);
        let mut res = Vec::<u8>::new();
        s.dump_sexpr(prefix!(s, "[2] my [2] prefix"), &mut res).unwrap();
        assert_eq!(input, String::from_utf8(res).unwrap());
    }

    #[test]
    fn parse_csv() {
        let csv_input = "0,123,foo\n1,321,bar\n";
        let reconstruction = "(0 123 foo)\n(1 321 bar)\n";
        let mut s = Space::new();
        assert_eq!(s.load_csv_old(csv_input).unwrap(), 2);
        let mut res = Vec::<u8>::new();
        s.dump_sexpr(Prefix::NONE, &mut res).unwrap();
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

        assert_eq!(16, s.load_json(json_input).unwrap());

        let mut res = Vec::<u8>::new();
        s.dump_sexpr(Prefix::NONE, &mut res).unwrap();
        assert_eq!(SEXPRS0, String::from_utf8(res).unwrap());
    }

    #[test]
    fn query_simple() {
        let mut s = Space::new();
        assert_eq!(16, s.load_sexpr(Prefix::NONE, SEXPRS0).unwrap());

        let mut i = 0;
        s.query(expr!(s, "[2] children [2] $ $"), |_, e| {
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
        assert_eq!(16, s.load_sexpr(Prefix::NONE, SEXPRS0).unwrap());

        s.transform(expr!(s, "[2] children [2] $ $"), expr!(s, "[2] child_results _2"));
        let mut i = 0;
        s.query(expr!(s, "[2] child_results $"), |_, e| {
            match i {
                0 => { assert_eq!(sexpr!(s, e), "(child_results Catherine)") }
                1 => { assert_eq!(sexpr!(s, e), "(child_results Thomas)") }
                2 => { assert_eq!(sexpr!(s, e), "(child_results Trevor)") }
                _ => { assert!(false) }
            }
            i += 1;
        });
    }

    #[test]
    fn transform_multi() {
        let mut s = Space::new();
        let mut file = File::open("/home/adam/Projects/MORK/benchmarks/aunt-kg/resources/simpsons.metta").unwrap();
        let mut fileb = vec![]; file.read_to_end(&mut fileb);
        s.load_sexpr(Prefix::NONE, std::str::from_utf8(&fileb).unwrap()).unwrap();

        s.transform_multi(&[expr!(s, "[3] Individuals $ [2] Id $"),
                                   expr!(s, "[3] Individuals _1 [2] Fullname $")],
                          expr!(s, "[3] hasName _2 _3"));

        // let mut res = Vec::<u8>::new();
        // s.dump(&mut res).unwrap();
        // println!("{}", String::from_utf8(res).unwrap());
    }

    const LOGICSEXPR0: &str = r#"(axiom (= (L $x $y $z) (R $x $y $z)))
(axiom (= (L 1 $x $y) (R 1 $x $y)))
(axiom (= (R $x (L $x $y $z) $w) $x))
(axiom (= (R $x (R $x $y $z) $w) $x))
(axiom (= (R $x (L $x $y $z) $x) (L $x (L $x $y $z) $x)))
(axiom (= (L $x $y (\ $y $z)) (L $x $y $z)))
(axiom (= (L $x $y (* $z $y)) (L $x $y $z)))
(axiom (= (L $x $y (\ $z 1)) (L $x $z $y)))
(axiom (= (L $x $y (\ $z $y)) (L $x $z $y)))
(axiom (= (L $x 1 (\ $y 1)) (L $x $y 1)))
(axiom (= (T $x (L $x $y $z)) $x))
(axiom (= (T $x (R $x $y $z)) $x))
(axiom (= (T $x (a $x $y $z)) $x))
(axiom (= (T $x (\ (a $x $y $z) $w)) (T $x $w)))
(axiom (= (T $x (* $y $y)) (T $x (\ (a $x $z $w) (* $y $y)))))
(axiom (= (R (/ 1 $x) $x (\ $x 1)) (\ $x 1)))
(axiom (= (\ $x 1) (/ 1 (L $x $x (\ $x 1)))))
(axiom (= (L $x $x $x) (* (K $x (\ $x 1)) $x)))"#;

    #[test]
    fn subsumption() {
        let mut s = Space::new();
        s.load_sexpr(Prefix::NONE, LOGICSEXPR0).unwrap();

        // s.transform(expr!(s, "[2] axiom [3] = _2 _1"), expr!(s, "[2] flip [3] = $ $"));
        s.transform(expr!(s, "[2] axiom [3] = $ $"), expr!(s, "[2] flip [3] = _2 _1"));
        let mut c_in = 0; s.query(expr!(s, "[2] axiom [3] = $ $"), |_, e| c_in += 1);
        let mut c_out = 0; s.query(expr!(s, "[2] flip [3] = $ $"), |_, e| c_out += 1);
        assert_eq!(c_in, c_out);

        let mut res = Vec::<u8>::new();
        s.dump_sexpr(Prefix::NONE, &mut res).unwrap();
        println!("{}", String::from_utf8(res).unwrap());
    }

    #[test]
    fn big_subsumption() {
        let mut s = Space::new();
        let mut file = std::fs::File::open("/home/adam/Projects/MORK/benchmarks/logic-query/resources/big.metta")
          .expect("Should have been able to read the file");
        let mut buf = vec![];
        file.read_to_end(&mut buf).unwrap();
        s.load_sexpr(Prefix::NONE, unsafe { from_utf8_unchecked(&buf[..]) }).unwrap();

        // expr!(s, "[2] flip [3] \"=\" _2 _1")
        // s.transform(expr!(s, "[2] assert [3] forall $ $"), expr!(s, "axiom _2"));
        // s.transform(expr!(s, "[2] axiom [3] = $ $"), expr!(s, "[2] flip [3] = _2 _1"));
        // s.query(expr!(s, "[2] axiom [3] = $ $"), |e| { println!("> {}", sexpr!(s, e)) });
        let t0 = Instant::now();
        let mut k = 0;
        s.query(expr!(s, "$x"), |_, e| {
            k += 1;
            std::hint::black_box(e);
            // println!("> {}", sexpr!(s, e))
        });
        println!("iterating all ({}) took {} microseconds", k, t0.elapsed().as_micros());



        // let mut res = Vec::<u8>::new();
        // s.dump(&mut res).unwrap();
        // println!("{}", String::from_utf8(res).unwrap());
    }
}
