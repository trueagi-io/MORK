pub mod space;
mod json_parser;
pub mod prefix;
mod space_temporary;
pub use space_temporary::*;

pub use mork_bytestring::{ExprTrait, Expr, OwnedExpr};

#[cfg(test)]
mod tests {
    use std::fs::File;
    use std::io::Read;
    use std::time::Instant;
    use crate::{expr, sexpr};
    use crate::json_parser::{Parser, WriteTranscriber};
    use crate::space::*;


    fn set_from_newlines(input : &str) -> std::collections::BTreeSet<&str> {
        let mut set = std::collections::BTreeSet::new();
        for each in input.split('\n').filter(|s| !s.is_empty()) {
            set.insert(each);
        }
        set
    }

    #[test]
    fn prefix_parse_sexpr() {
        let input = "((nested and) (singleton))\n(foo bar)\n(1 \"test\" 2)\n";
        let mut s = DefaultSpace::new();
        assert_eq!(s.load_sexpr_simple(input.as_bytes(), expr!(s, "$"), expr!(s, "[2] my [2] prefix _1")).unwrap(), 3);
        let mut res = Vec::<u8>::new();
        s.dump_sexpr(expr!(s, "[2] my [2] prefix $"), expr!(s, "_1"), &mut res).unwrap();

        // the order changed in the test for some reason so we need to use sets to not be concerened by this
        let out = String::from_utf8(res).unwrap();
        assert_eq!(set_from_newlines(input), set_from_newlines(&out));
    }

    #[test]
    fn parse_csv_little() {
        let csv_input = "0,123,foo\n1,321,bar\n";
        let reconstruction = "(0 123 foo)\n(1 321 bar)\n";
        let mut s = DefaultSpace::new();
        assert_eq!(s.load_csv_simple(csv_input.as_bytes(), expr!(s, "$"), expr!(s, "_1"), b',', false).unwrap(), 2);
        let mut res = Vec::<u8>::new();
        s.dump_sexpr(expr!(s, "$"), expr!(s, "_1"),&mut res).unwrap();
        assert_eq!(reconstruction, String::from_utf8(res).unwrap());
    }

    #[test]
    fn parse_csv_big() {
        let csv_input = concat!("AA00,123,foo\n AA01,321,bar\n AA02,456,baz\n AA03,654,boz\n",
                                "AA04,123,foo\n AA05,321,bar\n AA06,456,baz\n AA07,654,boz\n",
                                "AA08,123,foo\n AA09,321,bar\n AA0A,456,baz\n AA0B,654,boz\n",
                                "AA0C,123,foo\n AA0D,321,bar\n AA0E,456,baz\n AA0F,654,boz\n",
                                "AA10,123,foo\n AA11,321,bar\n AA12,456,baz\n AA13,654,boz\n",
                                "AA14,123,foo\n AA15,321,bar\n AA16,456,baz\n AA17,654,boz\n",
                                "AA18,123,foo\n AA19,321,bar\n AA1A,456,baz\n AA1B,654,boz\n\n",
                                "AA1C,123,foo\n AA1D,321,bar\n AA1E,456,baz\n AA1F,654,boz\n",
                                "AA20,123,foo\n AA21,321,bar\n AA22,456,baz\n AA23,654,boz\n",
                                "AA24,123,foo\n AA25,321,bar\n AA26,456,baz\n AA27,654,boz\n\n\n",
                                "AA28,123,foo\n AA29,321,bar\n AA2A,456,baz\n AA2B,654,boz\n",
                                "AA2C,123,foo\n AA2D,321,bar\n AA2E,456,baz\n AA2F,654,boz\n",
                                "AA30,123,foo\n AA31,321,bar\n AA32,456,baz\n AA33,654,boz\n",
                                "AA34,123,foo\n AA35,321,bar\n AA36,456,baz\n AA37,654,boz\n\n\n\n",
                                "AA38,123,foo\n AA39,321,bar\n AA3A,456,baz\n AA3B,654,boz\n",
                                "AA3C,123,foo\n AA3D,321,bar\n AA3E,456,baz\n AA3F,654,boz\n",
                                "AA40,123,foo\n AA41,321,bar\n AA42,456,baz\n AA43,654,boz\n",
                                "AA44,123,foo\n AA45,321,bar\n AA46,456,baz\n AA47,654,boz\n",
                                "AA48,123,foo\n AA49,321,bar\n AA4A,456,baz\n AA4B,654,boz\n",
                                "AA4C,123,foo\n AA4D,321,bar\n AA4E,456,baz\n AA4F,654,boz",
        );
        let mut s = DefaultSpace::new();
        assert_eq!(s.load_csv_simple(csv_input.as_bytes(), expr!(s, "$"), expr!(s, "_1"), b',', true).unwrap(), 80);

        // let mut res = Vec::<u8>::new();
        // s.dump_sexpr(expr!(s, "$"), expr!(s, "_1"),&mut res).unwrap();
        // println!("\n{}", String::from_utf8_lossy(&res));

        s.query(expr!(s, "[4] 27 $ $ $"), |e| {
            assert_eq!(sexpr!(s, e), "((27  AA1B 654 boz))")
        });
        s.query(expr!(s, "[4] 28 $ $ $"), |e| {
            assert_eq!(sexpr!(s, e), "((28 AA1C 123 foo))")
        });
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

        let mut s = DefaultSpace::new();

        assert_eq!(16, s.load_json(json_input).unwrap());

        let mut res = Vec::<u8>::new();
        s.dump_sexpr(expr!(s, "$"), expr!(s, "_1"), &mut res).unwrap();

        let out = String::from_utf8(res).unwrap();
        assert_eq!(set_from_newlines(SEXPRS0), set_from_newlines(&out));
    }

    #[test]
    fn query_simple() {
        let mut s = DefaultSpace::new();
        assert_eq!(16, s.load_sexpr_simple( SEXPRS0.as_bytes(), expr!(s, "$"), expr!(s, "_1"),).unwrap());

        let mut i = 0;
        s.query(expr!(s, "[2] children [2] $ $"), |e| {
            match i {
                0 => { assert_eq!(sexpr!(s, e), "((children (0 Catherine)))") }
                1 => { assert_eq!(sexpr!(s, e), "((children (1 Thomas)))") }
                2 => { assert_eq!(sexpr!(s, e), "((children (2 Trevor)))") }
                _ => { assert!(false) }
            }
            i += 1;
        });
    }

    #[test]
    fn transform_simple() {
        let mut s = DefaultSpace::new();
        assert_eq!(16, s.load_sexpr_simple(SEXPRS0.as_bytes(), expr!(s, "$"), expr!(s, "_1"),).unwrap());

        s.transform(expr!(s, "[2] children [2] $ $"), expr!(s, "[2] child_results _2"));
        let mut i = 0;
        s.query(expr!(s, "[2] child_results $x"), |e| {
            match i {
                0 => { assert_eq!(sexpr!(s, e), "((child_results Thomas))") }
                1 => { assert_eq!(sexpr!(s, e), "((child_results Trevor))") }
                2 => { assert_eq!(sexpr!(s, e), "((child_results Catherine))") }
                _ => { assert!(false) }
            }
            i += 1;
        });
    }

    #[test]
    fn transform_multi() {
        let mut s = DefaultSpace::new();
        let mut file = File::open("/home/adam/Projects/MORK/benchmarks/aunt-kg/resources/simpsons.metta").unwrap();
        let mut fileb = vec![]; file.read_to_end(&mut fileb).unwrap();
        s.load_sexpr_simple( fileb.as_slice(), expr!(s, "$"), expr!(s, "_1")).unwrap();

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

    /// GOAT, this test passes with unification OFF, but fails with it ON
    #[test]
    fn subsumption_little() {
        let mut s = DefaultSpace::new();
        s.load_sexpr_simple(LOGICSEXPR0.as_bytes(), expr!(s, "$"), expr!(s, "_1")).unwrap();

        // s.transform(expr!(s, "[2] axiom [3] = _2 _1"), expr!(s, "[2] flip [3] = $ $"));
        s.transform(expr!(s, "[2] axiom [3] = $ $"), expr!(s, "[2] flip [3] = _2 _1"));
        let mut c_in = 0; s.query(expr!(s, "[2] axiom [3] = $ $"), |_e| c_in += 1);
        let mut c_out = 0; s.query(expr!(s, "[2] flip [3] = $ $"), |_e| c_out += 1);
        assert_eq!(c_in, c_out);

        let mut res = Vec::<u8>::new();
        s.dump_sexpr(expr!(s, "$"), expr!(s, "_1"), &mut res).unwrap();
        let out = String::from_utf8(res).unwrap();
        assert_eq!(out.lines().count(), 36);
        println!("{}", out);
    }

    #[test]
    fn subsumption_big() {
        let mut s = DefaultSpace::new();
        let mut file = std::fs::File::open("/home/adam/Projects/MORK/benchmarks/logic-query/resources/big.metta")
          .expect("Should have been able to read the file");
        let mut buf = vec![];
        file.read_to_end(&mut buf).unwrap();
        s.load_sexpr_simple(&buf[..], expr!(s, "$"), expr!(s, "_1")).unwrap();

        // expr!(s, "[2] flip [3] \"=\" _2 _1")
        // s.transform(expr!(s, "[2] assert [3] forall $ $"), expr!(s, "axiom _2"));
        // s.transform(expr!(s, "[2] axiom [3] = $ $"), expr!(s, "[2] flip [3] = _2 _1"));
        // s.query(expr!(s, "[2] axiom [3] = $ $"), |e| { println!("> {}", sexpr!(s, e)) });
        let t0 = Instant::now();
        let mut k = 0;
        s.query(expr!(s, "$x"), |e| {
            k += 1;
            std::hint::black_box(e);
            // println!("> {}", sexpr!(s, e))
        });
        println!("iterating all ({}) took {} microseconds", k, t0.elapsed().as_micros());



        // let mut res = Vec::<u8>::new();
        // s.dump(&mut res).unwrap();
        // println!("{}", String::from_utf8(res).unwrap());
    }

    #[test]
    fn simple_transform_multi_multi_test0() {
        const SEXPR_CONTENTS: &str = r#"(Duck Quack)
            (Human BlaBla)"#;

        let mut s = DefaultSpace::new();

        s.load_sexpr_simple(SEXPR_CONTENTS.as_bytes(),
                     expr!(s, "[2] $ $"),
                     expr!(s, "[2] root [2] Sound [2] Sound [2] _1 _2")).unwrap();

        s.transform_multi_multi_simple(
            &[expr!(s, "[2] root [2] Sound [2] Sound [2] $ $")],
            &[expr!(s, "[2] root [2] Sound [2] Sound [3] say _1 _2")],
        );

        let mut output = Vec::new();
        s.dump_sexpr(expr!(s, "$v"), expr!(s, "$v"), &mut output).unwrap();
        let out_string = String::from_utf8_lossy(&output);
        //println!("{out_string}");
        assert_eq!(out_string.lines().count(), 4);
        assert_eq!(
            "(root (Sound (Sound (Duck Quack))))\
            \n(root (Sound (Sound (Human BlaBla))))\
            \n(root (Sound (Sound (say Duck Quack))))\
            \n(root (Sound (Sound (say Human BlaBla))))\
            \n",
            out_string
        );
    }

    #[test]
    fn metta_calculus_test0() {
        let mut s = DefaultSpace::new();
        // (exec PC0 (, (? $channel $payload $body) 
        //              (! $channel $payload)
        //              (exec PC0 $p $t)) 
        //           (, $body (exec PC0 $p $t)))

        // const SPACE_EXPRS: &str = r#"
        // (exec PC0 (, (? $channel $payload $body) (! $channel $payload) (exec PC0 $p $t)) (, $body (exec PC0 $p $t)))
        // (exec PC1 (, (| $lprocess $rprocess) (exec PC1 $p $t)) (, $lprocess $rprocess (exec PC1 $p $t)))

        // (? (add $ret) ((S $x) $y) (? (add $z) ($x $y) (! $ret (S $z)) ) )
        // (? (add $ret) (Z $y) (! $ret $y))

        // (! (add result) ((S Z) (S Z)))
        // "#;

        const SPACE_EXPRS: &str = 
        concat!
        ( ""
        // , "\n(exec (test0 PC0) (, (? $channel $payload $body) (! $channel $payload) (exec (test0 PC0) $p $t)) (, (body $body) (exec (test0 PC0_) $p $t)))"
        , "\n(exec (test0 PC1) (, (user (| $lprocess $rprocess)) (exec (test0 PC1) (user $p) (user $t))) (, (user $lprocess) (user $rprocess) (exec (test0 PC1) (user $p) (user $t))))"
        , "\n(user (? (add $ret) ((S $x) $y) (? (add $z) ($x $y) (! $ret (S $z)) ) ) )"
        , "\n(user (? (add $ret) (Z $y) (! $ret $y)))"
        , "\n(user (! (add result) ((S Z) (S Z))))"
        );

        s.load_sexpr_simple(SPACE_EXPRS.as_bytes(), expr!(s, "$"), expr!(s, "_1")).unwrap();

        s.metta_calculus_simple("test0").unwrap();

        let mut v = vec![];
        s.dump_sexpr(expr!(s, "$"), expr!(s, "_1"), &mut v).unwrap();

        let res = String::from_utf8(v).unwrap();

        // println!("\nRESULTS\n");
        // println!("{}", res);

        assert_eq!(res.lines().count(), 3);
        core::assert_eq!(
            res,
            "(user (! (add result) ((S Z) (S Z))))\n\
             (user (? (add $) (Z $) (! _1 _2)))\n\
             (user (? (add $) ((S $) $) (? (add $) (_2 _3) (! _1 (S _4)))))\n"
        );

        //GOAT, there are several things before this test will work "correctly", i.e. with the first expression
        // in `SPACE_EXPRS` uncommented

        //Firstly, we need to run this test in a thread we spin up ourself, so we can ensure there is enough
        // stack space. Otherwise we'll hit an overflow.  To temporarily work around this, you can set the
        // env var before running the test:
        //
        // ```bash
        // export RUST_MIN_STACK=16777216
        // ```
        //
        //But then we still won't get the right answer because of lack of real unification.
        //
        // "(exec PC0 (, (? $channel $payload $body) (! $channel $payload) (exec PC0 $p $t)) (, (body $body) (exec PC0_ $p $t)))"
        // "(exec PC0 (, (? $        $        $    ) (! _1       _2      ) (exec PC0 $  $ )) (, (body _3   ) (exec PC0_ _4 _5)))"
        //
        // first pattern
        // "(? (add $   ) ((S $ ) $ ) (? (add $ ) (_2  _3) (! _1   (S _4)) ) )"
        // $channel = (add $)
        // $payload = ((S $ ) $ )
        // $body    = (? (add $ ) (_2  _3) (! _1   (S _4)) ) )    // note that the references are now "divorced"
        //
        // second pattern
        // "(! (add result) ((S Z) (S Z)))"
        //                                                                // the following variable references are only true localy
        // $channel = (add result)          // unifies first pattern $channel where (add result) = (add $)       ; _1 = result
        // $payload = ((S Z) (S Z)))        // unifies first pattern $payload where ((S $) $)    = ((S Z) (S Z)) ; _1 = Z, _2 = (S Z)
        //
        // assume we substitued backwrds
        // "(? (add $      ) ((S $) $   ) (? (add $ ) (_2  _3  ) (! _1     (S _4)) ) )"
        // =>                       v                  v   v        v         v this should now decrement based on being the first introduction
        // "(? (add result) ((S Z) (S Z)) (? (add $ ) (Z  (S Z)) (! result (S _1)) ) )"
        //                                v new body
        //                                $body = (? (add $ ) (Z  (S Z)) (! result (S _1)) )
        //
        // but then body get substituted
        // $body = (? (add $ ) (_2  _3) (! _1   (S _4)) ) )
        // write (body (? (add $ ) (_2  _3) (! _1   (S _4)) ) ))
        //
        // but we expect
        // $body = (? (add $ ) (Z  (S Z)) (! result (S _1)) )
        // write (body (? (add $ ) (Z  (S Z)) (! result (S _1)) ))
        //
        // So if unification were working:
        //
        // "(body (? (add $) (_2 _3) (! _1 (S _4))))\n\
        //  (! (add result) ((S Z) (S Z)))\n
        //  (? (add $) (Z $) (! _1 _2))\n
        //  (? (add $) ((S $) $) (? (add $) (_2 _3) (! _1 (S _4))))\n\
        // "
        // into 
        // "(body (? (add $) (Z (S Z)) (! result (S _1))))\n\
        //  (! (add result) ((S Z) (S Z)))\n\
        //  (? (add $) (Z $) (! _1 _2))\n\
        //  (? (add $) ((S $) $) (? (add $) (_2 _3) (! _1 (S _4))))\n\
        // "
        //

    }

    #[test]
    fn metta_calculus_test_one_exec_only() {
        let mut s = DefaultSpace::new();

        const SPACE_EXPRS: &str = 
        concat!
        ( ""
        // , "\n(exec (test_one_exec_only PC0) (, v) (, thing))"                        // regression bug was outputing : "thing\n"
        // , "\n(exec (test_one_exec_only PC0) (, v) (, (thing) ))"                     // regression bug was outputing : "(thing)\n"
        // , "\n(exec (test_one_exec_only PC0) (, v) (, (thing (thing thing) thing) ))" // regression bug was outputing : "(thing (thing thing) thing)\n"
        // , "\n(exec (test_one_exec_only PC0) (, v) (, (thing thing) ))"               // regression bug was outputing : "(thing thing)\n"
        // , "\n(exec (test_one_exec_only PC0) (, v) (, ($x thing) ))"                  // fails because it's trying to grab a permission that conflicts with the build-in status location
        // , "\n(exec (test_one_exec_only PC0) (, v) (, (exec $x) ))"                   // fails because it's trying to grab a permission that conflicts with the build-in status location
        , "\n(exec (test_one_exec_only PC0) (, v) (, (executive $x) ))"                 // ""
        );

        s.load_sexpr_simple(SPACE_EXPRS.as_bytes(), expr!(s, "$"), expr!(s, "_1")).unwrap();

        s.metta_calculus_simple("test_one_exec_only").unwrap();

        let mut v = vec![];
        s.dump_sexpr(expr!(s, "$"), expr!(s, "_1"), &mut v).unwrap();

        let string = std::str::from_utf8(&v).unwrap();
        dbg!( string );

        core::assert_eq!(v.len(), 0);

    }
    #[test]
    fn metta_calculus_test_clears_two_execs() {
        let mut s = DefaultSpace::new();

        const SPACE_EXPRS: &str = 
        concat!
        ( ""
        , "\n(exec (test_clears_two_execs PC0) (, (exec $loc $p $t)) (, (result-pc0 (exec $loc $p $t))))"

        , "\n(exec (test_clears_two_execs PC1) (, (exec $loc $p $t)) (, (result-pc1 (exec $loc $p $t))))"
        );

        s.load_sexpr_simple(SPACE_EXPRS.as_bytes(), expr!(s, "$"), expr!(s, "_1")).unwrap();

        s.metta_calculus_simple("test_clears_two_execs").unwrap();

        let mut v = vec![];
        s.dump_sexpr(expr!(s, "$"), expr!(s, "_1"), &mut v).unwrap();

        let out = String::from_utf8(v).unwrap();


        assert_eq!(out.lines().count(), 3);
        core::assert_eq!(
            "(result-pc0 (exec (test_clears_two_execs PC0) (, (exec $ $ $)) (, (result-pc0 (exec _1 _2 _3)))))\n\
            (result-pc0 (exec (test_clears_two_execs PC1) (, (exec $ $ $)) (, (result-pc1 (exec _1 _2 _3)))))\n\
            (result-pc1 (exec (test_clears_two_execs PC1) (, (exec $ $ $)) (, (result-pc1 (exec _1 _2 _3)))))\n\
            ", &out
        )
    }

    /// This exercises the writer cleanup code by ensuring there is no spurious dangling path, or that
    /// the path isn't interpreted as a value
    #[test]
    fn transform_multi_multi_no_match() {
        let mut s = DefaultSpace::new();

        s.transform_multi_multi_simple(&[expr!(s, "aardvark")], &[expr!(s, "cat")]);

        let mut writer = Vec::new();
        s.dump_sexpr(expr!(s, "$"), expr!(s, "_1"), &mut writer).unwrap();

        let out = String::from_utf8(writer).unwrap();

        // println!("{}", out);
        core::assert_ne!(&out, "cat\n");
    }

    #[test]
    fn transform_multi_multi_ignoring_second_template() {
        let mut s = DefaultSpace::new();
                const SPACE_EXPRS: &str = 
        concat!
        ( "\n(val a b)"
        );

        s.load_sexpr_simple(SPACE_EXPRS.as_bytes(), expr!(s, "$"), expr!(s, "_1")).unwrap();

        s.transform_multi_multi_simple(&[expr!(s, "[3] val $ $")], &[expr!(s, "_1"), expr!(s, "_2")]);

        let mut writer = Vec::new();
        s.dump_sexpr(expr!(s, "$"), expr!(s, "_1"), &mut writer).unwrap();

        let out = unsafe {
            core::mem::transmute::<_,String>(writer)
        };

        println!("{}", out);

        let vals = ["a","b","(val a b)"];
        for each in vals {
            assert!(out.lines().any(|i| i == each))
        }
    }

    #[test]
    fn metta_calculus_swap_0() {
        let mut s = DefaultSpace::new();

        const SPACE_EXPRS: &str =
        concat!
        ( ""
        , "\n(val a b)"
        , "\n(exec (swap_0 \"00\") (, (val $x $y)) (, (swaped-val (val $x $y) (val $y $x))) )" // swap vals
        , "\n(exec (swap_0 \"01\") (, (val $x $y)) (, (pair $x $y)) )" // swap vals
        );

        s.load_sexpr_simple(SPACE_EXPRS.as_bytes(), expr!(s, "$"), expr!(s, "_1")).unwrap();

        s.metta_calculus_simple("swap_0").unwrap();

        let mut writer = Vec::new();
        s.dump_sexpr(expr!(s, "$"), expr!(s, "_1"), &mut writer).unwrap();

        let out = String::from(std::str::from_utf8(&writer).unwrap());

        // println!("\n{out:?}");
        // println!("\n{:?}", s.dump_raw_at_root());

        // println!("RESULTS:\n{}", out);
        assert_eq!(out.lines().count(), 3);
        assert_eq!(out, "(val a b)\n(pair a b)\n(swaped-val (val a b) (val b a))\n");
    }

    #[test]
    fn metta_calculus_swap2() {

        let mut s = DefaultSpace::new();

        const SPACE_EXPRS: &str =
        concat!
        ( ""
        , "\n(val a b)"
        , "\n(val c d)"
        , "\n(val e f)"
        , "\n(val g h)"

        , "\n(def (metta_thread_basic 2) (, (swapped $v $u))"
        , "\n                            (, (val $v $u))"
        , "\n)"

        , "\n(exec (metta_thread_basic 1) (, (val $x $y) (def (metta_thread_basic 2) $p $t) )"
        , "\n                         (,"
        , "\n                            (swapped $y $x)"
        , "\n                            (exec (metta_thread_basic 1) $p $t)"
        , "\n                         )"
        , "\n)"
        );

        s.load_sexpr_simple(SPACE_EXPRS.as_bytes(), expr!(s, "$"), expr!(s, "_1")).unwrap();

        s.metta_calculus_simple("metta_thread_basic").unwrap();

        let mut writer = Vec::new();
        s.dump_sexpr(expr!(s, "$"), expr!(s, "_1"), &mut writer).unwrap();

        let out = String::from(std::str::from_utf8(&writer).unwrap());

        assert_eq!(out.lines().count(), 13);
        assert_eq!(out,
            "(val a b)\n\
            (val b a)\n\
            (val c d)\n\
            (val d c)\n\
            (val e f)\n\
            (val f e)\n\
            (val g h)\n\
            (val h g)\n\
            (swapped b a)\n\
            (swapped d c)\n\
            (swapped f e)\n\
            (swapped h g)\n\
            (def (metta_thread_basic 2) (, (swapped $ $)) (, (val _1 _2)))\n\
            "
        );

        println!("RESULTS:\n{}", out);
    }

    #[test]
    fn process_calculus_test() {
        let mut s = DefaultSpace::new();

        // note 'idle' MM2-like statement that can be activated by moving it to the exec space
        const SPACE_EXPRS: &str = r#"
    (doc "inference control that switches between dispatching two space functions and runs 10 steps")
    (exec (process_calculus (IC 0 1 (S (S (S (S (S (S (S (S (S (S Z))))))))))))
                (, (exec (process_calculus (IC $x $y (S $c))) $sp $st)
                    ((exec $x) $p $t))
                (, (exec (process_calculus (IC $y $x $c)) $sp $st)
                    (exec (process_calculus (R $x)) $p $t)))
    (doc "process calculus recv-send matching")
    ((exec 0)
        (, (petri (? $channel $payload $body))
            (petri (! $channel $payload)))
        (, (petri $body)))
    (doc "process calculus | happens in parallel")
    ((exec 1)
        (, (petri (| $lprocess $rprocess)))
        (, (petri $lprocess)
            (petri $rprocess)))

    (doc "peano arithmetic process-calculus style, using content addressing for Private Name gen")
    (petri (? (add $ret) ((S $x) $y) (| (! (add (PN $x $y)) ($x $y))
                                        (? (PN $x $y) $z (! $ret (S $z)))  )  ))
    (petri (? (add $ret) (Z $y) (! $ret $y)))
    (doc "the actual input to the program: two peano numbers to add")
    (petri (! (add result) ((S (S Z)) (S (S Z)))))
        "#;

        s.load_sexpr_simple(SPACE_EXPRS.as_bytes(), expr!(s, "$"), expr!(s, "_1")).unwrap();

        s.metta_calculus_simple("process_calculus").unwrap(); // big number of steps to show the MM2 inference control working

        let mut v = vec![];
        // s.dump_all_sexpr(&mut v).unwrap();
        // We're only interested in the petri dish (not the state of exec), and specifically everything that was outputted `!` to `result`
        s.dump_sexpr(expr!(s, "[2] petri [3] ! result $"), expr!(s, "_1"), &mut v).unwrap();
        let res = String::from_utf8(v).unwrap();

        assert_eq!(res, "(S (S (S (S Z))))\n");
        println!("result: {res}")
    }


}
