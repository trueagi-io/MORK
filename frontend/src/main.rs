use std::fs;
use std::time::Instant;


// use typed_arena::Arena;
// use mork::rosetta_parser::{Error, ParseContext, SExp, SEXP_STRING_IN, SEXP_STRUCT, Token, Tokens};
//
// fn main() {
//     // println!("{:?}", SEXP_STRUCT.buffer_encode());
//     let mut ctx = ParseContext::new(SEXP_STRING_IN);
//     ctx.arena = Some(Arena::new());
//     let contents = fs::read_to_string("resources/edges67458171.metta")
//         .expect("Should have been able to read the file");
//     let mut tokens = Tokens::new(contents.as_str());
//     let ctx_ptr = &mut ctx as *mut ParseContext;
//     let tokens_ptr = &mut tokens as *mut Tokens;
//
//     let t0 = Instant::now();
//     let mut i = 0;
//     loop {
//         unsafe {
//             let e = SExp::parse_multiple(&mut *ctx_ptr, &mut *tokens_ptr);
//             match e {
//                 Ok(e) => {  }
//                 Err(Error::ExpectedEOF) => { break }
//                 Err(e) => { println!("{:?}", e); break }
//             }
//             i += 1;
//         }
//     }
//     println!("parsed {}", i);
//     println!("took {} ms", t0.elapsed().as_millis());  // 21 seconds
// }


use mork::he_parser::{Atom, SExprParser, Tokenizer};
use regex::Regex;

fn main() {
    let contents = fs::read_to_string("resources/edges67458171.metta")
        .expect("Should have been able to read the file");
    let mut parser = SExprParser::new(contents.as_str());
    let mut tokenizer = Tokenizer::new();
    tokenizer.register_fallible_token(Regex::new(r"[\-\+]?\d+(\.\d+)?[eE][\-\+]?\d+").unwrap(),
                                 |token| { Ok(Atom::gnd(token.parse::<f64>().unwrap())) });

    let t0 = Instant::now();
    let mut i = 0;
    loop {
        unsafe {
            let e = parser.parse(&tokenizer);
            match e {
                Ok(Some(e)) => { }
                Ok(None) => { break }
                Err(e) => { println!("{:?}", e); break }
            }
            i += 1;
        }
    }
    println!("parsed {}", i);
    println!("took {} ms", t0.elapsed().as_millis()); // 60 seconds
}
