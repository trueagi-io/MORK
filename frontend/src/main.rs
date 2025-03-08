use std::collections::HashMap;
use std::{fs, mem, ptr};
use std::hint::black_box;
use std::io::{BufReader, Read};
use std::time::Instant;
use pathmap::zipper::ZipperWriting;


// use typed_arena::Arena;
// use mork_frontend::rosetta_parser::{Error, ParseContext, SExp, SEXP_STRING_IN, SEXP_STRUCT, Token, Tokens};
//
// fn main() {
//     // println!("{:?}", SEXP_STRUCT.buffer_encode());
//     let mut ctx = ParseContext::new(SEXP_STRING_IN);
//     ctx.arena = Some(Arena::new());
//     let contents = fs::read_to_string("/run/media/adam/43323a1c-ad7e-4d9a-b3c0-cf84e69ec61a/awesome-biomedical-kg/ckg_v3-002/results/nodes.metta")
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
//                 Ok(e) => { }
//                 Err(Error::ExpectedEOF) => { break }
//                 Err(e) => { println!("{:?}", e); break }
//             }
//             i += 1;
//         }
//     }
//     println!("parsed {}", i);
//     println!("took {} ms", t0.elapsed().as_millis());  // 21 seconds
// }


// use mork::he_parser::{Atom, SExprParser, Tokenizer};
// use regex::Regex;
//
// fn main() {
//     let contents = fs::read_to_string("resources/edges67458171.metta")
//         .expect("Should have been able to read the file");
//     let mut parser = SExprParser::new(contents.as_str());
//     let mut tokenizer = Tokenizer::new();
//     tokenizer.register_fallible_token(Regex::new(r"[\-\+]?\d+(\.\d+)?[eE][\-\+]?\d+").unwrap(),
//                                  |token| { Ok(Atom::gnd(token.parse::<f64>().unwrap())) });
//
//     let t0 = Instant::now();
//     let mut i = 0;
//     loop {
//         unsafe {
//             let e = parser.parse(&tokenizer);
//             match e {
//                 Ok(Some(e)) => { }
//                 Ok(None) => { break }
//                 Err(e) => { println!("{:?}", e); break }
//             }
//             i += 1;
//         }
//     }
//     println!("parsed {}", i);
//     println!("took {} ms", t0.elapsed().as_millis()); // 60 seconds
// }


// use mork::cz2_parser::{Expr, Parser, isDigit, BufferedIterator};
// use regex::Regex;
//
// struct DataParser {
//     count: i64,
//     symbols: HashMap<String, i64>,
//     floats: HashMap<i64, i64>,
//     strings: HashMap<String, i64>,
// }
//
// impl DataParser {
//     fn new() -> Self {
//         Self {
//             count: 3,
//             symbols: HashMap::new(),
//             floats: HashMap::new(),
//             strings: HashMap::new(),
//         }
//     }
// }
//
// impl Parser for DataParser {
//   const empty: i64 = 1;
//   const singleton: i64 = 2;
//
//   fn tokenizer(&mut self, s: String) -> i64 {
//     self.count += 1;
//     if s.chars().next().unwrap() == '"' { self.strings.insert(s, self.count); }
//     else if !isDigit(s.chars().next().unwrap()) { self.symbols.insert(s, self.count); }
//     else { self.floats.insert(s.parse::<f64>().unwrap() as i64, self.count); }
//     self.count
//   }
// }
//
// fn main() {
//     let mut file = std::fs::File::open("resources/edges67458171.metta")
//         .expect("Should have been able to read the file");
//     let mut it = BufferedIterator{ file: file, buffer: [0; 4096], cursor: 4096, max: 4096 };
//     let mut parser = DataParser::new();
//
//     let t0 = Instant::now();
//     let mut i = 0;
//     let mut stack = Vec::with_capacity(100);
//     let mut vs = Vec::with_capacity(100);
//     loop {
//         unsafe {
//             let e = parser.sexprUnsafe(&mut it, &mut vs, &mut stack);
//             match e.as_ref() {
//                 Some(e) => {
//                     black_box(e);
//                 }
//                 None => { break }
//             }
//             i += 1;
//             vs.set_len(0);
//             stack.set_len(0);
//         }
//     }
//     println!("parsed {}", i);
//     println!("took {} ms", t0.elapsed().as_millis()); // 60 seconds
// }


// use mork::cz3_parser::{Expr, ExprZipper, Parser, isDigit, BufferedIterator};
//
// struct DataParser {
//     count: i64,
//     symbols: HashMap<String, i64>,
//     floats: HashMap<i64, i64>,
//     strings: HashMap<String, i64>,
// }
//
// impl DataParser {
//     fn new() -> Self {
//         Self {
//             count: 3,
//             symbols: HashMap::new(),
//             floats: HashMap::new(),
//             strings: HashMap::new(),
//         }
//     }
// }
//
// impl Parser for DataParser {
//     fn tokenizer(&mut self, s: String) -> i64 {
//         self.count += 1;
//         if s.chars().next().unwrap() == '"' { self.strings.insert(s, self.count); }
//         else if !isDigit(s.chars().next().unwrap()) { self.symbols.insert(s, self.count); }
//         else { self.floats.insert(s.parse::<f64>().unwrap() as i64, self.count); }
//         self.count
//     }
// }
//
// fn main() {
//     // let mut file = std::fs::File::open("resources/edges5000.metta")
//     let mut file = std::fs::File::open("resources/edges67458171.metta")
//         .expect("Should have been able to read the file");
//     let mut it = BufferedIterator{ file: file, buffer: [0; 4096], cursor: 4096, max: 4096 };
//     let mut parser = DataParser::new();
//
//     let t0 = Instant::now();
//     let mut i = 0;
//     let mut stack = Vec::with_capacity(100);
//     let mut vs = Vec::with_capacity(100);
//     loop {
//         unsafe {
//             let mut ez = ExprZipper::new(Expr{ptr: stack.as_mut_ptr()});
//             if parser.sexprUnsafe(&mut it, &mut vs, &mut ez) {
//                 // ExprZipper::new(ez.root).traverse(0); println!();
//                 black_box(ez.root);
//             } else { break }
//             i += 1;
//             vs.set_len(0);
//         }
//     }
//     println!("parsed {}", i);
//     println!("took {} ms", t0.elapsed().as_millis()); // 42 seconds
// }

use mork_bytestring::{Expr, ExprZipper};
use mork_frontend::bytestring_parser::{Parser, ParserError, Context};
use pathmap::trie_map::BytesTrieMap;

struct DataParser {
    count: u64,
    symbols: BytesTrieMap<u64>,
}

impl DataParser {
    fn new() -> Self {
        Self {
            count: 3,
            symbols: BytesTrieMap::new(),
        }
    }

    const EMPTY: &'static [u8] = &[];
}

fn gen_key<'a>(i: u64, buffer: *mut u8) -> &'a [u8] {
    let ir = u64::from_be(i);
    unsafe { ptr::write_unaligned(buffer as *mut u64, ir) };
    let bs = (8 - ir.trailing_zeros()/8) as usize;
    let l = bs.max(1);
    unsafe { std::slice::from_raw_parts(buffer.byte_offset((8 - l) as isize), l) }
}

// use pathmap::zipper::WriteZipper;
impl Parser for DataParser {
    fn tokenizer<'r>(&mut self, s: &[u8]) -> &'r [u8] {
        return unsafe { std::mem::transmute(s) };
        if s.len() == 0 { return Self::EMPTY }
        let mut z = self.symbols.write_zipper_at_path(s);
        let r = z.get_value_or_insert_with(|| {
            self.count += 1;
            u64::from_be(self.count)
        });
        let bs = (8 - r.trailing_zeros()/8) as usize;
        let l = bs.max(1);
        unsafe { std::slice::from_raw_parts_mut((r as *mut u64 as *mut u8).byte_offset((8 - l) as isize), l) }
    }
}

fn main() {
    let mut file = std::fs::File::open("resources/edges5000.metta")
    // let mut file = std::fs::File::open("/home/adam/Projects/metta-examples/aunt-kg/royal92.metta")
    // let mut file = std::fs::File::open("/run/media/adam/43323a1c-ad7e-4d9a-b3c0-cf84e69ec61a/awesome-biomedical-kg/ckg_v3-002/results/nodes.metta")
    // let file = std::fs::File::open("resources/edges67458171.metta")
        .expect("Should have been able to read the file");
    // let slice = unsafe { memmap2::Mmap::map(&file).unwrap() };
    let mut v = vec![];
    file.read_to_end(&mut v);
    let slice = &v[..];
    let mut it = Context::new(&slice);
    let mut parser = DataParser::new();

    let t0 = Instant::now();
    // let mut btm = BytesTrieMap::new();
    let mut i = 0;
    let mut stack = [0; 2 << 19];
    loop {
        unsafe {
            let mut ez = ExprZipper::new(Expr{ptr: stack.as_mut_ptr()});
            match parser.sexpr(&mut it, &mut ez) {
                Ok(()) => {
                    // btm.insert(&stack[..ez.loc], ());
                    // unsafe { println!("{}", std::str::from_utf8_unchecked(&stack[..])); }
                    // println!("{:?}", stack);
                    ExprZipper::new(ez.root).traverse(0); println!();
                    black_box(ez.root);
                }
                Err(ParserError::InputFinished) => { break }
                Err(other) => { panic!("{:?}", other) }
            }
            i += 1;
            it.variables.clear();
        }
    }
    println!("built {}", i);
    println!("took {} ms", t0.elapsed().as_millis()); // 4GB, 6 seconds
    // println!("map contains: {}", btm.val_count());
}
