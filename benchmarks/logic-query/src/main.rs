use std::hint::black_box;
use std::io::Read;
use std::time::Instant;
use mork_bytestring::*;
use mork_bytestring::Tag::{Arity, SymbolSize};
use mork_frontend::bytestring_parser::{Context, Parser, ParserError};
use pathmap::trie_map::BytesTrieMap;
use pathmap::zipper::{ReadZipperUntracked, Zipper, ZipperMoving, ZipperWriting};
use pathmap::zipper::{ZipperAbsolutePath, ZipperIteration};


static mut SIZES: [u64; 4] = [0u64; 4];
static mut ARITIES: [u64; 4] = [0u64; 4];
static mut VARS: [u64; 4] = [0u64; 4];

struct CfIter<'a> {
    i: u8,
    w: u64,
    mask: &'a [u64; 4]
}

impl <'a> CfIter<'a> {
    fn new(mask: &'a [u64; 4]) -> Self {
        Self {
            i: 0,
            w: mask[0],
            mask: mask
        }
    }
}

impl <'a> Iterator for CfIter<'a> {
    type Item = u8;

    fn next(&mut self) -> Option<u8> {
        loop {
            if self.w != 0 {
                let wi = self.w.trailing_zeros() as u8;
                self.w ^= 1u64 << wi;
                let index = self.i*64 + wi;
                return Some(index)
            } else if self.i < 3 {
                self.i += 1;
                self.w = *unsafe{ self.mask.get_unchecked(self.i as usize) };
            } else {
                return None
            }
        }
    }
}

fn mask_and(l: [u64; 4], r: [u64; 4]) -> [u64; 4] {
    [l[0] & r[0], l[1] & r[1], l[2] & r[2], l[3] & r[3]]
}


const ITER_AT_DEPTH: u8 = 0;
const ITER_SYMBOL_SIZE: u8 = 1;
const ITER_SYMBOLS: u8 = 2;
const ITER_VARIABLES: u8 = 3;
const ITER_ARITIES: u8 = 4;
const ITER_EXPR: u8 = 5;
const ITER_NESTED: u8 = 6;
const ITER_SYMBOL: u8 = 7;
const ITER_ARITY: u8 = 8;
const ITER_VAR_SYMBOL: u8 = 9;
const ITER_VAR_ARITY: u8 = 10;
const ACTION: u8 = 11;

#[allow(unused)]
fn label(l: u8) -> String {
    match l {
        ITER_AT_DEPTH => { "ITER_AT_DEPTH" }
        ITER_SYMBOL_SIZE => { "ITER_SYMBOL_SIZE" }
        ITER_SYMBOLS => { "ITER_SYMBOLS" }
        ITER_VARIABLES => { "ITER_VARIABLES" }
        ITER_ARITIES => { "ITER_ARITIES" }
        ITER_EXPR => { "ITER_EXPR" }
        ITER_NESTED => { "ITER_NESTED" }
        ITER_SYMBOL => { "ITER_SYMBOL" }
        ITER_ARITY => {" ITER_ARITY" }
        ITER_VAR_SYMBOL => { "ITER_VAR_SYMBOL" }
        ITER_VAR_ARITY => { "ITER_VAR_ARITY" }
        ACTION => { "ACTION" }
        _ => { return l.to_string() }
    }.to_string()
}

fn transition<F: FnMut(&mut ReadZipperUntracked<()>) -> ()>(stack: &mut Vec<u8>, loc: &mut ReadZipperUntracked<()>, f: &mut F) {
    // println!("stack {}", stack.iter().map(|x| label(*x)).reduce(|x, y| format!("{} {}", x, y)).unwrap_or("empty".to_string()));
    // println!("label {}", label(*stack.last().unwrap()));
    let last = stack.pop().unwrap();
    match last {
        ACTION => { f(loc) }
        ITER_AT_DEPTH => {
            let size = stack.pop().unwrap();
            if loc.descend_first_k_path(size as usize) {
                transition(stack, loc, f);
                while loc.to_next_k_path(size as usize) {
                    transition(stack, loc, f);
                }
            }
            stack.push(size);
        }
        ITER_NESTED => {
            let arity = stack.pop().unwrap();
            let l = stack.len();
            for _ in 0..arity { stack.push(ITER_EXPR); }
            transition(stack, loc, f);
            stack.truncate(l);
            stack.push(arity)
        }
        ITER_SYMBOL_SIZE => {
            let m = mask_and(loc.child_mask(), unsafe { SIZES });
            let mut it = CfIter::new(&m);

            while let Some(b) = it.next() {
                if let Tag::SymbolSize(s) = byte_item(b) {
                    if loc.descend_to_byte(b) {
                        let last = stack.pop().unwrap();
                        stack.push(s);
                        stack.push(last);
                        transition(stack, loc, f);
                        stack.pop();
                        stack.pop();
                        stack.push(last);
                    }
                    loc.ascend(1);
                } else {
                    unreachable!()
                }
            }
        }
        ITER_SYMBOLS => {
            stack.push(ITER_AT_DEPTH);
            stack.push(ITER_SYMBOL_SIZE);
            transition(stack, loc, f);
            stack.pop();
            stack.pop();
        }
        ITER_VARIABLES => {
            let m = mask_and(loc.child_mask(), unsafe { VARS });
            let mut it = CfIter::new(&m);

            while let Some(b) = it.next() {
                let buf = [b];
                if loc.descend_to(buf) {
                    transition(stack, loc, f);
                }
                loc.ascend(1);
            }
        }
        ITER_ARITIES => {
            let m = mask_and(loc.child_mask(), unsafe { ARITIES });
            let mut it = CfIter::new(&m);

            while let Some(b) = it.next() {
                if let Tag::Arity(a) = byte_item(b) {
                    let buf = [b];
                    if loc.descend_to(buf) {
                        let last = stack.pop().unwrap();
                        stack.push(a);
                        stack.push(last);
                        transition(stack, loc, f);
                        stack.pop();
                        stack.pop();
                        stack.push(last);
                    }
                    loc.ascend(1);
                } else {
                    unreachable!()
                }
            }
        }
        ITER_EXPR => {
            stack.push(ITER_VARIABLES);
            transition(stack, loc, f);
            stack.pop();

            stack.push(ITER_SYMBOLS);
            transition(stack, loc, f);
            stack.pop();

            stack.push(ITER_NESTED);
            stack.push(ITER_ARITIES);
            transition(stack, loc, f);
            stack.pop();
            stack.pop();
        }
        ITER_SYMBOL => {
            let size = stack.pop().unwrap();
            let mut v = vec![];
            for _ in 0..size { v.push(stack.pop().unwrap()) }
            loc.descend_to(&[item_byte(SymbolSize(size))]);
            loc.descend_to(&v[..]);
            transition(stack, loc, f);
            loc.ascend(size as usize);
            loc.ascend(1);
            for _ in 0..size { stack.push(v.pop().unwrap()) }
            stack.push(size)
        }
        ITER_VAR_SYMBOL => {
            let size = stack.pop().unwrap();
            let mut v = vec![];
            for _ in 0..size { v.push(stack.pop().unwrap()) }

            stack.push(ITER_VARIABLES);
            transition(stack, loc, f);
            stack.pop();

            loc.descend_to(&[item_byte(SymbolSize(size))]);
            loc.descend_to(&v[..]);
            transition(stack, loc, f);
            loc.ascend(size as usize);
            loc.ascend(1);
            for _ in 0..size { stack.push(v.pop().unwrap()) }
            stack.push(size)
        }
        ITER_ARITY => {
            let arity = stack.pop().unwrap();
            loc.descend_to(&[item_byte(Arity(arity))]);
            transition(stack, loc, f);
            loc.ascend(1);
            stack.push(arity);
        }
        ITER_VAR_ARITY => {
            let arity = stack.pop().unwrap();

            stack.push(ITER_VARIABLES);
            transition(stack, loc, f);
            stack.pop();

            loc.descend_to(&[item_byte(Arity(arity))]);
            transition(stack, loc, f);
            loc.ascend(1);
            stack.push(arity);
        }
        _ => { unreachable!() }
    }
    stack.push(last);
}


// fn iter_expr_tail<'a, F>(z0: &mut ReadZipper<()>, mut action: &'a mut F) -> &'a mut F where F: FnMut(&mut ReadZipper<()>) -> () {
//     iter_arities(z0, &mut |a1, z1| {
//         if a1 > 1 {
//             iter_expr(z1, action);
//         }
//     });
//     action
// }
// EXAMPLE
//  QUERY: [3] a $ c
//  SPACE: [3]-a b c
//              \d c
//            \p q r
//         $
// RESULT : [3]-a b c
//               \d c
//          $
// fn iter_indiscriminate_bidirectional_matching<F>(z: &mut ReadZipper<()>, ez: &mut ExprZipper, mut action: &mut F) where F: FnMut(&mut ReadZipper<()>) -> () {
//     match ez.item() {
//         Ok(Tag::NewVar) | Ok(Tag::VarRef(_)) => {
//             if ez.next() { iter_expr(z, &mut |z0| iter_indiscriminate_bidirectional_matching(z0, &mut ez.clone(), action)) }
//             else { iter_expr(z, action) }
//         }
//         Ok(Tag::SymbolSize(_)) => { unreachable!() }
//         Ok(Tag::Arity(a)) => {
//             let skip = unsafe { *ez.subexpr().span() }.len();
//             if ez.has_pibling() { iter_variables(z, |z0| iter_indiscriminate_bidirectional_matching(z0, &mut ExprZipper{ root: ez.root, loc: ez.loc + skip, trace: vec![]}, action)) }
//             else { iter_variables(z, action) }
//
//             if z.descend_to(&[item_byte(Tag::Arity(a))]) {
//                 match a {
//                     0 => {
//                         if ez.next() { iter_indiscriminate_bidirectional_matching(z, &mut ez.clone(), action) }
//                         else { action(z) }
//                     }
//                     1 => {
//                         assert!(ez.next());
//                         iter_indiscriminate_bidirectional_matching(z, &mut ez.clone(), &mut |z0| {
//                             if ez.next() { iter_indiscriminate_bidirectional_matching(z, &mut ez.clone(), action) }
//                             else { action(z0) }
//                         });
//                     }
//                     2 => {
//                         assert!(ez.next());
//                         iter_indiscriminate_bidirectional_matching(z, &mut ez.clone(), &mut |z0| {
//                             assert!(ez.next());
//                             iter_indiscriminate_bidirectional_matching(z0, &mut ez.clone(), &mut |z1| {
//                                 if ez.next() { iter_indiscriminate_bidirectional_matching(z1, &mut ez.clone(), action) }
//                                 else { action(z1) }
//                             })
//                         });
//                     }
//                     3 => {
//                         assert!(ez.next());
//                         iter_indiscriminate_bidirectional_matching(z, &mut ez.clone(), &mut |z0| {
//                             assert!(ez.next());
//                             iter_indiscriminate_bidirectional_matching(z0, &mut ez.clone(), &mut |z1| {
//                                 assert!(ez.next());
//                                 iter_indiscriminate_bidirectional_matching(z1, &mut ez.clone(), &mut |z2| {
//                                     if ez.next() { iter_indiscriminate_bidirectional_matching(z2, &mut ez.clone(), action) }
//                                     else { action(z2) }
//                                 })
//                             })
//                         })
//                     }
//                     _ => { panic!("unimplemented expr matching arity") }
//                 }
//             }
//             z.ascend(1);
//
//         }
//         Err(s) => {
//             let skip = unsafe { *ez.subexpr().span() }.len();
//             if ez.has_next() { iter_variables(z, |z0| iter_indiscriminate_bidirectional_matching(z0, &mut ExprZipper{ root: ez.root, loc: ez.loc + skip, trace: vec![]}, action)) }
//             else { iter_variables(z, action) }
//
//             if z.descend_to(&[item_byte(Tag::SymbolSize(s.len() as u8))]) {
//                 if z.descend_to(s) {
//                     if ez.has_next() { iter_indiscriminate_bidirectional_matching(z, &mut ExprZipper{ root: ez.root, loc: ez.loc + s.len() + 1, trace: vec![]}, action) }
//                     else { action(z) }
//                 }
//                 z.ascend(s.len());
//             }
//             z.ascend(1);
//         }
//     }
// }

/*
  def indiscriminateBidirectionalMatchingTrace(): Vector[Instr] = this match
    case Var(i) if i > 0 =>
      Vector(Instr.ClearApps, Instr.RestrictSymbols(i))
    case Var(_) => Vector.empty
    case App(f, a) =>
      Vector(Instr.ClearSymbols, Instr.ZoomInApps)
      ++ f.indiscriminateBidirectionalMatchingTrace()
      ++ Vector(Instr.ZoomOutApps, Instr.CollectApps(a.indiscriminateBidirectionalMatchingTrace(): _*))
 */

// enum Instr {
//     ClearExpr(),
//     ClearSymbols(),
//     RestrictSymbols(Vec<u8>),
//     RestrictArities(u8),
//     Step(u8),
// }

fn indiscriminate_bidirectional_matching_stack(ez: &mut ExprZipper) -> Vec<u8> {
    let mut v = vec![];
    loop {
        match ez.item() {
            Ok(Tag::NewVar) | Ok(Tag::VarRef(_)) => {
                v.push(ITER_EXPR);
            }
            Ok(Tag::SymbolSize(_)) => { unreachable!() }
            Err(s) => {
                v.push(ITER_VAR_SYMBOL);
                v.push(s.len() as u8);
                v.extend(s);
            }
            Ok(Tag::Arity(a)) => {
                v.push(ITER_VAR_ARITY);
                v.push(a);
            }
        }
        if !ez.next() {
            v.reverse();
            return v
        }
    }
}

// fn variable_or_arity_mask(a: u8) -> [u64; 4] {
//     let mut m = unsafe { VARS.clone() };
//     let arity_byte = item_byte(Tag::Arity(a));
//     m[((arity_byte & 0b11000000) >> 6) as usize] |= 1u64 << (arity_byte & 0b00111111);
//     m
// }

// fn variable_or_arity<WZ: WriteZipper<()>>(z: &mut WZ, a: u8) {
//     let m = variable_or_arity_mask(a);
//     z.remove_unmasked_branches(m);
// }

// fn variable_or_size_mask(a: u8) -> [u64; 4] {
//     let mut m = unsafe { VARS.clone() };
//     let arity_byte = item_byte(Tag::SymbolSize(a));
//     m[((arity_byte & 0b11000000) >> 6) as usize] |= 1u64 << (arity_byte & 0b00111111);
//     m
// }

// fn variable_or_symbol(z: &mut WriteZipper<()>, s: &[u8]) {
//     // ALTERNATIVE: build variable + s map, restrict to it
//     let m = variable_or_size_mask(s.len() as u8);
//     z.remove_unmasked_branches(m);
//     z.descend_to(&[item_byte(Tag::SymbolSize(s.len() as u8))]);
//     let mut zf = z.fork();
//     zf.descend_to(s);
//     let m = zf.make_map();
//     z.remove_branch();
//     z.descend_to(s);
//     z.graft_map(m);
//     z.ascend(s.len() + 1);
// }

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

impl Parser for DataParser {
    fn tokenizer<'r>(&mut self, s: &[u8]) -> &'r [u8] {
        // return unsafe { std::mem::transmute(s) };
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
    // SETUP PROCEDURE?
    for size in 1..64 {
        let k = item_byte(Tag::SymbolSize(size));
        unsafe { SIZES[((k & 0b11000000) >> 6) as usize] |= 1u64 << (k & 0b00111111); }
    }
    for arity in 1..64 {
        let k = item_byte(Tag::Arity(arity));
        unsafe { ARITIES[((k & 0b11000000) >> 6) as usize] |= 1u64 << (k & 0b00111111); }
    }
    let nv_byte = item_byte(Tag::NewVar);
    unsafe { VARS[((nv_byte & 0b11000000) >> 6) as usize] |= 1u64 << (nv_byte & 0b00111111); }
    for size in 1..64 {
        let k = item_byte(Tag::VarRef(size));
        unsafe { VARS[((k & 0b11000000) >> 6) as usize] |= 1u64 << (k & 0b00111111); }
    }


    // let mut file = std::fs::File::open("resources/test.metta")
    let mut file = std::fs::File::open("/home/adam/Projects/metta-examples/aunt-kg/royal92.metta")
        .expect("Should have been able to read the file");
    let mut buf = vec![];
    file.read_to_end(&mut buf).unwrap();
    let mut it = Context::new(&buf[..]);
    let mut parser = DataParser::new();

    let mut space = BytesTrieMap::<()>::new();
    // let space_ptr = &mut space as *mut BytesTrieMap<()>;

    #[allow(unused)]
    let t0 = Instant::now();
    #[allow(unused)]
    let mut i = 0;
    let mut stack = [0u8; 2048];
    loop {
        let mut ez = ExprZipper::new(Expr{ptr: stack.as_mut_ptr()});
        match parser.sexpr(&mut it, &mut ez) {
            Ok(()) => {
                space.insert(&stack[..ez.loc], ());
            }
            Err(ParserError::InputFinished) => break,
            Err(other) => panic!("{:?}", other)
        }
        i += 1;
        it.variables.clear();
    }
    // println!("built {}", i);
    // println!("took {} ms", t0.elapsed().as_millis());
    println!("map contains: {}", space.val_count());

    let t0 = Instant::now();
    let mut z = space.read_zipper();

    let mut visited = 0;
    let mut buffer = vec![ACTION, ITER_EXPR];
    transition(&mut buffer, &mut z, &mut |loc| {
        black_box(loc.origin_path());
        visited += 1;
    });
    println!("iterating all ({}) took {} microseconds", visited, t0.elapsed().as_micros());

    let t0 = Instant::now();
    let mut z = space.read_zipper();

    let mut visited = 0;
    let mut buffer = vec![ACTION];
    let mut q = vec![item_byte(Tag::Arity(3))];
    let relations_symbol = parser.tokenizer(b"Individuals");
    q.push(item_byte(Tag::SymbolSize(relations_symbol.len() as u8)));
    q.extend(&relations_symbol[..]);
    q.push(item_byte(Tag::NewVar));
    q.push(item_byte(Tag::Arity(2)));
    let fullname_symbol = parser.tokenizer(b"Fullname");
    q.push(item_byte(Tag::SymbolSize(fullname_symbol.len() as u8)));
    q.extend(&fullname_symbol[..]);
    q.push(item_byte(Tag::NewVar));
    buffer.extend(indiscriminate_bidirectional_matching_stack(&mut ExprZipper::new(Expr{ ptr: q.as_mut_ptr() })));
    transition(&mut buffer, &mut z, &mut |loc| {
        black_box(loc.origin_path());
        visited += 1;
    });

    println!("iterating {:?} ({}) took {} microseconds", q, visited, t0.elapsed().as_micros());

    let t0 = Instant::now();
    let mut z = space.read_zipper();

    let mut visited = 0;
    let mut buffer = vec![ACTION];
    let mut q = vec![item_byte(Tag::Arity(3))];
    let relations_symbol = parser.tokenizer(b"Relations");
    q.push(item_byte(Tag::SymbolSize(relations_symbol.len() as u8)));
    q.extend(&relations_symbol[..]);
    let interest_symbol = parser.tokenizer(b"1350");
    q.push(item_byte(Tag::SymbolSize(interest_symbol.len() as u8)));
    q.extend(&interest_symbol[..]);
    q.push(item_byte(Tag::NewVar));
    buffer.extend(indiscriminate_bidirectional_matching_stack(&mut ExprZipper::new(Expr{ ptr: q.as_mut_ptr() })));
    transition(&mut buffer, &mut z, &mut |loc| {
        black_box(loc.origin_path());
        visited += 1;
    });

    println!("iterating {:?} ({}) took {} microseconds", q, visited, t0.elapsed().as_micros());

    /*
    multithreading
    map contains: 53442
    iterating all took 9176 microseconds
    iterating [3, 193, 58, 192, 2, 193, 60, 192] (3001) took 1187 microseconds
    iterating [3, 193, 79, 194, 29, 251, 192] (3) took 3 microseconds
    real    0m0.110s
    user    0m0.085s
    sys     0m0.024s

    iter-optimization
    map contains: 53442
    iterating all took 9036 microseconds
    iterating [3, 193, 58, 192, 2, 193, 60, 192] (3001) took 1259 microseconds
    iterating [3, 193, 79, 194, 29, 251, 192] (3) took 3 microseconds
    real    0m0.107s
    user    0m0.084s
    sys     0m0.023s

    master
    map contains: 53442
    iterating all took 10908 microseconds
    iterating [3, 193, 58, 192, 2, 193, 60, 192] (3001) took 1350 microseconds
    iterating [3, 193, 79, 194, 29, 251, 192] (3) took 4 microseconds
    real    0m0.107s
    user    0m0.089s
    sys     0m0.018s
     */
}
