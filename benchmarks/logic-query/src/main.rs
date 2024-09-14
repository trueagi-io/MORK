use std::hint::black_box;
use std::ptr;
use std::time::Instant;
use mork_bytestring::*;
use mork_frontend::bytestring_parser::{BufferedIterator, Parser};
use pathmap::trie_map::BytesTrieMap;
use pathmap::zipper::{Zipper, ReadZipper, WriteZipper};


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

// fn iter_at_depth<F>(level: u32, loc: &mut ReadZipper<()>, mut action: F) where F: FnMut(&mut ReadZipper<()>) -> () {
//     assert!(level > 0);
//     let mut i = 0;
//     while i < level {
//         if loc.descend_indexed_branch(0) {
//             i += 1
//         } else if loc.to_sibling(true) {
//         } else if loc.ascend(1) {
//             i -= 1
//         } else {
//             return;
//         }
//     }
//
//     while i > 0 {
//         if i == level {
//             action(loc);
//             if loc.to_sibling(true) {
//             } else {
//                 assert!(loc.ascend(1));
//                 i -= 1;
//             }
//         } else if i < level {
//             if loc.to_sibling(true) {
//                 while i < level && loc.descend_indexed_branch(0) {
//                     i += 1;
//                 }
//             } else {
//                 if loc.ascend(1) {
//                     i -= 1;
//                 } else {
//                     unreachable!();
//                 }
//             }
//         }
//     }
// }

const ITER_AT_DEPTH: u8 = 0;
const ITER_SYMBOL_SIZE: u8 = 1;
const ITER_SYMBOLS: u8 = 2;
const ITER_VARIABLES: u8 = 3;
const ITER_ARITIES: u8 = 4;
const ITER_EXPR: u8 = 5;
const ITER_NESTED: u8 = 6;
const ACTION: u8 = 10;

fn label(l: u8) -> String {
    match l {
        ITER_AT_DEPTH => { "ITER_AT_DEPTH" }
        ITER_SYMBOL_SIZE => {"ITER_SYMBOL_SIZE"}
        ITER_SYMBOLS => {"ITER_SYMBOLS"}
        ITER_VARIABLES => {"ITER_VARIABLES"}
        ITER_ARITIES => { "ITER_ARITIES" }
        ITER_EXPR => { "ITER_EXPR" }
        ITER_NESTED => {"ITER_NESTED"}
        ACTION => {"ACTION"}
        _ => { return l.to_string() }
    }.to_string()
}

fn transition<F: FnMut(&mut ReadZipper<()>) -> ()>(stack: &mut Vec<u8>, loc: &mut ReadZipper<()>, f: &mut F) {
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
                    let buf = [b];
                    if loc.descend_to(buf) {
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

// fn indiscriminate_bidirectional_matching_instr(ez: &mut ExprZipper) -> (Vec<Instr>, Vec<Instr>) {
//     match ez.item() {
//         Ok(Tag::NewVar) | Ok(Tag::VarRef(_)) => {
//             vec![]
//         }
//         Ok(Tag::SymbolSize(_)) => { unreachable!() }
//         Err(s) => {
//             vec![ClearExpr(), RestrictSymbols(s.to_vec())]
//         }
//         Ok(Tag::Arity(a)) => {
//             let mut ins = vec![Instr::ClearSymbols(), RestrictArities(a)];
//             ins.extend(indiscriminate_bidirectional_matching_instr(ez));
//             ins.push()
//
//         }
//     }
// }


fn variable_or_arity_mask(a: u8) -> [u64; 4] {
    let mut m = unsafe { VARS.clone() };
    let arity_byte = item_byte(Tag::Arity(a));
    m[((arity_byte & 0b11000000) >> 6) as usize] |= 1u64 << (arity_byte & 0b00111111);
    m
}

fn variable_or_arity(z: &mut WriteZipper<()>, a: u8) {
    let m = variable_or_arity_mask(a);
    z.remove_masked_branches(m);
}

fn variable_or_size_mask(a: u8) -> [u64; 4] {
    let mut m = unsafe { VARS.clone() };
    let arity_byte = item_byte(Tag::SymbolSize(a));
    m[((arity_byte & 0b11000000) >> 6) as usize] |= 1u64 << (arity_byte & 0b00111111);
    m
}

// fn variable_or_symbol(z: &mut WriteZipper<()>, s: &[u8]) {
//     // ALTERNATIVE: build variable + s map, restrict to it
//     let m = variable_or_size_mask(s.len() as u8);
//     z.remove_masked_branches(m);
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
    symbols: BytesTrieMap<String>,
}

impl DataParser {
    fn new() -> Self {
        Self {
            count: 3,
            symbols: BytesTrieMap::new(),
        }
    }
}

fn gen_key<'a>(i: u64, buffer: *mut u8) -> &'a [u8] {
    let ir = u64::from_be(i);
    unsafe { ptr::write_unaligned(buffer as *mut u64, ir) };
    let bs = (8 - ir.trailing_zeros()/8) as usize;
    let l = bs.max(1);
    unsafe { std::slice::from_raw_parts(buffer.byte_offset((8 - l) as isize), l) }
}

impl Parser for DataParser {
    fn tokenizer(&mut self, s: String) -> String {
        return s;
        if let Some(r) = self.symbols.get(s.as_bytes()) {
            r.clone()
        } else {
            self.count += 1;
            let mut buf: [u8; 8] = [0; 8];
            let slice = gen_key(self.count, buf.as_mut_ptr());
            let string = String::from_utf8_lossy(slice).to_string();
            self.symbols.insert(s.as_bytes(), string.clone());
            string
        }
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
    let mut file = std::fs::File::open("/home/adam/Projects/metta-examples/aunt-kg/royal92_simple.metta")
        .expect("Should have been able to read the file");
    let mut it = BufferedIterator{ file: file, buffer: [0; 4096], cursor: 4096, max: 4096 };
    let mut parser = DataParser::new();

    let mut space = BytesTrieMap::<()>::new();
    // let space_ptr = &mut space as *mut BytesTrieMap<()>;


    let t0 = Instant::now();
    let mut i = 0;
    let mut stack = Vec::with_capacity(100);
    let mut vs = Vec::with_capacity(100);
    loop {
        unsafe {
            let mut ez = ExprZipper::new(Expr{ptr: stack.as_mut_ptr()});
            if parser.sexprUnsafe(&mut it, &mut vs, &mut ez) {
                stack.set_len(ez.loc);
                space.insert(&stack[..], ());
                // unsafe { println!("{}", std::str::from_utf8_unchecked(&stack[..])); }
                // ExprZipper::new(ez.root).traverse(0); println!();
            } else { break }
            i += 1;
            vs.set_len(0);
        }
    }
    // println!("built {}", i);
    // println!("took {} ms", t0.elapsed().as_millis());
    // println!("map contains: {}", space.val_count());


    let t0 = Instant::now();
    let REPEAT = 100;
    for _ in 0..REPEAT {
    let mut z = space.read_zipper();

    let mut buffer = vec![ACTION, ITER_EXPR];
    transition(&mut buffer, &mut z, &mut |loc| {
        // unsafe { println!("iter ({}) {}", loc.origin_path().unwrap().len(), std::str::from_utf8_unchecked(loc.origin_path().unwrap())); }
        // let e = Expr { ptr: loc.origin_path().unwrap().as_ptr().cast_mut() };
        // println!("{:?}", e);
        black_box(loc.origin_path());
    });
    }
    println!("iterating all took {} microseconds", (t0.elapsed().as_micros() as f64 / REPEAT as f64) as u64);

}
