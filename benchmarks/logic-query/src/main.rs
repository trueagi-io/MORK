use std::fs::File;
use std::hint::black_box;
use std::io::Read;
use std::time::Instant;
use mork_bytestring::*;
use mork_frontend::bytestring_parser::{Context, Parser, ParserError};
use pathmap::trie_map::BytesTrieMap;
use pathmap::zipper::{Zipper, ReadZipperUntracked, ZipperMoving, ZipperWriting};
use pathmap::zipper::{ZipperAbsolutePath, ZipperIteration};
use pathmap::utils::{ByteMaskIter, ByteMask};


static mut SIZES: [u64; 4] = [0u64; 4];
static mut ARITIES: [u64; 4] = [0u64; 4];
static mut VARS: [u64; 4] = [0u64; 4];

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
const BEGIN_RANGE: u8 = 12;
const FINALIZE_RANGE: u8 = 13;
const REFER_RANGE: u8 = 14;

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

fn all_at_depth<F>(loc: &mut ReadZipperUntracked<()>, level: u32, mut action: F) where F: FnMut(&mut ReadZipperUntracked<()>) -> () {
    assert!(level > 0);
    let mut i = 0;
    while i < level {
        if loc.descend_first_byte() {
            i += 1
        } else if loc.to_next_sibling_byte() {
        } else if loc.ascend_byte() {
            i -= 1
        } else {
            return;
        }
    }

    while i > 0 {
        if i == level {
            action(loc);
            if loc.to_next_sibling_byte() {
            } else {
                assert!(loc.ascend_byte());
                i -= 1;
            }
        } else if i < level {
            if loc.to_next_sibling_byte() {
                while i < level && loc.descend_first_byte() {
                    i += 1;
                }
            } else {
                if loc.ascend_byte() {
                    i -= 1;
                } else {
                    unreachable!();
                }
            }
        }
    }
}

fn transition<F: FnMut(&mut ReadZipperUntracked<()>) -> ()>(stack: &mut Vec<u8>, loc: &mut ReadZipperUntracked<()>, f: &mut F) {
    // println!("/stack {}", stack.iter().map(|x| label(*x)).reduce(|x, y| format!("{} {}", x, y)).unwrap_or("empty".to_string()));
    // println!("|path {:?}", serialize(loc.origin_path().unwrap()));
    // println!("\\label {}", label(*stack.last().unwrap()));
    let last = stack.pop().unwrap();
    match last {
        ACTION => { f(loc) }
        ITER_AT_DEPTH => {
            let size = stack.pop().unwrap();

            if false { // broken on normal execution
                all_at_depth(loc, size as _, |loc| transition(stack, loc, f));
            } else { // broken on all-dense-nodes execution
                if loc.descend_first_k_path(size as usize) {
                    transition(stack, loc, f);
                    while loc.to_next_k_path(size as usize) {
                        transition(stack, loc, f);
                    }
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
            let mut it = ByteMaskIter::new(m);

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
            let mut it = ByteMaskIter::new(m);

            while let Some(b) = it.next() {
                if loc.descend_to_byte(b) {
                    transition(stack, loc, f);
                }
                loc.ascend(1);
            }
        }
        ITER_ARITIES => {
            let m = mask_and(loc.child_mask(), unsafe { ARITIES });
            let mut it = ByteMaskIter::new(m);

            while let Some(b) = it.next() {
                if let Tag::Arity(a) = byte_item(b) {
                    if loc.descend_to_byte(b) {
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
            if loc.descend_to_byte(item_byte(Tag::SymbolSize(size))) {
                if loc.descend_to(&v[..]) {
                    transition(stack, loc, f);
                }
                loc.ascend(size as usize);
            }
            loc.ascend_byte();
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

            if loc.descend_to_byte(item_byte(Tag::SymbolSize(size))) {
                if loc.descend_to(&v[..]) {
                    transition(stack, loc, f);
                }
                loc.ascend(size as usize);
            }
            loc.ascend_byte();
            for _ in 0..size { stack.push(v.pop().unwrap()) }
            stack.push(size)
        }
        ITER_ARITY => {
            let arity = stack.pop().unwrap();
            if loc.descend_to_byte(item_byte(Tag::Arity(arity))) {
                transition(stack, loc, f);
            }
            loc.ascend_byte();
            stack.push(arity);
        }
        ITER_VAR_ARITY => {
            let arity = stack.pop().unwrap();

            stack.push(ITER_VARIABLES);
            transition(stack, loc, f);
            stack.pop();

            if loc.descend_to_byte(item_byte(Tag::Arity(arity))) {
                transition(stack, loc, f);
            }
            loc.ascend_byte();
            stack.push(arity);
        }
        _ => { unreachable!() }
    }
    stack.push(last);
}


fn referential_transition<F: FnMut(&mut ReadZipperUntracked<()>) -> ()>(stack: &mut Vec<u8>, loc: &mut ReadZipperUntracked<()>, references: &mut Vec<(u32, u32)>, f: &mut F) {
    // println!("/stack {}", stack.iter().map(|x| label(*x)).reduce(|x, y| format!("{} {}", x, y)).unwrap_or("empty".to_string()));
    // println!("|path {:?}", serialize(loc.origin_path().unwrap()));
    // println!("|refs {:?}", references);
    // println!("\\label {}", label(*stack.last().unwrap()));
    let last = stack.pop().unwrap();
    match last {
        ACTION => { f(loc) }
        ITER_AT_DEPTH => {
            let size = stack.pop().unwrap();

            if false { // broken on normal execution
                all_at_depth(loc, size as _, |loc| referential_transition(stack, loc, references, f));
            } else { // broken on all-dense-nodes execution
                if loc.descend_first_k_path(size as usize) {
                    referential_transition(stack, loc, references, f);
                    while loc.to_next_k_path(size as usize) {
                        referential_transition(stack, loc, references, f);
                    }
                }
            }
            stack.push(size);
        }
        ITER_NESTED => {
            let arity = stack.pop().unwrap();
            let l = stack.len();
            for _ in 0..arity { stack.push(ITER_EXPR); }
            referential_transition(stack, loc, references, f);
            stack.truncate(l);
            stack.push(arity)
        }
        ITER_SYMBOL_SIZE => {
            let m = mask_and(loc.child_mask(), unsafe { SIZES });
            let mut it = ByteMaskIter::new(m);

            while let Some(b) = it.next() {
                if let Tag::SymbolSize(s) = byte_item(b) {
                    let buf = [b];
                    if loc.descend_to(buf) {
                        let last = stack.pop().unwrap();
                        stack.push(s);
                        stack.push(last);
                        referential_transition(stack, loc, references, f);
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
            referential_transition(stack, loc, references, f);
            stack.pop();
            stack.pop();
        }
        ITER_VARIABLES => {
            let m = mask_and(loc.child_mask(), unsafe { VARS });
            let mut it = ByteMaskIter::new(m);

            while let Some(b) = it.next() {
                let buf = [b];
                if loc.descend_to(buf) {
                    referential_transition(stack, loc, references, f);
                }
                loc.ascend(1);
            }
        }
        ITER_ARITIES => {
            let m = mask_and(loc.child_mask(), unsafe { ARITIES });
            let mut it = ByteMaskIter::new(m);

            while let Some(b) = it.next() {
                if let Tag::Arity(a) = byte_item(b) {
                    let buf = [b];
                    if loc.descend_to(buf) {
                        let last = stack.pop().unwrap();
                        stack.push(a);
                        stack.push(last);
                        referential_transition(stack, loc, references, f);
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
            referential_transition(stack, loc, references, f);
            stack.pop();

            stack.push(ITER_SYMBOLS);
            referential_transition(stack, loc, references, f);
            stack.pop();

            stack.push(ITER_NESTED);
            stack.push(ITER_ARITIES);
            referential_transition(stack, loc, references, f);
            stack.pop();
            stack.pop();
        }
        ITER_SYMBOL => {
            let size = stack.pop().unwrap();
            let mut v = vec![];
            for _ in 0..size { v.push(stack.pop().unwrap()) }
            if loc.descend_to_byte(item_byte(Tag::SymbolSize(size))) {
                if loc.descend_to(&v[..]) {
                    referential_transition(stack, loc, references, f);
                }
                loc.ascend(size as usize);
            }
            loc.ascend_byte();
            for _ in 0..size { stack.push(v.pop().unwrap()) }
            stack.push(size)
        }
        ITER_VAR_SYMBOL => {
            let size = stack.pop().unwrap();
            let mut v = vec![];
            for _ in 0..size { v.push(stack.pop().unwrap()) }

            stack.push(ITER_VARIABLES);
            referential_transition(stack, loc, references, f);
            stack.pop();

            if loc.descend_to_byte(item_byte(Tag::SymbolSize(size))) {
                if loc.descend_to(&v[..]) {
                    referential_transition(stack, loc, references, f);
                }
                loc.ascend(size as usize);
            }
            loc.ascend_byte();
            for _ in 0..size { stack.push(v.pop().unwrap()) }
            stack.push(size)
        }
        ITER_ARITY => {
            let arity = stack.pop().unwrap();
            if loc.descend_to_byte(item_byte(Tag::Arity(arity))) {
                referential_transition(stack, loc, references, f);
            }
            loc.ascend_byte();
            stack.push(arity);
        }
        ITER_VAR_ARITY => {
            let arity = stack.pop().unwrap();

            stack.push(ITER_VARIABLES);
            referential_transition(stack, loc, references, f);
            stack.pop();

            if loc.descend_to_byte(item_byte(Tag::Arity(arity))) {
                referential_transition(stack, loc, references, f);
            }
            loc.ascend_byte();
            stack.push(arity);
        }
        BEGIN_RANGE => {
            references.push((loc.path().len() as u32, 0));
            referential_transition(stack, loc, references, f);
            references.pop();
        }
        FINALIZE_RANGE => {
            references.last_mut().unwrap().1 = loc.path().len() as u32;
            referential_transition(stack, loc, references, f);
            references.last_mut().unwrap().1 = 0;
        }
        REFER_RANGE => {
            let index = stack.pop().unwrap();
            let (begin, end) = references[index as usize];
            let subexpr = Expr { ptr: loc.path()[begin as usize..end as usize].as_ptr().cast_mut() };

            let substack = indiscriminate_bidirectional_matching_stack(&mut ExprZipper::new(subexpr));
            let substack_len = substack.len();
            stack.extend(substack);
            referential_transition(stack, loc, references, f);
            stack.truncate(stack.len() - substack_len);

            // println!("pushing ITER_EXPR but could do {}", serialize(&loc.path()[begin as usize..end as usize]));
            // stack.push(ITER_EXPR);
            // referential_transition(stack, loc, references, f);
            // stack.pop();

            stack.push(index);
        }
        _ => { unreachable!() }
    }
    stack.push(last);
}


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

fn referential_bidirectional_matching_stack(ez: &mut ExprZipper) -> Vec<u8> {
    let mut v = vec![];
    loop {
        match ez.item() {
            Ok(Tag::NewVar) => {
                v.push(BEGIN_RANGE);
                v.push(ITER_EXPR);
                v.push(FINALIZE_RANGE);
            }
            Ok(Tag::VarRef(r)) => {
                v.push(REFER_RANGE);
                v.push(r);
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
    for size in 0..64 {
        let k = item_byte(Tag::VarRef(size));
        unsafe { VARS[((k & 0b11000000) >> 6) as usize] |= 1u64 << (k & 0b00111111); }
    }


    // let mut file = std::fs::File::open("/home/adam/Projects/metta-examples/aunt-kg/royal92.metta")
    let mut file = std::fs::File::open("/home/adam/Projects/MORK/benchmarks/logic-query/resources/big.metta")
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
    let mut stack = [0u8; 2 << 19];
    loop {
        let mut ez = ExprZipper::new(Expr{ptr: stack.as_mut_ptr()});
        match parser.sexpr(&mut it, &mut ez) {
            Ok(()) => {
                // println!("{:?}", ez.root);
                space.insert(&stack[..ez.loc], ());
            }
            Err(ParserError::InputFinished) => break,
            Err(other) => panic!("{:?} (byte {}, line {})", other, it.loc, it.src[..it.loc].iter().rfold(0, |t, b| t + (if *b == b'\n' { 1 } else { 0 })))
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
    // let mut references: Vec<(u32, u32)> = vec![];
    // referential_transition(&mut buffer, &mut z, &mut references, &mut |loc| {
    transition(&mut buffer, &mut z, &mut |loc| {
        black_box(loc.origin_path());
        visited += 1;
    });
    println!("iterating all ({}) took {} microseconds", visited, t0.elapsed().as_micros());

    // let mut keeping = BytesTrieMap::from_iter(space.iter());

    // let mut f = File::create_new("/home/adam/Projects/MORK/benchmarks/logic-query/resources/big.metta.paths").unwrap();
    // let mut fv = vec![];
    // match space.serialize_paths(&[], &mut fv) {
    //     Ok((wr, bc, pc)) => { println!("ok {wr} {bc} {pc}") }
    //     Err(e) => { println!("err {e}") }
    // }
    // let mut recover: BytesTrieMap<()> = BytesTrieMap::new();
    // let mut f = File::open("/home/adam/Projects/MORK/benchmarks/logic-query/resources/big2.metta.paths").unwrap();
    // let mut fv = vec![];
    // f.read_to_end(&mut fv).unwrap();
    // println!("len {}", fv.len());
    // let mut _fv = vec![];
    // space.serialize_dag(&mut _fv);
    // space.serialize_tree(&mut _fv);
    // let t0 = Instant::now();
    // match recover.deserialize_paths(&[], &fv[..], ()) {
    //     Ok((wr, bc, pc)) => { println!("ok {wr} {bc} {pc} ({})", t0.elapsed().as_micros()) }
    //     Err(e) => { println!("err {} {e}", e.kind()) }
    // }
    // println!("{} {}", recover.val_count(), space.val_count());
    //
    // let mut lrz = recover.read_zipper();
    // while let Some(_) = lrz.to_next_val() {
    //     assert!(space.contains(lrz.path()), "{}", std::str::from_utf8(lrz.path()).unwrap());
    // }
    //
    // let mut rrz = space.read_zipper();
    // while let Some(_) = rrz.to_next_val() {
    //     assert!(recover.contains(rrz.path()));
    // }

    return;
    // let mut keeping_wz = keeping.write_zipper();
    let mut z = space.read_zipper();
    let mut k = 0;
    let mut total_unified = 0;
    let mut max_unified = 0;
    let mut total_res = 0;
    let mut max_res = 0;
    let mut buffer = vec![];
    while let Some(_) = z.to_next_val() {
        let se = Expr{ ptr: z.path().as_ptr().cast_mut() };
        buffer.push(ACTION);
        if k % 100 == 0 { println!("expr  {}", unsafe { serialize(se.span().as_ref().unwrap()) }); }
        buffer.extend(indiscriminate_bidirectional_matching_stack(&mut ExprZipper::new(se)));
        // buffer.extend(referential_bidirectional_matching_stack(&mut ExprZipper::new(se)));
        let mut visited = 0;
        let mut unified = 0;
        let mut rz = space.read_zipper();
        let mut references: Vec<(u32, u32)> = vec![];

        transition(&mut buffer, &mut rz, &mut |loc| {
        // referential_transition(&mut buffer, &mut rz, &mut references, &mut |loc| {
        //     black_box(loc.origin_path());
            visited += 1;
            // assert!(space.contains(loc.path()));

            // if z.path() != loc.path() {
            //     let se_copy = Expr { ptr: z.path().to_vec().leak().as_mut_ptr() };
            //     let pe = Expr { ptr: loc.path().as_ptr().cast_mut() };
            //     let pe_copy = Expr { ptr: loc.path().to_vec().leak().as_mut_ptr() };
            //
            //     match Expr::unification(se_copy, pe_copy) {
            //         Ok(e) => {
            //             std::hint::black_box(e);
            //             unified += 1;
            //             // keeping.remove_old(loc.path());
            //             // keeping_wz.descend_to(loc.path());
            //             // assert!(keeping.contains(loc.path()));
            //             // assert!(keeping_wz.path_exists());
            //             // assert!(space.contains(keeping_wz.path()));
            //             // assert!(keeping_wz.remove_value().is_some());
            //             keeping.remove(loc.path());
            //             // keeping_wz.reset();
            //         }
            //         Err(_) => {}
            //     }
            // }
        });
        // assert!(visited >= 1);
        total_res += visited;
        max_res = max_res.max(visited);
        total_unified += unified;
        max_unified = max_unified.max(unified);
        k += 1;
        buffer.clear();
    }

    println!("searching all in all (queries {} average res {}, max res {}) took {} microseconds", k, total_res/k, max_res, t0.elapsed().as_micros());
    println!("total unified {} (max unified {})", total_unified, max_unified);
    // println!("kept {}", keeping.val_count());
    // with unification, with all_dense_nodes
    // transition
    // searching all in all (queries 91692 average res 6, max res 23625) took 64735923 microseconds
    // total unified 28012 (max unified 137)
    // kept 76477
    // referential_transition
    // searching all in all (queries 91692 average res 2, max res 12196) took 67015791 microseconds
    // total unified 26788 (max unified 137)
    // kept 76750
    return;

    // let t0 = Instant::now();
    // let mut z = space.read_zipper();
    //
    // let mut visited = 0;
    // let mut buffer = vec![ACTION];
    // let mut q = vec![item_byte(Tag::Arity(3))];
    // let relations_symbol = parser.tokenizer(b"Individuals");
    // q.push(item_byte(Tag::SymbolSize(relations_symbol.len() as u8)));
    // q.extend(&relations_symbol[..]);
    // q.push(item_byte(Tag::NewVar));
    // q.push(item_byte(Tag::Arity(2)));
    // let fullname_symbol = parser.tokenizer(b"Fullname");
    // q.push(item_byte(Tag::SymbolSize(fullname_symbol.len() as u8)));
    // q.extend(&fullname_symbol[..]);
    // q.push(item_byte(Tag::NewVar));
    // buffer.extend(indiscriminate_bidirectional_matching_stack(&mut ExprZipper::new(Expr{ ptr: q.as_mut_ptr() })));
    // transition(&mut buffer, &mut z, &mut |loc| {
    //     black_box(loc.origin_path());
    //     visited += 1;
    // });
    //
    // println!("iterating {:?} ({}) took {} microseconds", q, visited, t0.elapsed().as_micros());
    //
    // let t0 = Instant::now();
    // let mut z = space.read_zipper();
    //
    // let mut visited = 0;
    // let mut buffer = vec![ACTION];
    // let mut q = vec![item_byte(Tag::Arity(3))];
    // let relations_symbol = parser.tokenizer(b"Relations");
    // q.push(item_byte(Tag::SymbolSize(relations_symbol.len() as u8)));
    // q.extend(&relations_symbol[..]);
    // let interest_symbol = parser.tokenizer(b"1350");
    // q.push(item_byte(Tag::SymbolSize(interest_symbol.len() as u8)));
    // q.extend(&interest_symbol[..]);
    // q.push(item_byte(Tag::NewVar));
    // buffer.extend(indiscriminate_bidirectional_matching_stack(&mut ExprZipper::new(Expr{ ptr: q.as_mut_ptr() })));
    // transition(&mut buffer, &mut z, &mut |loc| {
    //     black_box(loc.origin_path());
    //     visited += 1;
    // });
    //
    // println!("iterating {:?} ({}) took {} microseconds", q, visited, t0.elapsed().as_micros());

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
