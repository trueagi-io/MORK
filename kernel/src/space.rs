use std::io::Write;
use std::process;
use std::fs::File;
use std::time::Instant;
use mork_bytestring::{byte_item, Expr, ExprZipper, ExtractFailure, item_byte, Tag};
use mork_frontend::bytestring_parser::{Parser, ParserError, Context};
use bucket_map::{WritePermit, SharedMapping, SharedMappingHandle};
use pathmap::trie_map::BytesTrieMap;
use pathmap::utils::ByteMaskIter;
use pathmap::zipper::{ReadZipperUntracked, ZipperMoving, WriteZipperUntracked, Zipper, ZipperAbsolutePath, ZipperIteration, ZipperWriting, ZipperCreation};

pub struct Space {
    pub(crate) btm: BytesTrieMap<()>,
    pub sm: SharedMappingHandle
}

const SIZES: [u64; 4] = {
    let mut ret = [0u64; 4];
    let mut size = 1;
    while size < 64 {
        let k = item_byte(Tag::SymbolSize(size));
        ret[((k & 0b11000000) >> 6) as usize] |= 1u64 << (k & 0b00111111);
        size += 1;
    }
    ret
};
const ARITIES: [u64; 4] = {
    let mut ret = [0u64; 4];
    let mut arity = 1;
    while arity < 64 {
        let k = item_byte(Tag::Arity(arity));
        ret[((k & 0b11000000) >> 6) as usize] |= 1u64 << (k & 0b00111111);
        arity += 1;
    }
    ret
};
const VARS: [u64; 4] = {
    let mut ret = [0u64; 4];
    let nv_byte = item_byte(Tag::NewVar);
    ret[((nv_byte & 0b11000000) >> 6) as usize] |= 1u64 << (nv_byte & 0b00111111);
    let mut size = 0;
    while size < 64 {
        let k = item_byte(Tag::VarRef(size));
        ret[((k & 0b11000000) >> 6) as usize] |= 1u64 << (k & 0b00111111);
        size += 1;
    }
    ret
};

fn mask_and(l: [u64; 4], r: [u64; 4]) -> [u64; 4] {
    [l[0] & r[0], l[1] & r[1], l[2] & r[2], l[3] & r[3]]
}

/// this module will get refactored out 
pub(crate) mod space_constants {
    pub(crate) const ITER_AT_DEPTH    : u8 =  0;
    pub(crate) const ITER_SYMBOL_SIZE : u8 =  1;
    pub(crate) const ITER_SYMBOLS     : u8 =  2;
    pub(crate) const ITER_VARIABLES   : u8 =  3;
    pub(crate) const ITER_ARITIES     : u8 =  4;
    pub(crate) const ITER_EXPR        : u8 =  5;
    pub(crate) const ITER_NESTED      : u8 =  6;
    pub(crate) const ITER_SYMBOL      : u8 =  7;
    pub(crate) const ITER_ARITY       : u8 =  8;
    pub(crate) const ITER_VAR_SYMBOL  : u8 =  9;
    pub(crate) const ITER_VAR_ARITY   : u8 = 10;
    pub(crate) const ACTION           : u8 = 11;
    pub(crate) const BEGIN_RANGE      : u8 = 12;
    pub(crate) const FINALIZE_RANGE   : u8 = 13;
    pub(crate) const REFER_RANGE      : u8 = 14;
}
use space_constants::*;

#[allow(unused)]
fn label(l: u8) -> String {
    match l {
        ITER_AT_DEPTH    => { "ITER_AT_DEPTH"      }
        ITER_SYMBOL_SIZE => { "ITER_SYMBOL_SIZE"   }
        ITER_SYMBOLS     => { "ITER_SYMBOLS"       }
        ITER_VARIABLES   => { "ITER_VARIABLES"     }
        ITER_ARITIES     => { "ITER_ARITIES"       }
        ITER_EXPR        => { "ITER_EXPR"          }
        ITER_NESTED      => { "ITER_NESTED"        }
        ITER_SYMBOL      => { "ITER_SYMBOL"        }
        ITER_ARITY       => { "ITER_ARITY"         }
        ITER_VAR_SYMBOL  => { "ITER_VAR_SYMBOL"    }
        ITER_VAR_ARITY   => { "ITER_VAR_ARITY"     }
        ACTION           => { "ACTION"             }
        _                => { return l.to_string() }
    }.to_string()
}

fn all_at_depth<Z : ZipperMoving, F>(loc: &mut Z, level: u32, mut action: F) where F: FnMut(&mut Z) -> () {
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
            let m = mask_and(loc.child_mask(), SIZES);
            let mut it = pathmap::utils::ByteMaskIter::new(m);

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
            let m = mask_and(loc.child_mask(), VARS);
            let mut it = ByteMaskIter::new(m);

            while let Some(b) = it.next() {
                let buf = [b];
                if loc.descend_to(buf) {
                    transition(stack, loc, f);
                }
                loc.ascend(1);
            }
        }
        ITER_ARITIES => {
            let m = mask_and(loc.child_mask(), ARITIES);
            let mut it = ByteMaskIter::new(m);

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
            loc.descend_to(&[item_byte(Tag::SymbolSize(size))]);
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

            loc.descend_to(&[item_byte(Tag::SymbolSize(size))]);
            loc.descend_to(&v[..]);
            transition(stack, loc, f);
            loc.ascend(size as usize);
            loc.ascend(1);
            for _ in 0..size { stack.push(v.pop().unwrap()) }
            stack.push(size)
        }
        ITER_ARITY => {
            let arity = stack.pop().unwrap();
            loc.descend_to(&[item_byte(Tag::Arity(arity))]);
            transition(stack, loc, f);
            loc.ascend(1);
            stack.push(arity);
        }
        ITER_VAR_ARITY => {
            let arity = stack.pop().unwrap();

            stack.push(ITER_VARIABLES);
            transition(stack, loc, f);
            stack.pop();

            loc.descend_to(&[item_byte(Tag::Arity(arity))]);
            transition(stack, loc, f);
            loc.ascend(1);
            stack.push(arity);
        }
        _ => { unreachable!() }
    }
    stack.push(last);
}

fn referential_transition<Z : ZipperMoving + Zipper<()>, F: FnMut(&mut Z) -> ()>(stack: &mut Vec<u8>, loc: &mut Z, references: &mut Vec<(u32, u32)>, f: &mut F) {
    // println!("/stack {}", stack.iter().map(|x| label(*x)).reduce(|x, y| format!("{} {}", x, y)).unwrap_or("empty".to_string()));
    // println!("|path {:?}", serialize(loc.origin_path().unwrap()));
    // println!("|refs {:?}", references);
    // println!("\\label {}", label(*stack.last().unwrap()));
    let last = stack.pop().unwrap();
    match last {
        ACTION => { f(loc) }
        ITER_AT_DEPTH => {
            let size = stack.pop().unwrap();
            all_at_depth(loc, size as _, |loc| referential_transition(stack, loc, references, f));
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
            let m = mask_and(loc.child_mask(), SIZES);
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
            let m = mask_and(loc.child_mask(), VARS);
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
            let m = mask_and(loc.child_mask(), ARITIES);
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
pub(crate) struct ParDataParser<'a> { count: u64, buf: [u8; 8], write_permit: WritePermit<'a> }

impl <'a> Parser for ParDataParser<'a> {
    fn tokenizer<'r>(&mut self, s: &[u8]) -> &'r [u8] {
        self.count += 1;
        // FIXME hack until either the parser is rewritten or we can take a pointer of the symbol
        self.buf = self.write_permit.get_sym_or_insert(s);
        return unsafe { std::mem::transmute(&self.buf[..]) };
    }
}

impl <'a> ParDataParser<'a> {
    pub(crate) fn new(handle: &'a SharedMappingHandle) -> Self {
        Self {
            count: 3,
            buf: (3u64).to_be_bytes(),
            write_permit: handle.try_aquire_permission().unwrap()
        }
    }
}

pub type PathCount      = usize;
pub type NodeCount      = usize;
pub type AttributeCount = usize;
pub type SExprCount     = usize;

pub struct SpaceTranscriber<'a, 'b, 'c> { 
    /// count of unnested values == path_count
    path_count : PathCount, 
    wz         : &'c mut WriteZipperUntracked<'a, 'b, ()>,
    pdp        : ParDataParser<'a> }
impl <'a, 'b, 'c> SpaceTranscriber<'a, 'b, 'c> {
    #[inline(always)] fn write<S : Into<String>>(&mut self, s: S) {
        let token = self.pdp.tokenizer(s.into().as_bytes());
        let mut path = vec![item_byte(Tag::SymbolSize(token.len() as u8))];
        path.extend(token);
        self.wz.descend_to(&path[..]);
        self.wz.set_value(());
        self.wz.ascend(path.len());
    }
}
impl <'a, 'b, 'c> crate::json_parser::Transcriber for SpaceTranscriber<'a, 'b, 'c> {
    #[inline(always)] fn descend_index(&mut self, i: usize, first: bool) -> () {
        if first { self.wz.descend_to(&[item_byte(Tag::Arity(2))]); }
        let token = self.pdp.tokenizer(i.to_string().as_bytes());
        self.wz.descend_to(&[item_byte(Tag::SymbolSize(token.len() as u8))]);
        self.wz.descend_to(token);
    }
    #[inline(always)] fn ascend_index(&mut self, i: usize, last: bool) -> () {
        self.wz.ascend(self.pdp.tokenizer(i.to_string().as_bytes()).len() + 1);
        if last { self.wz.ascend(1); }
    }
    #[inline(always)] fn write_empty_array(&mut self) -> () { self.write("[]"); self.path_count += 1; }
    #[inline(always)] fn descend_key(&mut self, k: &str, first: bool) -> () {
        if first { self.wz.descend_to(&[item_byte(Tag::Arity(2))]); }
        let token = self.pdp.tokenizer(k.to_string().as_bytes());
        // let token = k.to_string();
        self.wz.descend_to(&[item_byte(Tag::SymbolSize(token.len() as u8))]);
        self.wz.descend_to(token);
    }
    #[inline(always)] fn ascend_key(&mut self, k: &str, last: bool) -> () {
        let token = self.pdp.tokenizer(k.to_string().as_bytes());
        // let token = k.to_string();
        self.wz.ascend(token.len() + 1);
        if last { self.wz.ascend(1); }
    }
    #[inline(always)] fn write_empty_object(&mut self) -> () { self.write("{}"); self.path_count += 1; }
    #[inline(always)] fn write_string(&mut self, s: &str) -> () { self.write(s); self.path_count += 1; }
    #[inline(always)] fn write_number(&mut self, negative: bool, mantissa: u64, exponent: i16) -> () {
        let mut s = String::new();
        if negative { s.push('-'); }
        s.push_str(mantissa.to_string().as_str());
        if exponent != 0 { s.push('e'); s.push_str(exponent.to_string().as_str()); }
        self.write(s);
        self.path_count += 1;
    }
    #[inline(always)] fn write_true(&mut self) -> () { self.write("true"); self.path_count += 1; }
    #[inline(always)] fn write_false(&mut self) -> () { self.write("false"); self.path_count += 1; }
    #[inline(always)] fn write_null(&mut self) -> () { self.write("null"); self.path_count += 1; }
    #[inline(always)] fn begin(&mut self) -> () {}
    #[inline(always)] fn end(&mut self) -> () {}
}

#[macro_export]
macro_rules! expr {
    ($space:ident, $s:literal) => {{
        let mut src = parse!($s);
        let q = Expr{ ptr: src.as_mut_ptr() };
        let mut pdp = ParDataParser::new(&$space.sm);
        let mut buf = [0u8; 2048];
        let p = Expr{ ptr: buf.as_mut_ptr() };
        let used = q.substitute_symbols(&mut ExprZipper::new(p), |x| pdp.tokenizer(x));
        unsafe {
            let b = std::alloc::alloc(std::alloc::Layout::array::<u8>(used.len()).unwrap());
            std::ptr::copy_nonoverlapping(p.ptr, b, used.len());
            Expr{ ptr: b }
        }
    }};
}

#[macro_export]
macro_rules! sexpr {
    ($space:ident, $e:expr) => {{
        let mut v = vec![];
        $e.serialize(&mut v, |s| {
            let symbol = i64::from_be_bytes(s.try_into().unwrap()).to_be_bytes();
            let mstr = $space.sm.get_bytes(symbol).map(unsafe { |x| std::str::from_utf8_unchecked(x) });
            // println!("symbol {symbol:?}, bytes {mstr:?}");
            unsafe { std::mem::transmute(mstr.expect(format!("failed to look up {:?}", symbol).as_str())) }
        });
        String::from_utf8(v).unwrap()
    }};
}

impl Space {
    pub fn new() -> Self {
        Self { btm: BytesTrieMap::new(), sm: SharedMapping::new() }
    }


    // Remy : we need to be able to reconstruct the map to do exports within the server
    #[doc(hidden)]
    /// Although not memory unsafe, the caller of this function is given the burden of passing the correct [`SharedMapping`]
    /// to interpret the symbols embedded in the map.
    /// It has been made unsafe to describe the fact that it cannot guarantee with a Result that the mapping passed in is valid.
    pub unsafe fn reconstruct(btm : BytesTrieMap<()>, sm : SharedMappingHandle) -> Space{
        Space {
            btm,
            sm,
        }
    }

    pub fn statistics(&self) {
        println!("val count {}", self.btm.val_count());
    }

    fn write_zipper_unchecked<'a>(&'a self) -> WriteZipperUntracked<'a, 'a, ()> {
        unsafe { (&self.btm as *const BytesTrieMap<()>).cast_mut().as_mut().unwrap().write_zipper() }
    }

    pub fn load_csv(&mut self, r: &str) -> Result<PathCount, String> {
        let mut i = 0;
        let mut stack = [0u8; 2048];
        let mut pdp = ParDataParser::new(&self.sm);
        for sv in r.as_bytes().split(|&x| x == b'\n') {
            if sv.len() == 0 { continue }
            let mut a = 0;
            let e = Expr{ ptr: stack.as_mut_ptr() };
            let mut ez = ExprZipper::new(e);
            ez.loc += 1;
            for symbol in sv.split(|&x| x == b',') {
                let internal = pdp.tokenizer(symbol);
                ez.write_symbol(&internal[..]);
                ez.loc += internal.len() + 1;
                a += 1;
            }
            let total = ez.loc;
            ez.reset();
            ez.write_arity(a);
            self.btm.insert(&stack[..total], ());
            i += 1;
        }

        Ok(i)
    }

    pub fn load_json(&mut self, r: &str) -> Result<PathCount, String> {
        let mut wz = self.write_zipper_unchecked();
        let mut st = SpaceTranscriber{ path_count: 0, wz: &mut wz, pdp: ParDataParser::new(&self.sm) };
        let mut p = crate::json_parser::Parser::new(r);
        p.parse(&mut st).map_err(|e| format!("{e}"))?;
        Ok(st.path_count)
    }

    pub fn load_neo4j_triples(&mut self, uri: &str, user: &str, pass: &str) -> Result<PathCount, String> {
        use neo4rs::*;
        let graph = Graph::new(uri, user, pass).unwrap();

        let rt = tokio::runtime::Builder::new_current_thread()
          .enable_io()
          .build()
          .unwrap();
        let mut pdp = ParDataParser::new(&self.sm);

        let mut count = 0;

        let mut result = rt.block_on(graph.execute(
            query("MATCH (s)-[p]->(o) RETURN id(s), id(p), id(o)"))).unwrap();
        let spo_symbol = pdp.tokenizer("SPO".as_bytes());
        while let Ok(Some(row)) = rt.block_on(result.next()) {
            let s: i64 = row.get("id(s)").unwrap();
            let p: i64 = row.get("id(p)").unwrap();
            let o: i64 = row.get("id(o)").unwrap();
            let mut buf = [0u8; 64];
            let e = Expr{ ptr: buf.as_mut_ptr() };
            let mut ez = ExprZipper::new(e);
            ez.write_arity(4);
            ez.loc += 1;
            {
                ez.write_symbol(&spo_symbol[..]);
                ez.loc += spo_symbol.len() + 1;
            }
            {
                let internal = pdp.tokenizer(&s.to_be_bytes());
                ez.write_symbol(&internal[..]);
                ez.loc += internal.len() + 1;
            }
            {
                let internal = pdp.tokenizer(&p.to_be_bytes());
                ez.write_symbol(&internal[..]);
                ez.loc += internal.len() + 1;
            }
            {
                let internal = pdp.tokenizer(&o.to_be_bytes());
                ez.write_symbol(&internal[..]);
                ez.loc += internal.len() + 1;
            }
            // space.
            self.btm.insert(ez.span(), ());
            count += 1;
        }
        Ok(count)
    }

    pub fn load_neo4j_node_properties(&mut self, uri: &str, user: &str, pass: &str) -> Result<(NodeCount, AttributeCount), String> {
        use neo4rs::*;
        let graph = Graph::new(uri, user, pass).unwrap();

        let rt = tokio::runtime::Builder::new_current_thread()
          .enable_io()
          .build()
          .unwrap();
        let mut pdp = ParDataParser::new(&self.sm);
        let zh = self.btm.zipper_head();
        let mut wz = zh.write_zipper_at_exclusive_path(&[]).unwrap();
        let sa_symbol = pdp.tokenizer("NKV".as_bytes());
        let mut nodes = 0;
        let mut attributes = 0;

        wz.descend_to_byte(item_byte(Tag::Arity(4)));
        wz.descend_to_byte(item_byte(Tag::SymbolSize(sa_symbol.len() as _)));
        wz.descend_to(sa_symbol);

        let mut result = rt.block_on(graph.execute(
            query("MATCH (s) RETURN id(s), s"))
        ).unwrap();
        while let Ok(Some(row)) = rt.block_on(result.next()) {
            let s: i64 = row.get("id(s)").unwrap();
            let internal_s = pdp.tokenizer(&s.to_be_bytes());
            wz.descend_to_byte(item_byte(Tag::SymbolSize(internal_s.len() as _)));
            wz.descend_to(internal_s);

            let a: BoltMap = row.get("s").unwrap();

            for (bs, bt) in a.value.iter() {
                let internal_k = pdp.tokenizer(bs.value.as_bytes());
                wz.descend_to_byte(item_byte(Tag::SymbolSize(internal_k.len() as _)));
                wz.descend_to(internal_k);

                let BoltType::String(bv) = bt else { unreachable!() };

                let internal_v = pdp.tokenizer(bv.value.as_bytes());
                wz.descend_to_byte(item_byte(Tag::SymbolSize(internal_v.len() as _)));
                wz.descend_to(internal_v);

                wz.set_value(());

                wz.ascend(internal_v.len() + 1);

                wz.ascend(internal_k.len() + 1);
                attributes += 1;
            }

            wz.ascend(internal_s.len() + 1);
            nodes += 1;
            if nodes % 1000000 == 0 {
                println!("{nodes} {attributes}");
            }
        }
        Ok((nodes, attributes))
    }

    pub fn load_sexpr(&mut self, r: &str) -> Result<SExprCount, String> {
        let mut it = Context::new(r.as_bytes());

        let mut i = 0;
        let mut stack = [0u8; 2048];
        let mut parser = ParDataParser::new(&self.sm);
        loop {
            let mut ez = ExprZipper::new(Expr{ptr: stack.as_mut_ptr()});
            match parser.sexpr(&mut it, &mut ez) {
                Ok(()) => { self.btm.insert(&stack[..ez.loc], ()); }
                Err(ParserError::InputFinished) => { break }
                Err(other) => { panic!("{:?}", other) }
            }
            i += 1;
            it.variables.clear();
        }
        Ok(i)
    }

    pub fn dump_as_sexpr<W : Write>(&self, w: &mut W) -> Result<PathCount, String> {
        let mut rz = self.btm.read_zipper();

        let t0 = Instant::now();
        let mut i = 0;
        loop {
            match rz.to_next_val() {
                None => { break }
                Some(()) => {
                    let path = rz.origin_path().unwrap();
                    let e = Expr { ptr: path.as_ptr().cast_mut() };
                    e.serialize(w, |s| {
                        let symbol = i64::from_be_bytes(s.try_into().unwrap()).to_be_bytes();
                        let mstr = self.sm.get_bytes(symbol).map(unsafe { |x| std::str::from_utf8_unchecked(x) });
                        #[cfg(debug_assertions)]
                        println!("symbol {symbol:?}, bytes {mstr:?}");
                        unsafe { std::mem::transmute(mstr.expect(format!("failed to look up {:?}", symbol).as_str())) }
                    });
                    w.write(&[b'\n']).map_err(|x| x.to_string())?;
                    i += 1;
                }
            }
        }
        println!("dumping took {} ms", t0.elapsed().as_millis());
        Ok(i)
    }

    pub fn backup_symbols<OutFilePath : AsRef<std::path::Path>>(&self, path: OutFilePath) -> Result<(), std::io::Error>  {
        self.sm.serialize(path)
    }

    pub fn restore_symbols(&mut self, path: impl AsRef<std::path::Path>) -> Result<(), std::io::Error> {
        self.sm = bucket_map::SharedMapping::deserialize(path)?;
        Ok(())
    }

    pub fn backup_as_dag<OutFilePath : AsRef<std::path::Path>>(&self, path: OutFilePath) -> Result<(), std::io::Error> {
        pathmap::serialization::write_trie("neo4j triples", self.btm.read_zipper(),
                                           |_v, _b| pathmap::serialization::ValueSlice::Read(&[]),
                                           path.as_ref()).map(|_| ())
    }

    pub fn restore_from_dag(&mut self, path: impl AsRef<std::path::Path>) -> Result<(), std::io::Error> {
        self.btm = pathmap::serialization::deserialize_file(path, |_| ())?;
        Ok(())
    }

    pub fn backup_as_paths<OutFilePath : AsRef<std::path::Path>>(&self, path: OutFilePath) -> Result<pathmap::path_serialization::SerializationStats, std::io::Error> {
        let mut file = File::create(path).unwrap();
        pathmap::path_serialization::serialize_paths_(self.btm.read_zipper(), &mut file)
    }

    pub fn restore_as_paths<OutFilePath : AsRef<std::path::Path>>(&mut self, path: OutFilePath) -> Result<pathmap::path_serialization::DeserializationStats, std::io::Error> {
        let mut file = File::open(path).unwrap();
        pathmap::path_serialization::deserialize_paths(self.btm.write_zipper(), &mut file, |_, _| ())
    }

    pub fn query<F : FnMut(Expr) -> ()>(&self, pattern: Expr, mut effect: F) {
        let mut rz = self.btm.read_zipper();
        let mut pz = ExprZipper::new(pattern);
        let mut stack = vec![ACTION];
        stack.extend(indiscriminate_bidirectional_matching_stack(&mut pz));
        transition(&mut stack, &mut rz, &mut |loc| {
            let e = Expr { ptr: loc.origin_path().unwrap().as_ptr().cast_mut() };
            effect(e);
        });
    }

    pub fn transform(&mut self, pattern: Expr, template: Expr) {
        // todo take read zipper at static pattern prefix
        let mut rz = self.btm.read_zipper();
        // todo take write zipper at static template prefix
        let mut wz = self.write_zipper_unchecked();
        let mut pz = ExprZipper::new(pattern);
        // todo create feedback signal from ExprZipper to buffer size
        let mut buffer = [0u8; 512];
        let mut stack = vec![ACTION];
        // todo generate matching from dynamic postfix
        stack.extend(indiscriminate_bidirectional_matching_stack(&mut pz));
        // todo transition should gather pattern bindings
        transition(&mut stack, &mut rz, &mut |loc| {
            // todo split Readable and Writeable Expr
            let e = Expr { ptr: loc.origin_path().unwrap().as_ptr().cast_mut() };
            let mut oz = ExprZipper::new(Expr { ptr: buffer.as_mut_ptr() });
            // todo generate transform(Data) functions outside of transition
            match e.transformData(pattern, template, &mut oz) {
                Ok(()) => {
                    // todo (here and below) descend to dynamic path and reset/ascend to static prefix
                    // println!("{}", sexpr!(self, oz.root));
                    wz.descend_to(&buffer[..oz.loc]);
                    wz.set_value(());
                    wz.reset()
                }
                Err(ExtractFailure::IntroducedVar()) | Err(ExtractFailure::RecurrentVar(_)) => {
                    // upgrade to full unification
                    // println!("full unification");
                    match e.transform(pattern, template) {
                        Ok(e) => {
                            wz.descend_to(unsafe { &*e.span() });
                            wz.set_value(());
                            wz.reset()
                        }
                        _ => {

                        }
                    }
                }
                _ => {}
            }
        });
    }

    pub fn transform_multi(&mut self, patterns: &[Expr], template: Expr) {
        #![allow(unused)]
        let mut arity_hack = BytesTrieMap::new();
        arity_hack.write_zipper_at_path(&[item_byte(Tag::Arity(patterns.len() as _))]).graft(&self.btm.read_zipper());
        let mut rz = arity_hack.read_zipper();
        let mut prz = pathmap::experimental::ProductZipper::new(rz, patterns[1..].iter().map(|_| self.btm.read_zipper()));
        let mut wz = self.write_zipper_unchecked();

        let mut buffer = [0u8; 512];
        let mut stack = vec![ACTION];

        let mut compound_vec = vec![item_byte(Tag::Arity(patterns.len() as _))];
        for pattern in patterns.iter() {
            compound_vec.extend_from_slice(unsafe { &*pattern.span() });
        }
        // for pattern in patterns.iter().rev() {
        //     let mut pz = ExprZipper::new(*pattern);
        //     stack.extend(referential_bidirectional_matching_stack(&mut pz));
        // }
        // stack.push(patterns.len() as u8);
        // stack.push(ITER_ARITIES);
        let mut compound = Expr{ ptr: compound_vec.as_mut_ptr() };
        println!("cq {:?}", sexpr!(self, compound));
        stack.extend(referential_bidirectional_matching_stack(&mut ExprZipper::new(compound)));

        let mut references: Vec<(u32, u32)> = vec![];
        let mut candidate = 0;
        referential_transition(&mut stack, &mut prz, &mut references, &mut |loc| {
            let e = Expr { ptr: loc.origin_path().unwrap().as_ptr().cast_mut() };
            println!("{candidate} {:?}", sexpr!(self, e));
            candidate += 1;
        });
    }

    #[doc(hidden /* this should not be part of the public api, but it will stay here until we can factor it out, `main.rs` is still implicitly dependant on it inside the commented code */)]
    pub fn done(self) -> ! {
        // let counters = pathmap::counters::Counters::count_ocupancy(&self.btm);
        // counters.print_histogram_by_depth();
        // counters.print_run_length_histogram();
        // counters.print_list_node_stats();
        // println!("#symbols {}", self.sm.symbol_count());
        process::exit(0);
    }

    pub fn into_map(self) -> BytesTrieMap<()> {
        self.btm
    }
}
