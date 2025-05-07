use std::io::{BufRead, Read, Write};
use std::{mem, process, ptr};
use std::any::Any;
use std::fs::File;
use std::mem::MaybeUninit;
use std::ptr::{addr_of, null_mut};
use std::time::Instant;
use pathmap::ring::{AlgebraicStatus, Lattice};
use pathmap::zipper::{ProductZipper, ZipperSubtries};
use mork_bytestring::{byte_item, Expr, ExprZipper, ExtractFailure, item_byte, parse, serialize, Tag, traverseh};
use mork_frontend::bytestring_parser::{Parser, ParserError, Context};
use bucket_map::{WritePermit, SharedMapping, SharedMappingHandle};
use pathmap::trie_map::BytesTrieMap;
use pathmap::utils::{BitMask, ByteMask};
use pathmap::zipper::{ReadZipperUntracked, ZipperMoving, WriteZipperUntracked, Zipper, ZipperAbsolutePath, ZipperIteration, ZipperWriting, ZipperCreation};
use crate::json_parser::Transcriber;
use crate::prefix::Prefix;

use pathmap::{
    zipper::*,
};
pub use crate::space_temporary::{
    PathCount,
    NodeCount,
    AttributeCount,
    SExprCount,
};
pub struct Space {
    pub btm: BytesTrieMap<()>,
    pub sm: SharedMappingHandle
}

const SIZES: [u64; 4] = {
    use mork_bytestring::{item_byte, Tag};

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
    use mork_bytestring::{item_byte, Tag};

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
    use mork_bytestring::{item_byte, Tag};

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

const ITER_AT_DEPTH    : u8 =  0;
const ITER_SYMBOL_SIZE : u8 =  1;
const ITER_SYMBOLS     : u8 =  2;
const ITER_VARIABLES   : u8 =  3;
const ITER_ARITIES     : u8 =  4;
const ITER_EXPR        : u8 =  5;
const ITER_NESTED      : u8 =  6;
const ITER_SYMBOL      : u8 =  7;
const ITER_ARITY       : u8 =  8;
const ITER_VAR_SYMBOL  : u8 =  9;
const ITER_VAR_ARITY   : u8 = 10;
const ACTION           : u8 = 11;
const BEGIN_RANGE      : u8 = 12;
const FINALIZE_RANGE   : u8 = 13;
const REFER_RANGE      : u8 = 14;
#[allow(unused)]
const RESERVED         : u8 = 15;

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

#[allow(unused)]
fn show_stack<R:AsRef<[u8]>>(s: R) -> String {
    s.as_ref().iter().copied().map(label).reduce(|mut x, y| {
        x.push(' ');
        x.push_str(y.as_str());
        x
    }).unwrap()
}

fn referential_transition<Z : ZipperMoving + Zipper + ZipperAbsolutePath, F: FnMut(&[Expr], &mut Z) -> ()>(mut last: *mut u8, loc: &mut Z, references: &mut Vec<Expr>, f: &mut F) {
    unsafe {
    macro_rules! unroll {
    (ACTION $recursive:expr) => { f(&references[..], loc); };
    (ITER_AT_DEPTH $recursive:expr) => {
        let level = *last; last = last.offset(-1);

        let mut i = 0;
        while i < level {
            if loc.descend_first_byte() {
                i += 1
            } else if loc.to_next_sibling_byte() {
            } else if loc.ascend_byte() {
                i -= 1
            } else {
                i = 0;
                break
            }
        }

        while i > 0 {
            if i == level {
                referential_transition(last, loc, references, f);
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
                    assert!(loc.ascend_byte());
                    i -= 1;
                }
            }
        }

        last = last.offset(1); *last = level;
    };
    (ITER_NESTED $recursive:expr) => {
        let arity = *last; last = last.offset(-1);
        if arity == 0 {
          referential_transition(last, loc, references, f);
        } else {
            for _ in 0..arity-1 {
                last = last.offset(1);
                *last = ITER_EXPR;
            }
            unroll!(ITER_EXPR referential_transition(last, loc, references, f));

            last = last.offset(-(arity as isize - 1));
        }
        last = last.offset(1); *last = arity;
    };
    (ITER_SYMBOL_SIZE $recursive:expr) => {
        let m = loc.child_mask().and(&pathmap::utils::ByteMask(SIZES));
        let mut it = m.iter();

        while let Some(b) = it.next() {
            if let Tag::SymbolSize(s) = byte_item(b) {
                let buf = [b];
                if loc.descend_to(buf) {
                    let lastv = *last; last = last.offset(-1);
                    last = last.offset(1); *last = s;
                    last = last.offset(1); *last = lastv;
                    referential_transition(last, loc, references, f);
                    last = last.offset(-1);
                    last = last.offset(-1);
                    last = last.offset(1); *last = lastv;
                }
                loc.ascend(1);
            } else {
                unreachable!("no symbol size next")
            }
        }
    };
    (ITER_SYMBOLS $recursive:expr) => {
         last = last.offset(1); *last = ITER_AT_DEPTH;
         // last = last.offset(1); *last = ITER_SYMBOL_SIZE;
         unroll!(ITER_SYMBOL_SIZE $recursive);
         // last = last.offset(-1);
         last = last.offset(-1);
    };
    (ITER_VARIABLES $recursive:expr) => {
        let m = loc.child_mask().and(&ByteMask(VARS));
        let mut it = m.iter();

        while let Some(b) = it.next() {
            let buf = [b];
            if loc.descend_to(buf) {
                referential_transition(last, loc, references, f);
            }
            loc.ascend(1);
        }
    };
    (ITER_ARITIES $recursive:expr) => {
        let m = loc.child_mask().and(&ByteMask(ARITIES));
        let mut it = m.iter();

        while let Some(b) = it.next() {
            if let Tag::Arity(a) = byte_item(b) {
                let buf = [b];
                if loc.descend_to(buf) {
                    let lastv = *last; last = last.offset(-1);
                    last = last.offset(1); *last = a;
                    last = last.offset(1); *last = lastv;
                    referential_transition(last, loc, references, f);
                    last = last.offset(-1);
                    last = last.offset(-1);
                    last = last.offset(1); *last = lastv;
                }
                loc.ascend(1);
            } else {
                unreachable!()
            }
        }
    };
    (ITER_EXPR $recursive:expr) => {
        unroll!(ITER_VARIABLES $recursive);

        unroll!(ITER_SYMBOLS $recursive);

        last = last.offset(1); *last = ITER_NESTED;
        // last = last.offset(1); *last = ITER_ARITIES;
        unroll!(ITER_ARITIES $recursive);
        // last = last.offset(-1);
        last = last.offset(-1);
    };
    (ITER_SYMBOL $recursive:expr) => {
        let size = *last; last = last.offset(-1);
        let mut v = [0; 64];
        for i in 0..size { *v.get_unchecked_mut(i as usize) = *last; last = last.offset(-1); }

        if loc.descend_to_byte(item_byte(Tag::SymbolSize(size))) {
            if loc.descend_to(&v[..size as usize]) {
                $recursive;
            }
            loc.ascend(size as usize);
        }
        loc.ascend_byte();
        for i in 0..size { last = last.offset(1); *last = *v.get_unchecked((size - i - 1) as usize) }
        last = last.offset(1); *last = size;
    };
    (ITER_VAR_SYMBOL $recursive:expr) => {
        let size = *last; last = last.offset(-1);
        let mut v = [0; 64];
        for i in 0..size { *v.get_unchecked_mut(i as usize) = *last; last = last.offset(-1); }

        unroll!(ITER_VARIABLES $recursive);

        if loc.descend_to_byte(item_byte(Tag::SymbolSize(size))) {
            if loc.descend_to(&v[..size as usize]) {
                referential_transition(last, loc, references, f);
            }
            loc.ascend(size as usize);
        }
        loc.ascend_byte();
        for i in 0..size { last = last.offset(1); *last = *v.get_unchecked((size - i - 1) as usize) }
        last = last.offset(1); *last = size;
    };
    (ITER_ARITY $recursive:expr) => {
        let arity = *last; last = last.offset(-1);
        if loc.descend_to_byte(item_byte(Tag::Arity(arity))) {
            referential_transition(last, loc, references, f);
        }
        loc.ascend_byte();
        last = last.offset(1); *last = arity;
    };
    (ITER_VAR_ARITY $recursive:expr) => {
        let arity = *last; last = last.offset(-1);

        unroll!(ITER_VARIABLES $recursive);

        if loc.descend_to_byte(item_byte(Tag::Arity(arity))) {
            referential_transition(last, loc, references, f);
        }
        loc.ascend_byte();
        last = last.offset(1); *last = arity;
    };
    (BEGIN_RANGE $recursive:expr) => {
        // references.push((loc.path().len() as u32, 0));
        let p = loc.absolute_path();
        references.push(Expr { ptr: p.as_ptr().cast_mut().offset(p.len() as _) });
        $recursive;
        references.pop();
    };
    (FINALIZE_RANGE $recursive:expr) => {
        // references.last_mut().unwrap().1 = loc.path().len() as u32;
        $recursive;
        // references.last_mut().unwrap().1 = 0;
    };
    (REFER_RANGE $recursive:expr) => {
        let index = *last; last = last.offset(-1);
        let subexpr = references[index as usize];
        let mut ez = ExprZipper::new(subexpr);
        #[allow(unused_mut)]
        let mut v0 = last;
        loop {
            match ez.item() {
                Ok(Tag::NewVar) | Ok(Tag::VarRef(_)) => {
                    last = last.offset(1); *last = ITER_EXPR;
                }
                Ok(Tag::SymbolSize(_)) => { unreachable!() }
                Err(s) => {
                    last = last.offset(1); *last = ITER_VAR_SYMBOL;
                    last = last.offset(1); *last = s.len() as u8;
                    last = last.offset(1);
                    std::ptr::copy_nonoverlapping(s.as_ptr(), last, s.len());
                    last = last.offset((s.len() - 1) as isize);
                }
                Ok(Tag::Arity(a)) => {
                    last = last.offset(1); *last = ITER_VAR_ARITY;
                    last = last.offset(1); *last = a;
                }
            }
            if !ez.next() {
                let d = last.offset_from(v0) as usize;
                std::ptr::slice_from_raw_parts_mut(v0.offset(1), d).as_mut().unwrap_unchecked().reverse();
                break;
            }
        };

        $recursive;
        last = v0;

        last = last.offset(1); *last = index;
    };
    (DISPATCH $s:ident $recursive:expr) => {
        match $s {
            ITER_AT_DEPTH => { unroll!(ITER_AT_DEPTH $recursive); }
            ITER_SYMBOL_SIZE => { unroll!(ITER_SYMBOL_SIZE $recursive); }
            ITER_SYMBOLS => { unroll!(ITER_SYMBOLS $recursive); }
            ITER_VARIABLES => { unroll!(ITER_VARIABLES $recursive); }
            ITER_ARITIES => { unroll!(ITER_ARITIES $recursive); }
            ITER_EXPR => { unroll!(ITER_EXPR $recursive); }
            ITER_NESTED => { unroll!(ITER_NESTED $recursive); }
            ITER_SYMBOL => { unroll!(ITER_SYMBOL $recursive); }
            ITER_ARITY => { unroll!(ITER_ARITY $recursive); }
            ITER_VAR_SYMBOL => { unroll!(ITER_VAR_SYMBOL $recursive); }
            ITER_VAR_ARITY => { unroll!(ITER_VAR_ARITY $recursive); }
            ACTION => { unroll!(ACTION $recursive); }
            BEGIN_RANGE => { unroll!(BEGIN_RANGE $recursive); }
            FINALIZE_RANGE => { unroll!(FINALIZE_RANGE $recursive); }
            REFER_RANGE => { unroll!(REFER_RANGE $recursive); }
            RESERVED => { unreachable!("reserved opcode"); }
            c => { unreachable!("invalid opcode {}", c); }
        }
    };
    (CALL $recursive:expr) => {
        {
            let lastv = *last;
            last = last.offset(-1);
            unroll!(DISPATCH lastv $recursive);
            last = last.offset(1);
            *last = lastv;
        }
    };
    }
    // unroll!(CALL unroll!(CALL unroll!(CALL referential_transition(last, loc, references, f))));
    unroll!(CALL unroll!(CALL referential_transition(last, loc, references, f)));
    // unroll!(CALL referential_transition(last, loc, references, f));
    }
}


#[allow(unused_variables)]
fn referential_bidirectional_matching_stack_traverse(e: Expr, from: usize) -> Vec<u8> {
    let mut v = mork_bytestring::traverseh!((), (), (Vec<u8>, usize), e, (vec![], from),
        |(v, from): &mut (Vec<u8>, usize), o| {
            if o < *from { return }
            v.push(BEGIN_RANGE);
            v.push(ITER_EXPR);
            v.push(FINALIZE_RANGE);
        },
        |(v, from): &mut (Vec<u8>, usize), o, i| {
            if o < *from { return }
            v.push(REFER_RANGE);
            v.push(i);
        },
        |(v, from): &mut (Vec<u8>, usize), o, s: &[u8]| {
            if o < *from { return }
            v.push(ITER_VAR_SYMBOL);
            v.push(s.len() as u8);
            v.extend(s);
        },
        |(v, from): &mut (Vec<u8>, usize), o, a| {
            if o < *from { return }
            v.push(ITER_VAR_ARITY);
            v.push(a);
        },
        |v, o, r, s| {},
        |v, o, r| {}
    ).0.0;
    v.reverse();
    v
}

unsafe extern "C" {
    fn longjmp(env: &mut [u64; 64], status: i32);
    fn setjmp(env: &mut [u64; 64]) -> i32;
}

pub struct ParDataParser<'a> { count: u64,
    #[cfg(feature="interning")]
    buf: [u8; 8],
    #[cfg(not(feature="interning"))]
    buf: [u8; 64],
    #[cfg(not(feature="interning"))]
    truncated: u64,
    #[allow(dead_code)]
    write_permit: WritePermit<'a> }

impl <'a> Parser for ParDataParser<'a> {
    fn tokenizer<'r>(&mut self, s: &[u8]) -> &'r [u8] {
        self.count += 1;
        #[cfg(feature="interning")]
        {
        // FIXME hack until either the parser is rewritten or we can take a pointer of the symbol
        self.buf = self.write_permit.get_sym_or_insert(s);
        return unsafe { std::mem::transmute(&self.buf[..]) };
        }
        #[cfg(not(feature="interning"))]
        {
        let mut l = s.len();
        if l > 63 {
            self.truncated += 1;
            // panic!("len greater than 63 bytes {}", std::str::from_utf8(s).unwrap_or(format!("{:?}", s).as_str()))
            l = 63
        }
        self.buf[..l].clone_from_slice(&s[..l]);
        return unsafe { std::mem::transmute(&self.buf[..l]) };
        }
    }
}

impl <'a> ParDataParser<'a> {
    pub fn new(handle: &'a SharedMappingHandle) -> Self {
        Self {
            count: 3,
            #[cfg(feature="interning")]
            buf: (3u64).to_be_bytes(),
            #[cfg(not(feature="interning"))]
            buf: [0; 64],
            #[cfg(not(feature="interning"))]
            truncated: 0u64,
            write_permit: handle.try_aquire_permission().unwrap()
        }
    }
}


pub struct SpaceTranscriber<'a, 'c, WZ> { 
    /// count of unnested values == path_count
    path_count : PathCount, 
    wz         : &'c mut WZ,
    pdp        : ParDataParser<'a> }

impl <'a, 'c, WZ> SpaceTranscriber<'a, 'c, WZ> where WZ : Zipper + ZipperMoving + ZipperWriting<()> {
    #[inline(always)] fn write<S : Into<String>>(&mut self, s: S) {
        use mork_bytestring::{Tag, item_byte};

        let token = self.pdp.tokenizer(s.into().as_bytes());
        let mut path = vec![item_byte(Tag::SymbolSize(token.len() as u8))];
        path.extend(token);
        self.wz.descend_to(&path[..]);
        self.wz.set_value(());
        self.wz.ascend(path.len());
    }
}
impl <'a, 'c, WZ> crate::json_parser::Transcriber for SpaceTranscriber<'a, 'c, WZ> where WZ : Zipper + ZipperMoving + ZipperWriting<()> {
    #[inline(always)] fn descend_index(&mut self, i: usize, first: bool) -> () {
        use mork_bytestring::{Tag, item_byte};

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
        use mork_bytestring::{Tag, item_byte};

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
        let mut src = mork_bytestring::parse!($s);
        let q = mork_bytestring::Expr{ ptr: src.as_mut_ptr() };
        let table = $space.symbol_table();
        let mut pdp = $crate::space::ParDataParser::new(&table);
        let mut buf = [0u8; 2048];
        let p = mork_bytestring::Expr{ ptr: buf.as_mut_ptr() };
        let used = q.substitute_symbols(&mut mork_bytestring::ExprZipper::new(p), |x| <_ as mork_frontend::bytestring_parser::Parser>::tokenizer(&mut pdp, x));
        #[allow(unused_unsafe)]
        unsafe {
            let b = std::alloc::alloc(std::alloc::Layout::array::<u8>(used.len()).unwrap());
            std::ptr::copy_nonoverlapping(p.ptr, b, used.len());
            mork_bytestring::Expr{ ptr: b }
        }
    }};
}

#[macro_export]
macro_rules! sexpr {
    ($space:ident, $e:expr) => {{
        let mut v = vec![];
        let e: mork_bytestring::Expr = $e;
        e.serialize(&mut v, |s| {
            #[cfg(feature="interning")]
            {
            let symbol = i64::from_be_bytes(s.try_into().unwrap()).to_be_bytes();
            let table = $space.symbol_table();
            let mstr = table.get_bytes(symbol).map(unsafe { |x| std::str::from_utf8_unchecked(x) });
            // println!("symbol {symbol:?}, bytes {mstr:?}");
            unsafe { std::mem::transmute(mstr.expect(format!("failed to look up {:?}", symbol).as_str())) }
            }
            #[cfg(not(feature="interning"))]
            unsafe { std::mem::transmute(std::str::from_utf8(s).unwrap_or(format!("{:?}", s).as_str())) }
        });
        String::from_utf8(v).unwrap_or_else(|_| unsafe { e.span().as_ref()}.map(mork_bytestring::serialize).unwrap_or("<null>".to_string()))
    }};
}

#[macro_export]
macro_rules! prefix {
    ($space:ident, $s:literal) => {{
        let mut src = parse!($s);
        let q = Expr{ ptr: src.as_mut_ptr() };
        let mut pdp = $crate::space::ParDataParser::new(&$space.sm);
        let mut buf = [0u8; 2048];
        let p = Expr{ ptr: buf.as_mut_ptr() };
        let used = q.substitute_symbols(&mut ExprZipper::new(p), |x| pdp.tokenizer(x));
        let correction = 1; // hack to allow the re-use of substitute_symbols on something that's not a complete expression
        unsafe {
            let b = std::alloc::alloc(std::alloc::Layout::array::<u8>(used.len()-correction).unwrap());
            std::ptr::copy_nonoverlapping(p.ptr, b, used.len()-correction);
            crate::prefix::Prefix::<'static> { slice: std::ptr::slice_from_raw_parts(b, used.len()-correction).as_ref().unwrap() }
        }
    }};
}

impl Space {
    pub fn new() -> Self {
        Self { btm: BytesTrieMap::new(), sm: SharedMapping::new() }
    }

    /// Remy :I want to really discourage the use of this method, it needs to be exposed if we want to use the debugging macros `expr` and `sexpr` without giving access directly to the field
    ///       The name matches the name the Space trait so the macro expr works with it.
    #[doc(hidden)]
    pub fn symbol_table(&self)->SharedMappingHandle{
        self.sm.clone()
    }

    pub fn statistics(&self) {
        println!("val count {}", self.btm.val_count());
    }

    #[allow(unused)]
    fn write_zipper_unchecked<'a>(&'a self) -> WriteZipperUntracked<'a, 'a, ()> {
        unsafe { (&self.btm as *const BytesTrieMap<()>).cast_mut().as_mut().unwrap().write_zipper() }
    }

    fn write_zipper_at_unchecked<'a, 'b>(&'a self, path: &'b [u8]) -> WriteZipperUntracked<'a, 'b, ()> {
        unsafe { (&self.btm as *const BytesTrieMap<()>).cast_mut().as_mut().unwrap().write_zipper_at_path(path) }
    }

    pub fn load_csv(&mut self, r: &str, pattern: Expr, template: Expr) -> Result<usize, String> {
        load_csv_impl(&self.sm.clone(), r, pattern, template, self.write_zipper_at_unchecked(unsafe { &*template.prefix().unwrap_or(template.span()) })).map_err(|e| format!("{:?}",e))
    }
}
pub(crate) fn load_csv_impl<'s, WZ>(
    sm       : &SharedMappingHandle,
    r        : &str,
    pattern  : Expr,
    template : Expr,
    mut wz   : WZ,
) -> Result<crate::space::PathCount, ()>
    where
        WZ : Zipper + ZipperMoving + ZipperWriting<()> + 's
{
        let constant_template_prefix = unsafe { template.prefix().unwrap_or_else(|_| template.span()).as_ref().unwrap() };


        #[allow(unused_mut)]
        let mut buf = [0u8; 2048];

        let mut i = 0;
        let mut stack = [0u8; 2048];
        let mut pdp = ParDataParser::new(sm);
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

            let data = &stack[..total];
            let mut oz = ExprZipper::new(Expr{ ptr: buf.as_ptr().cast_mut() });
            match (Expr{ ptr: data.as_ptr().cast_mut() }.transformData(pattern, template, &mut oz)) {
                Ok(()) => {}
                Err(_e) => { continue }
            }
            let new_data = &buf[..oz.loc];
            wz.descend_to(&new_data[constant_template_prefix.len()..]);
            wz.set_value(());
            wz.reset();
            i += 1;
        }

        Ok(i)
}
impl Space {
    pub fn load_json(&mut self, r: &str) -> Result<PathCount, String> {
        load_json_impl(&self.sm, &mut self.btm.write_zipper(), r)
    }
}
pub(crate) fn load_json_impl<'s, WZ>(sm : &SharedMappingHandle, wz : &mut WZ, r: &str) -> Result<crate::space::PathCount, String> 
    where 
        WZ : Zipper + ZipperMoving + ZipperWriting<()>
{
    let mut st = SpaceTranscriber{ path_count: 0, wz, pdp: ParDataParser::new(sm) };
    let mut p = crate::json_parser::Parser::new(r);
    p.parse(&mut st).map_err(|e| format!("{e}"))?;
    Ok(st.path_count)
}
impl Space {
    #[cfg(feature="neo4j")]
    pub fn load_neo4j_triples(&mut self, uri: &str, user: &str, pass: &str) -> Result<PathCount, String> {
        let rt = tokio::runtime::Builder::new_current_thread()
          .enable_io()
          .build()
          .unwrap();
        load_neo4j_triples_impl(&self.sm, &mut self.btm.write_zipper(), &rt.handle(), uri, user, pass)
    }
}

#[cfg(feature="neo4j")]
pub(crate) fn load_neo4j_triples_impl<'s, WZ>(sm : &SharedMappingHandle, wz : &mut WZ, rt : &tokio::runtime::Handle, uri: &str, user: &str, pass: &str) -> Result<PathCount, String> 
    where
        WZ : Zipper + ZipperMoving + ZipperWriting<()>
{
        use neo4rs::*;

        let graph = Graph::new(uri, user, pass).unwrap();

        let mut pdp = ParDataParser::new(sm);

        let mut count = 0;

        let guard = rt.enter();
        let mut result = rt.block_on(graph.execute(
            query("MATCH (s)-[p]->(o) RETURN id(s), type(p), id(o)"))).unwrap();
        let spo_symbol = pdp.tokenizer("SPO".as_bytes());
        while let Ok(Some(row)) = rt.block_on(result.next()) {
            let s: i64 = row.get("id(s)").unwrap();
            let p: String = row.get("type(p)").unwrap();
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
                let internal = pdp.tokenizer(&p.as_bytes());
                ez.write_symbol(&internal[..]);
                ez.loc += internal.len() + 1;
            }
            {
                let internal = pdp.tokenizer(&o.to_be_bytes());
                ez.write_symbol(&internal[..]);
                ez.loc += internal.len() + 1;
            }
            // .insert(ez.span(), ()); // if only we had this function...
            wz.descend_to(ez.span());
            wz.set_value(());
            wz.reset();

            count += 1;
        }

        drop(guard);
        Ok(count)
}
impl Space {
    #[cfg(feature="neo4j")]
    pub fn load_neo4j_node_properties(&mut self, uri: &str, user: &str, pass: &str) -> Result<(NodeCount, AttributeCount), String> {
        let rt = tokio::runtime::Builder::new_current_thread()
          .enable_io()
          .build()
          .unwrap();
        load_neo4j_node_properties_impl(&self.sm, &mut self.btm.write_zipper(), &rt.handle(), uri, user, pass)
    }
}
#[cfg(feature="neo4j")]
pub(crate) fn load_neo4j_node_properties_impl<'s, WZ>(sm : &SharedMappingHandle, wz : &mut WZ, rt : &tokio::runtime::Handle, uri: &str, user: &str, pass: &str) -> Result<(NodeCount, AttributeCount), String> 
    where
        WZ : Zipper + ZipperMoving + ZipperWriting<()>
{
        use neo4rs::*;
        use mork_bytestring::{Tag, item_byte};
        let graph = Graph::new(uri, user, pass).unwrap();

        let mut pdp = ParDataParser::new(sm);
        let sa_symbol = pdp.tokenizer("NKV".as_bytes());
        let mut nodes = 0;
        let mut attributes = 0;

        wz.descend_to_byte(item_byte(Tag::Arity(4)));
        wz.descend_to_byte(item_byte(Tag::SymbolSize(sa_symbol.len() as _)));
        wz.descend_to(sa_symbol);

        let guard = rt.enter();
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
                if bv.value.starts_with("[") && bv.value.ends_with("]") {
                    for chunk in bv.value[1..bv.value.len()-1].split(", ") {
                        let c = if chunk.starts_with("\"") && chunk.ends_with("\"") { &chunk[1..chunk.len()-1] } else { chunk };
                        let internal_v = pdp.tokenizer(c.as_bytes());
                        wz.descend_to_byte(item_byte(Tag::SymbolSize(internal_v.len() as _)));
                        wz.descend_to(internal_v);

                        wz.set_value(());

                        wz.ascend(internal_v.len() + 1);
                    }
                } else {
                    let internal_v = pdp.tokenizer(bv.value.as_bytes());
                    wz.descend_to_byte(item_byte(Tag::SymbolSize(internal_v.len() as _)));
                    wz.descend_to(internal_v);

                    wz.set_value(());

                    wz.ascend(internal_v.len() + 1);
                }

                wz.ascend(internal_k.len() + 1);
                attributes += 1;
            }

            wz.ascend(internal_s.len() + 1);
            nodes += 1;
        }
        drop(guard);
        Ok((nodes, attributes))
}
impl Space {
    #[cfg(feature="neo4j")]
    pub fn load_neo4j_node_lables(&mut self, uri: &str, user: &str, pass: &str) -> Result<(NodeCount, AttributeCount), String> {
        let rt = tokio::runtime::Builder::new_current_thread()
          .enable_io()
          .build()
          .unwrap();
        load_neo4j_node_labels_impl(&self.sm, &mut self.btm.write_zipper(), &rt.handle(), uri, user, pass)
    }
}
#[cfg(feature="neo4j")]
pub fn load_neo4j_node_labels_impl<'s, WZ>(sm : &SharedMappingHandle, wz : &mut WZ, rt : &tokio::runtime::Handle, uri: &str, user: &str, pass: &str) -> Result<(usize, usize), String> 
    where
        WZ : Zipper + ZipperMoving + ZipperWriting<()>
{
        use neo4rs::*;
        use mork_bytestring::{Tag, item_byte};
        let graph = Graph::new(uri, user, pass).unwrap();

        let mut pdp = ParDataParser::new(&sm);
        let sa_symbol = pdp.tokenizer("NL".as_bytes());
        let mut nodes = 0;
        let mut labels = 0;

        wz.descend_to_byte(item_byte(Tag::Arity(3)));
        wz.descend_to_byte(item_byte(Tag::SymbolSize(sa_symbol.len() as _)));
        wz.descend_to(sa_symbol);

        let guard = rt.enter();
        let mut result = rt.block_on(graph.execute(
            query("MATCH (s) RETURN id(s), labels(s)"))
        ).unwrap();
        while let Ok(Some(row)) = rt.block_on(result.next()) {
            let s: i64 = row.get("id(s)").unwrap();
            let internal_s = pdp.tokenizer(&s.to_be_bytes());
            wz.descend_to_byte(item_byte(Tag::SymbolSize(internal_s.len() as _)));
            wz.descend_to(internal_s);

            let a: BoltList = row.get("labels(s)").unwrap();

            for bl in a.value.iter() {
                let BoltType::String(bv) = bl else { unreachable!() };

                let internal_v = pdp.tokenizer(bv.value.as_bytes());
                wz.descend_to_byte(item_byte(Tag::SymbolSize(internal_v.len() as _)));
                wz.descend_to(internal_v);

                wz.set_value(());

                wz.ascend(internal_v.len() + 1);

                labels += 1;
            }

            wz.ascend(internal_s.len() + 1);
            nodes += 1;
        }
        drop(guard);
        Ok((nodes, labels))
}
impl Space {
    pub fn load_sexpr(&mut self, r: &str, pattern: Expr, template: Expr) -> Result<SExprCount, String> {
        load_sexpr_impl(&self.sm, r, pattern, template, self.btm.write_zipper_at_path(unsafe { &*template.prefix().unwrap_or(template.span()) })).map_err(|e| format!("{:?}", e))
    }
}
pub(crate) fn load_sexpr_impl<'s, WZ>(
    sm       : &SharedMappingHandle,
    r        : &str,
    pattern  : Expr,
    template : Expr,
    mut wz   : WZ,
) -> Result<usize, ParserError>
where
        WZ : Zipper + ZipperMoving + ZipperWriting<()> /* + ZipperAbsolutePath */ + 's
{
        let constant_template_prefix = unsafe { template.prefix().unwrap_or_else(|_| template.span()).as_ref().unwrap() };
        // core::debug_assert_eq!(wz.origin_path().unwrap(), constant_template_prefix);

        #[allow(unused_mut)]
        let mut buffer = [0u8; 4096];
        let mut it = Context::new(r.as_bytes());
        let mut i = 0;
        let mut stack = [0u8; 2048];
        let mut parser = ParDataParser::new(sm);
        loop {
            let mut ez = ExprZipper::new(Expr{ptr: stack.as_mut_ptr()});
            match parser.sexpr(&mut it, &mut ez) {
                Ok(()) => {
                    let data = &stack[..ez.loc];
                    let mut oz = ExprZipper::new(Expr{ ptr: buffer.as_ptr().cast_mut() });
                    match (Expr{ ptr: data.as_ptr().cast_mut() }.transformData(pattern, template, &mut oz)) {
                        Ok(()) => {}
                        Err(_e) => { continue }
                    }
                    let new_data = &buffer[..oz.loc];
                    wz.descend_to(&new_data[constant_template_prefix.len()..]);
                    wz.set_value(());
                    wz.reset();
                }
                Err(ParserError::InputFinished) => { break }
                Err(other) => { return Err(other) }
            }
            i += 1;
            it.variables.clear();
        }
        Ok(i)
}
impl Space {
    pub fn dump_sexpr<W : Write>(&self, pattern: Expr, template: Expr, w: &mut W) -> Result<usize, String> {
        dump_as_sexpr_impl(
            &self.sm,
            pattern,
            self.btm.read_zipper_at_path(unsafe { pattern.prefix().unwrap_or_else(|_| pattern.span()).as_ref().unwrap() }),
            template,
            w, 
            || "IoWriteError"
        ).map_err(|e| format!("{:?}", e))
    }
}
pub(crate) fn dump_as_sexpr_impl<'s, RZ, W : std::io::Write, IoWriteError : Copy>(
    #[allow(unused_variables)]
    sm          : &SharedMapping,
    pattern     : Expr,
    pattern_rz  : RZ,
    template    : Expr,
    w           : &mut W,
    f           : impl Fn()->IoWriteError, 
) -> Result<usize, IoWriteError>
    where
    RZ : ZipperMoving + ZipperReadOnlySubtries<'s, ()> + ZipperAbsolutePath
{
        let mut buffer = [0u8; 4096];

        query_multi_impl(&[pattern], &[pattern_rz],|refs, _loc| {
            let mut oz = ExprZipper::new(Expr { ptr: buffer.as_mut_ptr() });
            template.substitute(refs, &mut oz);

            // &buffer[constant_template_prefix.len()..oz.loc]
            Expr{ ptr: buffer.as_ptr().cast_mut() }.serialize(w, |s| {
                #[cfg(feature="interning")]
                {
                    let symbol = i64::from_be_bytes(s.try_into().unwrap()).to_be_bytes();
                    let mstr = sm.get_bytes(symbol).map(unsafe { |x| std::str::from_utf8_unchecked(x) });
                    // println!("symbol {symbol:?}, bytes {mstr:?}");
                    unsafe { std::mem::transmute(mstr.expect(format!("failed to look up {:?}", symbol).as_str())) }
                }
                #[cfg(not(feature="interning"))]
                unsafe { std::mem::transmute(std::str::from_utf8(s).unwrap()) }
            });
            w.write(&[b'\n']).map_err(|_| f())?;

            Ok(())
        })
}
impl Space {
    pub fn backup_symbols<OutFilePath : AsRef<std::path::Path>>(&self, #[allow(unused_variables)]path: OutFilePath) -> Result<(), std::io::Error>  {
        #[cfg(feature="interning")]
        {
        self.sm.serialize(path)
        }
        #[cfg(not(feature="interning"))]
        {
        Ok(())
        }
    }

    pub fn restore_symbols(&mut self, #[allow(unused_variables)]path: impl AsRef<std::path::Path>) -> Result<(), std::io::Error> {
        #[cfg(feature="interning")]
        {
        self.sm = SharedMapping::deserialize(path)?;
        }
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

    pub fn backup_paths<OutDirPath : AsRef<std::path::Path>>(&self, path: OutDirPath) -> Result<pathmap::path_serialization::SerializationStats, std::io::Error> {
        let mut file = File::create(path).unwrap();
        pathmap::path_serialization::serialize_paths_(self.btm.read_zipper(), &mut file)
    }

    pub fn restore_paths<OutDirPath : AsRef<std::path::Path>>(&mut self, path: OutDirPath) -> Result<pathmap::path_serialization::DeserializationStats, std::io::Error> {
        let mut file = File::open(path).unwrap();
        pathmap::path_serialization::deserialize_paths(self.btm.write_zipper(), &mut file, |_, _| ())
    }


    pub fn query_multi<T : Copy, F : FnMut(&[Expr], Expr) -> Result<(), T>>(&self, patterns: &[Expr], effect: F) -> Result<usize, T> {
        let rzs = patterns.iter().map(
            |p| self.btm.read_zipper_at_path(unsafe { p.prefix().unwrap_or_else(|_| p.span()).as_ref().unwrap() })
        ).collect::<Vec<_>>();

        query_multi_impl(patterns,&rzs , effect)
    }
}
pub(crate) fn query_multi_impl<'s, RZ, E: Copy, F: FnMut(&[Expr], Expr) -> Result<(), E>>
(
    patterns    : &[Expr],
    pattern_rzs : &[RZ],
    mut effect  : F,
) -> Result<usize, E>
where
    RZ :  ZipperMoving + ZipperReadOnlySubtries<'s, ()> + ZipperAbsolutePath
{
        let make_prefix = |e:&Expr|  unsafe { e.prefix().unwrap_or_else(|_| e.span()).as_ref().unwrap() };

        core::debug_assert_eq!(patterns.len(), pattern_rzs.len());
        #[cfg(debug_assertions)]
        for i in 0..patterns.len() {
            core::debug_assert_eq!(
                make_prefix(&patterns[i]),
                pattern_rzs[i].absolute_path()
            );
        }

        //Graft all the remaining read zippers into temporary maps in order to work around the
        // fact that product zippers can't handle factor zippers beginning in the middle of nodes
        // Also, we need to preserve the original origin path
        //TODO: this can be simplified when prefix zippers can handle factors that start in the
        // middle of nodes and we have the ability to supply a prefix (origin) path on a product
        // zipper factor
        let mut tmp_maps = vec![];
        for each_rz in pattern_rzs {
            let mut btm = BytesTrieMap::new();
            let zh = btm.zipper_head();
            zh.write_zipper_at_exclusive_path(each_rz.absolute_path()).unwrap().graft(each_rz);
            drop(zh);
            tmp_maps.push(btm);
        }

        let [pat_0, pat_rest @ ..] = patterns            else { return Ok(0); };
        let [tmp_0, tmp_rest @ ..] = tmp_maps.as_slice() else { return Ok(0); };

        let mut prz = ProductZipper::new(
            tmp_0.read_zipper_at_path(make_prefix(pat_0)), 
            tmp_rest.iter().zip(pat_rest).map(|(tmp_m, p)| {
                tmp_m.read_zipper_at_path(make_prefix(p))
            }
        ));

        prz.reserve_path_buffer(4096);

        let mut stack = vec![0; 1];
        stack[0] = ACTION;

        for pattern in patterns.iter().rev() {
            let prefix = unsafe { pattern.prefix().unwrap_or_else(|_| pattern.span()).as_ref().unwrap() };
            stack.extend_from_slice(&referential_bidirectional_matching_stack_traverse(*pattern, prefix.len())[..]);
        }
        stack.reserve(4096);

        let mut references: Vec<Expr> = vec![];
        let mut candidate = 0;

        thread_local! {
            static BREAK: std::cell::RefCell<[u64; 64]> = const { std::cell::RefCell::new([0; 64]) };
            static RET: std::cell::Cell<*mut u8> = const { std::cell::Cell::new(std::ptr::null_mut()) };
        }
        BREAK.with_borrow_mut(|a| {
            if unsafe { setjmp(a) == 0 } {
                referential_transition(stack.last_mut().unwrap(), &mut prz, &mut references, &mut |refs, loc| {
                    let e = Expr { ptr: loc.absolute_path().as_ptr().cast_mut() };
                    match effect(refs, e) {
                        Ok(()) => {}
                        Err(t) => {
                            let t_ptr = unsafe { std::alloc::alloc(std::alloc::Layout::new::<E>()) };
                            unsafe { std::ptr::write(t_ptr as *mut E, t) };
                            RET.set(t_ptr);
                            unsafe { longjmp(a, 1) }
                        }
                    }
                    unsafe { std::ptr::write_volatile(&mut candidate, std::ptr::read_volatile(&candidate) + 1); }
                })
            }
        });
        RET.with(|mptr| {
            if mptr.get().is_null() { Ok(candidate) }
            else {
                #[allow(unused_unsafe)]
                let tref = unsafe { mptr.get() };
                let t = unsafe { std::ptr::read(tref as _) };
                unsafe { std::alloc::dealloc(tref, std::alloc::Layout::new::<E>()) };
                Err(t)
            }
        })
}

impl Space {
    pub fn transform_multi_multi(&mut self, patterns: &[Expr], templates: &[Expr]) -> (usize, bool) {

        let readers = patterns.iter().map(|e| 
            self.btm.read_zipper_at_path(unsafe { e.prefix().unwrap_or_else(|_| e.span()).as_ref().unwrap() })
        ).collect::<Vec<_>>();

        let template_prefixes: Vec<_> = templates.iter().map(|e| unsafe { e.prefix().unwrap_or_else(|_| e.span()).as_ref().unwrap() }).collect();
        let mut template_wzs: Vec<_> = template_prefixes.iter().map(|p| self.write_zipper_at_unchecked(p)).collect();


        transform_multi_multi_impl(patterns, &readers, templates, &template_prefixes, &mut template_wzs)
    }
}
pub(crate) fn transform_multi_multi_impl<'s, RZ, WZ>(
    patterns          : &[Expr],
    pattern_rzs       : &[RZ],
    templates         : &[Expr],
    template_prefixes : &[&[u8]],
    template_wzs      : &mut [WZ]
) -> (usize, bool)
    where
    RZ : ZipperMoving + ZipperReadOnlySubtries<'s, ()> + ZipperAbsolutePath,
    WZ : ZipperMoving + ZipperWriting<()>
{
        let mut buffer = [0u8; 512];

        let mut any_new = false;
        let touched = query_multi_impl(patterns, pattern_rzs, |refs, _loc| {
            for ((wz, prefix), template) in template_wzs.iter_mut().zip(template_prefixes).zip(templates) {
                let mut oz = ExprZipper::new(Expr { ptr: buffer.as_mut_ptr() });
                template.substitute(refs, &mut oz);
                wz.descend_to(&buffer[prefix.len()..oz.loc]);
                any_new = any_new || wz.set_value(()).is_none();
                wz.reset();
            }
            Result::<(),()>::Ok(())
        }).unwrap();
        (touched, any_new)
}

impl Space {
    pub fn transform_multi(&mut self, patterns: &[Expr], template: Expr) -> (usize, bool) {
        self.transform_multi_multi(patterns, &[template])
    }

    pub fn transform(&mut self, pattern: Expr, template: Expr) -> (usize, bool) {
        self.transform_multi_multi(&[pattern], &[template])
    }

    pub fn query<F : FnMut(&[Expr], Expr) -> ()>(&self, pattern: Expr, mut effect: F) {
        let _ = self.query_multi(&[pattern], |refs, e| { effect(refs, e); Ok::<(), ()>(()) } ).unwrap();
    }

    // (exec <loc> (, <src1> <src2> <srcn>)
    //             (, <dst1> <dst2> <dstm>))
    pub fn interpret(&mut self, rt: Expr) {
        let mut rtz = ExprZipper::new(rt);
        println!("interpreting {:?}", serialize(unsafe { rt.span().as_ref().unwrap() }));
        assert_eq!(rtz.item(), Ok(Tag::Arity(4)));
        assert!(rtz.next());
        assert_eq!(unsafe { rtz.subexpr().span().as_ref().unwrap() }, unsafe { expr!(self, "exec").span().as_ref().unwrap() });
        assert!(rtz.next());
        let loc = rtz.subexpr();

        assert!(rtz.next_child());
        let srcs = comma_fun_args(self, rtz.subexpr());

        assert!(rtz.next_child());
        let dsts = comma_fun_args(self, rtz.subexpr());

        self.transform_multi_multi(&srcs[..], &dsts[..]);
    }

    pub fn interpret_datalog(&mut self, rt: Expr) -> bool {
        let mut rtz = ExprZipper::new(rt);
        assert_eq!(rtz.item(), Ok(Tag::Arity(3)));
        assert!(rtz.next());
        assert_eq!(unsafe { rtz.subexpr().span().as_ref().unwrap() }, unsafe { expr!(self, "-:").span().as_ref().unwrap() });

        assert!(rtz.next_child());
        let dsts = comma_fun_args(self, rtz.subexpr());

        assert!(rtz.next_child());
        let mut res = rtz.subexpr();

        self.transform_multi(&dsts[..], res).1
    }

    pub fn datalog(&mut self, statements: &[Expr]) {
        let mut changed = true;
        while changed {
            changed = false;
            for statement in statements {
                changed |= self.interpret_datalog(*statement);
            }
        }
    }

    // pub fn datalog(&mut self, statements: &[Expr]) {
    //     let last_wrapped = vec![item_byte(Tag::Arity(2)), item_byte(Tag::SymbolSize(1)), 0];
    //     let current_wrapped = vec![item_byte(Tag::Arity(2)), item_byte(Tag::SymbolSize(1)), 1];
    //
    //     for statement in statements {
    //         let patterns = f(statement);
    //         let last_wrapped_patterns = patterns;
    //         let template = g(statement);
    //         let current_wrapped_template = template;
    //         self.transform_multi(last_wrapped_patterns, current_wrapped_template);
    //
    //     }
    //
    //     loop {
    //         match self.btm.write_zipper_at_path(&current_wrapped[..]).join_into(&mut self.btm.write_zipper_at_path(&last_wrapped[..])) {
    //             AlgebraicStatus::Element => {}
    //             AlgebraicStatus::Identity => { break }
    //             AlgebraicStatus::None => { panic!("zero") }
    //         }
    //     }
    // }

    pub fn metta_calculus(&mut self) {
        let prefix_e = expr!(self, "[4] exec $ $ $");
        let prefix = unsafe { prefix_e.prefix().unwrap().as_ref().unwrap() };

        loop {
            let mut rz = self.btm.read_zipper_at_borrowed_path(prefix);
            if !rz.to_next_val() { break }

            let mut x: Box<[u8]> = rz.absolute_path().into(); // should use local buffer
            drop(rz);
            self.btm.remove(&x[..]);
            self.interpret(Expr{ ptr: x.as_mut_ptr() });
        }
    }

    pub fn done(self) -> ! {
        // let counters = pathmap::counters::Counters::count_ocupancy(&self.btm);
        // counters.print_histogram_by_depth();
        // counters.print_run_length_histogram();
        // counters.print_list_node_stats();
        // println!("#symbols {}", self.sm.symbol_count());
        process::exit(0);
    }
}

fn comma_fun_args(s : &Space, e : Expr)->Vec<Expr> {
    let mut ez = ExprZipper::new(e);
    let Ok(Tag::Arity(n)) = ez.item() else { panic!() };
    let mut srcs = Vec::with_capacity(n as usize - 1);
    ez.next();
    assert_eq!(unsafe { ez.subexpr().span().as_ref().unwrap() }, unsafe { expr!(s, ",").span().as_ref().unwrap() });
    for i in 0..n as usize - 1 {
        ez.next_child();
        srcs.push(ez.subexpr());
    }
    srcs
}