use std::io::{BufRead, Read, Write};
use std::{mem, process, ptr};
use std::any::Any;
use std::collections::BTreeMap;
use std::fs::File;
use std::hint::unreachable_unchecked;
use std::mem::MaybeUninit;
use std::ops::{Coroutine, CoroutineState};
use std::pin::Pin;
use std::ptr::{addr_of, null, null_mut, slice_from_raw_parts, slice_from_raw_parts_mut};
use std::task::Poll;
use std::time::Instant;
use futures::StreamExt;
use pathmap::ring::{AlgebraicStatus, Lattice};
use mork_bytestring::{byte_item, Expr, ExprZipper, ExtractFailure, item_byte, parse, serialize, Tag, traverseh, ExprEnv, unify, UnificationFailure, apply};
use mork_frontend::bytestring_parser::{Parser, ParserError, Context};
use bucket_map::{WritePermit, SharedMapping, SharedMappingHandle};
use pathmap::trie_map::BytesTrieMap;
use pathmap::utils::{BitMask, ByteMask};
use pathmap::zipper::*;
use crate::json_parser::Transcriber;
use crate::prefix::Prefix;
use log::*;

pub static mut transitions: usize = 0;
pub static mut unifications: usize = 0;

pub struct Space {
    pub btm: BytesTrieMap<()>,
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


// future Adam: don't fall for the temptation of keeping references of data->pattern, you tried it twice already: it's not worth the complexity, it's incompatible due to the PZ de-Bruijn level non-well-foundedness, it doesn't occur in most queries, and the performance is not worth it
// others: this code has haphephobia, contact Adam when you run into problems
// optimization opportunities:
// - use u16 x u16 compressed byte mask to reduce stack size
// - decrease the size of ExprEnv; it's too rich for this function
// - symbol size can use more optimized descend at depth k implementation (PZ)
// - this function gets massive (many thousands of instructions) but can do with less checked functions
// - ascends may be avoided by using RZ refs instead of re-ascending in some cases
// - the adiabatic crate may be used to get rid of the recursion (though currently the recursion is significantly faster)
// - `references` can be elided by not putting the virtual $ Expr's on the `stack` such that _k maps directly to the indices
// - keeping a needle instead of a stack to avoid the `reverse` (would also create the opportunity to be even more lazy about instruction gen)
fn coreferential_transition<Z : ZipperMoving + Zipper + ZipperAbsolutePath + ZipperIteration, F: FnMut(&mut Z) -> ()>(
    loc: &mut Z, mut stack: &mut Vec<ExprEnv>, references: &mut Vec<u32>, f: &mut F) {
    unsafe {
    trace!(target: "coref trans", "loc {}    len {}", serialize(loc.path()), loc.path().len());
    trace!(target: "coref trans", "top {}", stack.last().map(|x| x.show()).unwrap_or_else(|| "empty".into()));
    unsafe { transitions += 1 };
    match stack.pop() {
        None => { f(loc) }
        Some(e) => {
            let e_byte = *e.base.ptr.add(e.offset as usize);

            macro_rules! vs {
                () => {{
                    let m = loc.child_mask().and(&ByteMask(VARS));
                    let mut it = m.iter();

                    while let Some(b) = it.next() {
                        if !loc.descend_to_byte(b) { unreachable_unchecked() };
                        coreferential_transition(loc, stack, references, f);
                        if !loc.ascend_byte() { unreachable_unchecked() };
                    }
                }};
            }

            match byte_item(e_byte) {
                Tag::NewVar => {
                    if e.n == 0 { references.push(loc.path().len() as u32); }
                    else {
                        trace!(target: "coref trans", "not putting {} {}", e.n, e.show());
                    }

                    vs!();

                    let m = loc.child_mask().and(&ByteMask(SIZES));
                    let mut it = m.iter();
                    while let Some(b) = it.next() {
                        let Tag::SymbolSize(size) = byte_item(b) else { unreachable_unchecked() };
                        if !loc.descend_to_byte(b) { unreachable_unchecked() }
                        if !loc.descend_first_k_path(size as _) { unreachable_unchecked() }
                        loop {
                            coreferential_transition(loc, stack, references, f);   
                            if !loc.to_next_k_path(size as _) { break }
                        }
                        if !loc.ascend_byte() { unreachable_unchecked() }
                    }

                    let m = loc.child_mask().and(&ByteMask(ARITIES));
                    let mut it = m.iter();
                    while let Some(b) = it.next() {
                        let Tag::Arity(a) = byte_item(b) else { unreachable_unchecked() };
                        if !loc.descend_to_byte(b) { unreachable_unchecked() };
                        static nv: u8 = item_byte(Tag::NewVar);
                        let ol = stack.len();
                        for _ in 0..a { stack.push(ExprEnv::new(255, Expr { ptr: ((&nv) as *const u8).cast_mut() })) }
                        coreferential_transition(loc, stack, references, f);
                        stack.truncate(ol);
                        if !loc.ascend_byte() { unreachable_unchecked() };
                    }

                    if e.n == 0 { references.pop(); }
                }
                Tag::VarRef(i) => {
                    // wrong addition v and n?
                    let addition = if e.n == 0 {
                        trace!(target: "coref trans", "varref {i} at {} pushing {}", references[i as usize], serialize(&loc.path()[references[i as usize] as usize..]));
                        trace!(target: "coref trans", "varref {i} {:?}", &loc.path()[references[i as usize] as usize..]);
                        ExprEnv{ n: 254, v: 0, offset: 0, base: Expr{ ptr: loc.path().as_ptr().cast_mut().offset(references[i as usize] as _) } }
                    } else {
                        trace!(target: "coref trans", "varref <{},{i}> 'any'", e.n);
                        static nv: u8 = item_byte(Tag::NewVar);
                        ExprEnv{ n: 255, v: 0, offset: 0, base: Expr{ ptr: ((&nv) as *const u8).cast_mut() } }
                    };
                    stack.push(addition);
                    vs!();
                    coreferential_transition(loc, stack, references, f);
                    stack.pop();
                }
                Tag::SymbolSize(size) => {
                    vs!();
                    if loc.descend_to_byte(e_byte) {
                        if loc.descend_to(&*slice_from_raw_parts(e.base.ptr.byte_add(e.offset as usize + 1), size as usize)) {
                            coreferential_transition(loc, stack, references, f);
                        }
                        loc.ascend(size as usize);
                    }
                    loc.ascend_byte();

                }
                Tag::Arity(arity) => {
                    vs!();
                    if loc.descend_to_byte(e_byte) {
                        let stackl = stack.len();
                        e.args(&mut stack);
                        stack[stackl..].reverse();
                        coreferential_transition(loc, stack, references, f);
                        stack.truncate(stack.len() - arity as usize);
                    }
                    loc.ascend_byte();
                }
            }

            stack.push(e);
        }
    }
    }
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
    write_permit: WritePermit<'a> }

impl <'a> Parser for ParDataParser<'a> {
    fn tokenizer<'r>(&mut self, s: &[u8]) -> &'r [u8] {
        self.count += 1;
        #[cfg(feature="interning")]
        {
        // FIXME hack until either the parser is rewritten or we can take a pointer of the symbol
        self.buf = (self.write_permit.get_sym_or_insert(s) );
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

pub struct SpaceTranscriber<'a, 'b, 'c> { count: usize, wz: &'c mut WriteZipperUntracked<'a, 'b, ()>, pdp: ParDataParser<'a> }
impl <'a, 'b, 'c> SpaceTranscriber<'a, 'b, 'c> {
    #[inline(always)] fn write<S : AsRef<[u8]>>(&mut self, s: S) {
        let token = self.pdp.tokenizer(s.as_ref());
        let mut path = vec![item_byte(Tag::SymbolSize(token.len() as u8))];
        path.extend(token);
        self.wz.descend_to(&path[..]);
        self.wz.set_val(());
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
    #[inline(always)] fn write_empty_array(&mut self) -> () { self.write("[]"); self.count += 1; }
    #[inline(always)] fn descend_key(&mut self, k: &str, first: bool) -> () {
        if first { self.wz.descend_to(&[item_byte(Tag::Arity(2))]); }
        let token = self.pdp.tokenizer(k.as_bytes());
        self.wz.descend_to(&[item_byte(Tag::SymbolSize(token.len() as u8))]);
        self.wz.descend_to(token);
    }
    #[inline(always)] fn ascend_key(&mut self, k: &str, last: bool) -> () {
        let token = self.pdp.tokenizer(k.as_bytes());
        self.wz.ascend(token.len() + 1);
        if last { self.wz.ascend(1); }
    }
    #[inline(always)] fn write_empty_object(&mut self) -> () { self.write("{}"); self.count += 1; }
    #[inline(always)] fn write_string(&mut self, s: &str) -> () { self.write(s); self.count += 1; }
    #[inline(always)] fn write_number(&mut self, negative: bool, mantissa: u64, exponent: i16) -> () {
        let mut s = String::new();
        if negative { s.push('-'); }
        s.push_str(mantissa.to_string().as_str());
        if exponent != 0 { s.push('e'); s.push_str(exponent.to_string().as_str()); }
        self.write(s);
        self.count += 1;
    }
    #[inline(always)] fn write_true(&mut self) -> () { self.write("true"); self.count += 1; }
    #[inline(always)] fn write_false(&mut self) -> () { self.write("false"); self.count += 1; }
    #[inline(always)] fn write_null(&mut self) -> () { self.write("null"); self.count += 1; }
    #[inline(always)] fn begin(&mut self) -> () {}
    #[inline(always)] fn end(&mut self) -> () {}
}

#[macro_export]
macro_rules! prefix {
    ($space:ident, $s:literal) => {{
        let mut src = parse!($s);
        let q = Expr{ ptr: src.as_mut_ptr() };
        let mut pdp = ParDataParser::new(&$space.sm);
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

#[macro_export]
macro_rules! expr {
    ($space:ident, $s:literal) => {{
        let mut src = mork_bytestring::parse!($s);
        let q = mork_bytestring::Expr{ ptr: src.as_mut_ptr() };
        let table = $space.sym_table();
        let mut pdp = $crate::space::ParDataParser::new(&table);
        let mut buf = [0u8; 4096];
        let p = mork_bytestring::Expr{ ptr: buf.as_mut_ptr() };
        let used = q.substitute_symbols(&mut mork_bytestring::ExprZipper::new(p), |x| <_ as mork_frontend::bytestring_parser::Parser>::tokenizer(&mut pdp, x));
        unsafe {
            let b = std::alloc::alloc(std::alloc::Layout::array::<u8>(used.len()).unwrap());
            std::ptr::copy_nonoverlapping(p.ptr, b, used.len());
            mork_bytestring::Expr{ ptr: b }
        }
    }};
    ($space:ident, $s:expr) => {{
        let mut src = mork_bytestring::parse::<4096>($s);
        let q = mork_bytestring::Expr{ ptr: src.as_mut_ptr() };
        let table = $space.sym_table();
        let mut pdp = $crate::space::ParDataParser::new(&table);
        let mut buf = [0u8; 4096];
        let p = mork_bytestring::Expr{ ptr: buf.as_mut_ptr() };
        let used = q.substitute_symbols(&mut mork_bytestring::ExprZipper::new(p), |x| <_ as mork_frontend::bytestring_parser::Parser>::tokenizer(&mut pdp, x));
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
            let mstr = $space.sym_table().get_bytes(symbol).map(unsafe { |x| std::str::from_utf8_unchecked(x) });
            // println!("symbol {symbol:?}, bytes {mstr:?}");
            unsafe { std::mem::transmute(mstr.expect(format!("failed to look up {:?}", symbol).as_str())) }
            }
            #[cfg(not(feature="interning"))]
            unsafe { std::mem::transmute(std::str::from_utf8(s).unwrap_or(format!("{:?}", s).as_str())) }
        });
        String::from_utf8(v).unwrap_or_else(|_| unsafe { e.span().as_ref()}.map(mork_bytestring::serialize).unwrap_or("<null>".to_string()))
    }};
}

impl Space {
    pub fn new() -> Self {
        Self { btm: BytesTrieMap::new(), sm: SharedMapping::new() }
    }

    /// Remy :I want to really discourage the use of this method, it needs to be exposed if we want to use the debugging macros `expr` and `sexpr` without giving acces directly to the field
    #[doc(hidden)]
    pub fn sym_table(&self)->SharedMappingHandle{
        self.sm.clone()
    }

    pub fn statistics(&self) {
        println!("val count {}", self.btm.val_count());
    }

    fn write_zipper_unchecked<'a>(&'a self) -> WriteZipperUntracked<'a, 'a, ()> {
        unsafe { (&self.btm as *const BytesTrieMap<()>).cast_mut().as_mut().unwrap().write_zipper() }
    }

    fn write_zipper_at_unchecked<'a, 'b>(&'a self, path: &'b [u8]) -> WriteZipperUntracked<'a, 'b, ()> {
        unsafe { (&self.btm as *const BytesTrieMap<()>).cast_mut().as_mut().unwrap().write_zipper_at_path(path) }
    }

    /*
        pub fn load_csv<R : Read>(&mut self, prefix: Prefix, mut r: R, sm: &mut SymbolMapping, separator: u8) -> Result<usize, String> {
        let mut i = 0;
        let mut buf = vec![];
        let mut stack = [0u8; 2048];

        match r.read_to_end(&mut buf) {
            Ok(read) => {
                let mut wz = self.btm.write_zipper_at_path(prefix.path());
                for sv in buf.split(|&x| x == b'\n') {
                    if sv.len() == 0 { continue }
                    let mut a = 0;
                    let e = Expr{ ptr: stack.as_mut_ptr() };
                    let mut ez = ExprZipper::new(e);
                    ez.loc += 1;
                    let rown = sm.tokenizer(unsafe { String::from_utf8_unchecked(i.to_string().into_bytes()) });
                    ez.write_symbol(&rown[..]);
                    ez.loc += rown.len() + 1;
                    a += 1;
                    for symbol in sv.split(|&x| x == separator) {
                        let internal = sm.tokenizer(unsafe { String::from_utf8_unchecked(symbol.to_vec()) });
                        ez.write_symbol(&internal[..]);
                        ez.loc += internal.len() + 1;
                        a += 1;
                    }
                    let total = ez.loc;
                    ez.reset();
                    ez.write_arity(a);
                    wz.descend_to(&stack[..total]);
                    wz.set_value(());
                    wz.reset();
                    i += 1;
                }
            }
            Err(e) => { return Err(format!("{:?}", e)) }
        }

        Ok(i)
    }
     */


    pub fn load_csv(&mut self, r: &[u8], pattern: Expr, template: Expr, seperator: u8) -> Result<usize, String> {
        let constant_template_prefix = unsafe { template.prefix().unwrap_or_else(|_| template.span()).as_ref().unwrap() };
        let mut wz = self.write_zipper_at_unchecked(constant_template_prefix);
        let mut buf = [0u8; 2048];

        let mut i = 0usize;
        let mut stack = [0u8; 2048];
        let mut pdp = ParDataParser::new(&self.sm);
        for sv in r.split(|&x| x == b'\n') {
            if sv.len() == 0 { continue }
            let mut a = 0;
            let e = Expr{ ptr: stack.as_mut_ptr() };
            let mut ez = ExprZipper::new(e);
            ez.loc += 1;
            let num = pdp.tokenizer(i.to_string().as_bytes());
            // ez.write_symbol(i.to_be_bytes().as_slice());
            ez.write_symbol(num);
            // ez.loc += 9;
            ez.loc += num.len() + 1;

            for symbol in sv.split(|&x| x == seperator) {
                let internal = pdp.tokenizer(symbol);
                ez.write_symbol(&internal[..]);
                ez.loc += internal.len() + 1;
                a += 1;
            }
            let total = ez.loc;
            ez.reset();
            ez.write_arity(a + 1);

            let data = &stack[..total];
            let mut oz = ExprZipper::new(Expr{ ptr: buf.as_ptr().cast_mut() });
            match (Expr{ ptr: data.as_ptr().cast_mut() }.transformData(pattern, template, &mut oz)) {
                Ok(()) => {}
                Err(e) => { continue }
            }
            let new_data = &buf[..oz.loc];
            wz.descend_to(&new_data[constant_template_prefix.len()..]);
            wz.set_value(());
            wz.reset();
            i += 1;
        }

        Ok(i)
    }

    pub fn load_json(&mut self, r: &[u8]) -> Result<usize, String> {
        let mut wz = self.write_zipper_unchecked();
        let mut st = SpaceTranscriber{ count: 0, wz: &mut wz, pdp: ParDataParser::new(&self.sm) };
        let mut p = crate::json_parser::Parser::new(unsafe { std::str::from_utf8_unchecked(r) });
        p.parse(&mut st).unwrap();
        Ok(st.count)
    }

    #[cfg(all(feature = "nightly"))]
    pub fn json_to_paths<W : std::io::Write>(&mut self, r: &[u8], d: &mut W) -> Result<usize, String> {
        pub struct ASpaceTranscriber<'a, 'c> { count: usize, wz: &'c mut Vec<u8>, pdp: ParDataParser<'a> }
        impl <'a, 'c> ASpaceTranscriber<'a, 'c> {
            #[inline(always)] fn write<S : AsRef<[u8]>>(&mut self, s: S) -> impl Iterator<Item=&'static [u8]> {
                gen move {
                let token = self.pdp.tokenizer(s.as_ref());
                self.wz.push(item_byte(Tag::SymbolSize(token.len() as u8)));
                self.wz.extend_from_slice(token);
                yield unsafe { std::mem::transmute(&self.wz[..]) };
                self.wz.truncate(self.wz.len() - (token.len() + 1));
                }
            }
        }
        impl <'a, 'c> crate::json_parser::ATranscriber<&'static [u8]> for ASpaceTranscriber<'a, 'c> {
            #[inline(always)] fn descend_index(&mut self, i: usize, first: bool) -> () {
                if first { self.wz.push(item_byte(Tag::Arity(2))); }
                let token = self.pdp.tokenizer(i.to_string().as_bytes());
                self.wz.push(item_byte(Tag::SymbolSize(token.len() as u8)));
                self.wz.extend_from_slice(token);
            }
            #[inline(always)] fn ascend_index(&mut self, i: usize, last: bool) -> () {
                self.wz.truncate(self.wz.len() - (self.pdp.tokenizer(i.to_string().as_bytes()).len() + 1));
                if last { self.wz.truncate(self.wz.len() - 1); }
            }
            #[inline(always)] fn write_empty_array(&mut self) -> impl Iterator<Item=&'static [u8]> { self.count += 1; self.write("[]") }
            #[inline(always)] fn descend_key(&mut self, k: &str, first: bool) -> () {
                if first { self.wz.push(item_byte(Tag::Arity(2))); }
                let token = self.pdp.tokenizer(k.as_bytes());
                self.wz.push(item_byte(Tag::SymbolSize(token.len() as u8)));
                self.wz.extend_from_slice(token);
            }
            #[inline(always)] fn ascend_key(&mut self, k: &str, last: bool) -> () {
                let token = self.pdp.tokenizer(k.as_bytes());
                self.wz.truncate(self.wz.len() - (token.len() + 1));
                if last { self.wz.truncate(self.wz.len() - 1); }
            }
            #[inline(always)] fn write_empty_object(&mut self) -> impl Iterator<Item=&'static [u8]> { self.count += 1; self.write("{}") }
            #[inline(always)] fn write_string(&mut self, s: &str) -> impl Iterator<Item=&'static [u8]> { self.count += 1; self.write(s) }
            #[inline(always)] fn write_number(&mut self, negative: bool, mantissa: u64, exponent: i16) -> impl Iterator<Item=&'static [u8]> {
                let mut buf = [0u8; 64];
                let mut cur = std::io::Cursor::new(&mut buf[..]);
                if negative { write!(cur, "-").unwrap(); }
                write!(cur, "{}", mantissa).unwrap();
                if exponent != 0 { write!(cur, "e{}", exponent).unwrap(); }
                let len = cur.position() as usize;
                self.count += 1;
                self.write(unsafe { std::mem::transmute::<_, &'static [u8]>(&cur.into_inner()[..len]) })
            }
            #[inline(always)] fn write_true(&mut self) -> impl Iterator<Item=&'static [u8]> { self.count += 1; self.write("true") }
            #[inline(always)] fn write_false(&mut self) -> impl Iterator<Item=&'static [u8]> { self.count += 1; self.write("false") }
            #[inline(always)] fn write_null(&mut self) -> impl Iterator<Item=&'static [u8]> { self.count += 1; self.write("null") }
            #[inline(always)] fn begin(&mut self) -> () {}
            #[inline(always)] fn end(&mut self) -> () {}
        }

        let mut sink = pathmap::paths_serialization::paths_serialization_sink(d);

        let mut wz = Vec::with_capacity(4096);
        let mut st = ASpaceTranscriber{ count: 0, wz: &mut wz, pdp: ParDataParser::new(&self.sm) };

        let mut p = crate::json_parser::Parser::new(unsafe { std::str::from_utf8_unchecked(r) });
        let mut coro = p.parse_stream(&mut st);
        while let CoroutineState::Yielded(n) = Pin::new(&mut coro).resume(()) {
            Pin::new(&mut sink).resume(Some(n));
        }
        match Pin::new(&mut sink).resume(None) {
            CoroutineState::Yielded(_) => { panic!() }
            CoroutineState::Complete(summary) => { println!("{:?}", summary) }
        }
        drop(coro);
        Ok(st.count)
    }

    pub fn load_jsonl(&mut self, r: &[u8]) -> Result<(usize, usize), String> {
        let mut wz = self.write_zipper_unchecked();
        let mut lines = 0usize;
        let mut count = 0usize;
        let mut pdp = ParDataParser::new(&self.sm);
        let spo_symbol = pdp.tokenizer("JSONL".as_bytes());
        let mut path = vec![item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(spo_symbol.len() as u8))];
        path.extend_from_slice(spo_symbol);
        wz.descend_to(&path[..]);
        for line in unsafe { std::str::from_utf8_unchecked(r).lines() } {
            wz.descend_to(lines.to_be_bytes());
            let mut st = SpaceTranscriber{ count: 0, wz: &mut wz, pdp: ParDataParser::new(&self.sm) };
            let mut p = crate::json_parser::Parser::new(line);
            p.parse(&mut st).unwrap();
            count += st.count;
            lines += 1;
            wz.ascend(8);
            if lines > 0 && lines % 1000_000 == 0 {
                println!("parsed {} JSON lines ({} paths)", lines, count);
            }
        }
        Ok((lines, count))
    }

    pub fn load_jsonl_par(&mut self, r: &[u8]) -> Result<(usize, usize), String> {
        let mut wz = self.write_zipper_unchecked();
        let mut lines = 0usize;
        let mut count = 0usize;
        let mut pdp = ParDataParser::new(&self.sm);
        let spo_symbol = pdp.tokenizer("JSONL".as_bytes());
        let mut path = vec![item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(spo_symbol.len() as u8))];
        path.extend_from_slice(spo_symbol);
        wz.descend_to(&path[..]);
        for line in unsafe { std::str::from_utf8_unchecked(r).lines() } {
            wz.descend_to(lines.to_be_bytes());
            let mut st = SpaceTranscriber{ count: 0, wz: &mut wz, pdp: ParDataParser::new(&self.sm) };
            let mut p = crate::json_parser::Parser::new(line);
            p.parse(&mut st).unwrap();
            count += st.count;
            lines += 1;
            wz.ascend(8);
            if lines > 0 && lines % 1000_000 == 0 {
                println!("parsed {} JSON lines ({} paths)", lines, count);
            }
        }
        Ok((lines, count))
    }

    pub fn load_json_(&mut self, r: &[u8], pattern: Expr, template: Expr) -> Result<usize, String> {
        let constant_template_prefix = unsafe { template.prefix().unwrap_or_else(|_| template.span()).as_ref().unwrap() };
        let mut wz = self.write_zipper_at_unchecked(constant_template_prefix);

        let mut st = SpaceTranscriber{ count: 0, wz: &mut wz, pdp: ParDataParser::new(&self.sm) };
        let mut p = crate::json_parser::Parser::new(unsafe { std::str::from_utf8_unchecked(r) });
        p.parse(&mut st).unwrap();
        Ok(st.count)
    }

    #[cfg(feature="neo4j")]
    pub fn load_neo4j_triples(&mut self, uri: &str, user: &str, pass: &str) -> Result<usize, String> {
        use neo4rs::*;
        let graph = Graph::new(uri, user, pass).unwrap();

        let rt = tokio::runtime::Builder::new_current_thread()
          .enable_io()
          // .unhandled_panic(tokio::runtime::UnhandledPanic::Ignore)
          .build()
          .unwrap();
        let mut pdp = ParDataParser::new(&self.sm);

        let mut count = 0;

        let mut result = rt.block_on(graph.execute(
            query("MATCH (s)-[p]->(o) RETURN id(s), type(p), id(o)"))).unwrap();
        let spo_symbol = pdp.tokenizer("SPO".as_bytes()).to_vec();
        while let Ok(Some(row)) = rt.block_on(result.next()) {
            let s: i64 = row.get("id(s)").unwrap();
            let p: String = row.get("type(p)").unwrap();
            let o: i64 = row.get("id(o)").unwrap();
            // std::hint::black_box((s, p, o));
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
                let internal = pdp.tokenizer(p.as_bytes());
                ez.write_symbol(&internal[..]);
                ez.loc += internal.len() + 1;
            }
            {
                let internal = pdp.tokenizer(&o.to_be_bytes());
                ez.write_symbol(&internal[..]);
                ez.loc += internal.len() + 1;
            }
            // println!("{}", serialize(ez.span()));
            unsafe { self.btm.insert(ez.span(), ()); }
            count += 1;
            if count % 1000000 == 0 {
                println!("{count} triples");
            }
        }
        Ok(count)
    }

    #[cfg(feature="neo4j")]
    pub fn load_neo4j_node_properties(&mut self, uri: &str, user: &str, pass: &str) -> Result<(usize, usize), String> {
        use neo4rs::*;
        let graph = Graph::new(uri, user, pass).unwrap();

        let rt = tokio::runtime::Builder::new_current_thread()
          .enable_io()
          // .unhandled_panic(tokio::runtime::UnhandledPanic::Ignore)
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
            if nodes % 1000000 == 0 {
                println!("{attributes} attributes of {nodes}");
            }
        }
        Ok((nodes, attributes))
    }

    #[cfg(feature="neo4j")]
    pub fn load_neo4j_node_labels(&mut self, uri: &str, user: &str, pass: &str) -> Result<(usize, usize), String> {
        use neo4rs::*;
        let graph = Graph::new(uri, user, pass).unwrap();

        let rt = tokio::runtime::Builder::new_current_thread()
          .enable_io()
          // .unhandled_panic(tokio::runtime::UnhandledPanic::Ignore)
          .build()
          .unwrap();
        let mut pdp = ParDataParser::new(&self.sm);
        let zh = self.btm.zipper_head();
        let mut wz = zh.write_zipper_at_exclusive_path(&[]).unwrap();
        let sa_symbol = pdp.tokenizer("NL".as_bytes());
        let mut nodes = 0;
        let mut labels = 0;

        wz.descend_to_byte(item_byte(Tag::Arity(3)));
        wz.descend_to_byte(item_byte(Tag::SymbolSize(sa_symbol.len() as _)));
        wz.descend_to(sa_symbol);

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
            if nodes % 1000000 == 0 {
                println!("{labels} labels of {nodes}");
            }
        }
        Ok((nodes, labels))
    }

    pub fn load_all_sexpr(&mut self, r: &[u8]) -> Result<usize, String> {
        let mut stack = Vec::with_capacity(1 << 32);
        unsafe { stack.set_len(1 << 32); }
        let mut it = Context::new(r);
        let mut i = 0;
        let mut parser = ParDataParser::new(&self.sm);
        loop {
            let mut ez = ExprZipper::new(Expr{ptr: stack.as_mut_ptr()});
            match parser.sexpr(&mut it, &mut ez) {
                Ok(()) => {
                    let data = &stack[..ez.loc];
                    self.btm.insert(data, ());
                }
                Err(ParserError::InputFinished) => { break }
                Err(other) => { panic!("{:?}", other) }
            }
            i += 1;
            it.variables.clear();
        }
        Ok(i)
    }

    pub fn load_sexpr(&mut self, r: &[u8], pattern: Expr, template: Expr) -> Result<usize, String> {
        let constant_template_prefix = unsafe { template.prefix().unwrap_or_else(|_| template.span()).as_ref().unwrap() };
        let mut wz = self.write_zipper_at_unchecked(constant_template_prefix);
        let mut buffer: Vec<u8> = Vec::with_capacity(1 << 32);
        unsafe { buffer.set_len(1 << 32); }
        let mut stack = Vec::with_capacity(1 << 32);
        unsafe { stack.set_len(1 << 32); }
        let mut it = Context::new(r);
        let mut i = 0;
        let mut parser = ParDataParser::new(&self.sm);
        loop {
            let mut ez = ExprZipper::new(Expr{ptr: stack.as_mut_ptr()});
            match parser.sexpr(&mut it, &mut ez) {
                Ok(()) => {
                    let data = &stack[..ez.loc];
                    let mut oz = ExprZipper::new(Expr{ ptr: buffer.as_ptr().cast_mut() });
                    match (Expr{ ptr: data.as_ptr().cast_mut() }.transformData(pattern, template, &mut oz)) {
                        Ok(()) => {}
                        Err(e) => { continue }
                    }
                    let new_data = &buffer[..oz.loc];
                    wz.descend_to(&new_data[constant_template_prefix.len()..]);
                    wz.set_value(());
                    wz.reset();
                }
                Err(ParserError::InputFinished) => { break }
                Err(other) => { panic!("{:?}", other) }
            }
            i += 1;
            it.variables.clear();
        }
        Ok(i)
    }

    pub fn dump_all_sexpr<W : Write>(&self, w: &mut W) -> Result<usize, String> {
        let mut rz = self.btm.read_zipper();
        let mut i = 0usize;
        while rz.to_next_val() {
            Expr{ ptr: rz.path().as_ptr().cast_mut() }.serialize2(w, |s| {
                #[cfg(feature="interning")]
                {
                    let symbol = i64::from_be_bytes(s.try_into().unwrap()).to_be_bytes();
                    let mstr = self.sm.get_bytes(symbol).map(unsafe { |x| std::str::from_utf8_unchecked(x) });
                    // println!("symbol {symbol:?}, bytes {mstr:?}");
                    unsafe { std::mem::transmute(mstr.expect(format!("failed to look up {:?}", symbol).as_str())) }
                }
                #[cfg(not(feature="interning"))]
                unsafe { std::mem::transmute(std::str::from_utf8(s).unwrap()) }
            }, |i, intro| { Expr::VARNAMES[i as usize] });
            // w.write(serialize(rz.path()).as_bytes());
            w.write(&[b'\n']).map_err(|x| x.to_string())?;
            i += 1;
        }
        Ok(i)
    }

    pub fn dump_sexpr<W : Write>(&self, pattern: Expr, template: Expr, w: &mut W) -> usize {
        let constant_template_prefix = unsafe { template.prefix().unwrap_or_else(|_| template.span()).as_ref().unwrap() };

        let mut buffer = [0u8; 4096];
        let mut pat = vec![item_byte(Tag::Arity(2)), item_byte(Tag::SymbolSize(1)), b','];
        pat.extend_from_slice(unsafe { pattern.span().as_ref().unwrap() });

        Self::query_multi(&self.btm, Expr{ ptr: pat.leak().as_mut_ptr() }, |refs_bindings, loc| {
            let mut oz = ExprZipper::new(Expr { ptr: buffer.as_mut_ptr() });

            match refs_bindings {
                Ok(refs) => {
                    // todo
                    // template.substitute(&refs.iter().map(|ee| ee.subsexpr()).collect::<Vec<_>>()[..], &mut oz);
                }
                Err((ref bindings, ti, ni, _)) => {
                    mork_bytestring::apply(0, ni as u8, ti as u8, &mut ExprZipper::new(template), bindings, &mut oz, &mut BTreeMap::new(), &mut vec![], &mut vec![]);
                }
            }

            // &buffer[constant_template_prefix.len()..oz.loc]
            Expr{ ptr: buffer.as_ptr().cast_mut() }.serialize2(w, |s| {
                #[cfg(feature="interning")]
                {
                    let symbol = i64::from_be_bytes(s.try_into().unwrap()).to_be_bytes();
                    let mstr = self.sm.get_bytes(symbol).map(unsafe { |x| std::str::from_utf8_unchecked(x) });
                    // println!("symbol {symbol:?}, bytes {mstr:?}");
                    unsafe { std::mem::transmute(mstr.expect(format!("failed to look up {:?}", symbol).as_str())) }
                }
                #[cfg(not(feature="interning"))]
                unsafe { std::mem::transmute(std::str::from_utf8(s).unwrap()) }
            }, |i, intro| { Expr::VARNAMES[i as usize] });
            w.write(&[b'\n']).map_err(|x| x.to_string()).unwrap();

            true
        })
    }

    pub fn backup_symbols<out_dir_path : AsRef<std::path::Path>>(&self, path: out_dir_path) -> Result<(), std::io::Error>  {
        #[cfg(feature="interning")]
        {
        self.sm.serialize(path)
        }
        #[cfg(not(feature="interning"))]
        {
        Ok(())
        }
    }

    pub fn restore_symbols(&mut self, path: impl AsRef<std::path::Path>) -> Result<(), std::io::Error> {
        #[cfg(feature="interning")]
        {
        self.sm = SharedMapping::deserialize(path)?;
        }
        Ok(())
    }

    pub fn backup<OutDirPath : AsRef<std::path::Path>>(&self, path: OutDirPath) -> Result<(), std::io::Error> {
        pathmap::serialization::write_trie("neo4j triples", self.btm.read_zipper(),
                                           |v, b| pathmap::serialization::ValueSlice::Read(&[]),
                                           path.as_ref()).map(|_| ())
    }

    pub fn restore(&mut self, path: impl AsRef<std::path::Path>) -> Result<(), std::io::Error> {
        self.btm = pathmap::serialization::deserialize_file(path, |_| ())?;
        Ok(())
    }

    pub fn backup_tree<OutDirPath : AsRef<std::path::Path>>(&self, path: OutDirPath) -> Result<(), std::io::Error> {
        pathmap::arena_compact::ArenaCompactTree::dump_from_zipper(
            self.btm.read_zipper(), |_v| 0, path).map(|_tree| ())
    }

    pub fn restore_tree(&mut self, path: impl AsRef<std::path::Path>) -> Result<(), std::io::Error> {
        let tree = pathmap::arena_compact::ArenaCompactTree::open_mmap(path)?;
        let mut rz = tree.read_zipper();
        while rz.to_next_val() {
            self.btm.insert(rz.path(), ());
        }
        Ok(())
    }

    pub fn backup_paths<OutDirPath: AsRef<std::path::Path>>(&self, path: OutDirPath) -> Result<pathmap::paths_serialization::SerializationStats, std::io::Error> {
        let mut file = File::create(path).unwrap();
        pathmap::paths_serialization::serialize_paths(self.btm.read_zipper(), &mut file)
    }

    pub fn restore_paths<OutDirPath : AsRef<std::path::Path>>(&mut self, path: OutDirPath) -> Result<pathmap::paths_serialization::DeserializationStats, std::io::Error> {
        let mut file = File::open(path).unwrap();
        pathmap::paths_serialization::deserialize_paths(self.btm.write_zipper(), &mut file, ())
    }

    pub fn query_multi<F : FnMut(Result<&[u32], (BTreeMap<(u8, u8), ExprEnv>, u8, u8, &[(u8, u8)])>, Expr) -> bool>(btm: &BytesTrieMap<()>, pat_expr: Expr, mut effect: F) -> usize {
        let pat_newvars = pat_expr.newvars();
        trace!(target: "query_multi", "pattern (newvars={}) {:?}", pat_newvars, serialize(unsafe { pat_expr.span().as_ref().unwrap() }));
        let mut pat_args = vec![];
        ExprEnv::new(0, pat_expr).args(&mut pat_args);

        if pat_args.len() <= 1 { return 0 }

        let mut rz = btm.read_zipper();
        // SWAP!!!
        let mut prz = ProductZipperG::new(rz, (0..(pat_args.len() - 2)).map(|i| {
            btm.read_zipper()
        }));
        prz.reserve_buffers(1 << 32, 32);

        let mut stack = pat_args[1..].iter().rev().cloned().collect::<Vec<_>>();

        let mut scratch = Vec::with_capacity(1 << 32);

        let mut assignments: Vec<(u8, u8)> = vec![];
        let mut trace: Vec<(u8, u8)> = vec![];
        let mut references: Vec<u32> = vec![];
        let mut candidate = 0;
        thread_local! {
            static BREAK: std::cell::RefCell<[u64; 64]> = const { std::cell::RefCell::new([0; 64]) };
        }

        BREAK.with_borrow_mut(|a| {
            if unsafe { setjmp(a) == 0 } {
                coreferential_transition(&mut prz, &mut stack, unsafe { ((&references) as *const Vec<u32>).cast_mut().as_mut().unwrap() },&mut |loc| {
                    let e = Expr { ptr: loc.origin_path().as_ptr().cast_mut() };
                    trace!(target: "query_multi", "pi {:?}", loc.path_indices());
                    trace!(target: "query_multi", "at {:?}", e);
                    for &other_i in loc.path_indices() {
                        trace!(target: "query_multi", "at {:?}",
                            Expr { ptr: unsafe { loc.origin_path().as_ptr().cast_mut().add(other_i) } });
                    }

                    // if e.variables() != 0 {
                    if true {
                        let mut pairs = vec![(pat_args[1], ExprEnv::new(1, e))];

                        for (&pa, &other_i) in pat_args[2..].iter().zip(loc.path_indices()) {
                            let fe = ExprEnv::new((pairs.len() + 1) as u8,
                                                  Expr { ptr: unsafe { loc.origin_path().as_ptr().cast_mut().add(other_i) } });
                            pairs.push((pa, fe))
                        }

                        // pairs.iter().for_each(|(x, y)| println!("pair {} {}", x.show(), y.show()));

                        let bindings = unify(pairs);

                        match bindings {
                            Ok(bs) => {
                                // bs.iter().for_each(|(v, ee)| trace!(target: "query_multi", "binding {:?} {}", *v, ee.show()));
                                let (oi, ni) = {
                                    let mut cycled = BTreeMap::<(u8, u8), u8>::new();
                                    let r = apply(0, 0, 0, &mut ExprZipper::new(pat_expr), &bs, &mut ExprZipper::new(Expr{ ptr: scratch.as_mut_ptr() }), &mut cycled, &mut trace, &mut assignments);
                                    trace.clear();
                                    assignments.clear();
                                    // println!("scratch {:?}", Expr { ptr: scratch.as_mut_ptr() });
                                    r
                                };
                                // println!("pre {:?} {:?} {}", (oi, ni), assignments, assignments.len());

                                unsafe { std::ptr::write_volatile(&mut candidate, std::ptr::read_volatile(&candidate) + 1); }
                                if !effect(Err((bs, oi, ni, &assignments[..])), e) {
                                    unsafe { longjmp(a, 1) }
                                }
                            }
                            Err(failed) => {
                                trace!(target: "query_multi", "failed {:?}", failed)
                            }
                        }
                    } else {
                        unsafe { std::ptr::write_volatile(&mut candidate, std::ptr::read_volatile(&candidate) + 1); }
                        if !effect(Ok(unsafe { slice_from_raw_parts(references.as_ptr(), references.len()).as_ref().unwrap() }), e) {
                            unsafe { longjmp(a, 1) }
                        }
                    }
                })
            }
        });

        candidate
    }

    pub fn prefix_subsumption(prefixes: &[&[u8]]) -> Vec<usize> {
        let n = prefixes.len();
        let mut out = Vec::with_capacity(n);

        for (i, &cur) in prefixes.iter().enumerate() {
            let mut best_idx = i;
            let mut best_len = cur.len();

            for (j, &cand) in prefixes.iter().enumerate() {
                if pathmap::utils::find_prefix_overlap(cand, cur) == cand.len() {
                    let cand_len = cand.len();

                    if cand_len < best_len || (cand_len == best_len && j < best_idx) {
                        best_idx = j;
                        best_len = cand_len;
                    }
                }
            }

            out.push(best_idx);
        }

        out
    }
    pub fn transform_multi_multi_(&mut self, pat_expr: Expr, templates: &[Expr], add: Expr) -> (usize, bool) {
        let mut buffer = Vec::with_capacity(1 << 32);
        unsafe { buffer.set_len(1 << 32); }
        let mut template_prefixes: Vec<_> = templates.iter().map(|e| unsafe { e.prefix().unwrap_or_else(|x| e.span()).as_ref().unwrap() }).collect();
        let mut subsumption = Self::prefix_subsumption(&template_prefixes[..]);
        let mut placements = subsumption.clone();
        let mut read_copy = self.btm.clone();
        read_copy.insert(unsafe { add.span().as_ref().unwrap() }, ());
        let mut template_wzs: Vec<_> = vec![];
        // let mut write_copy = self.btm.clone();
        template_prefixes.iter().enumerate().for_each(|(i, x)| {
            if subsumption[i] == i {
                placements[i] = template_wzs.len();
                template_wzs.push(self.write_zipper_at_unchecked(x));
                // template_wzs.push(write_copy.write_zipper_at_path(x));
            }
        });
        for i in 0..subsumption.len() {
            subsumption[i] = placements[subsumption[i]]
        }
        trace!(target: "transform", "templates {:?}", templates);
        trace!(target: "transform", "prefixes {:?}", template_prefixes);
        trace!(target: "transform", "subsumption {:?}", subsumption);

        let mut ass = Vec::with_capacity(64);
        let mut astack = Vec::with_capacity(64);

        let mut any_new = false;
        let touched = Self::query_multi(&read_copy, pat_expr, |refs_bindings, loc| {
            trace!(target: "transform", "data {}", serialize(unsafe { loc.span().as_ref().unwrap()}));
            unsafe { unifications += 1; }
            match refs_bindings {
                Ok(refs) => {
                    for (i, (prefix, template)) in template_prefixes.iter().zip(templates.iter()).enumerate() {
                        let wz = &mut template_wzs[subsumption[i]];
                        let mut oz = ExprZipper::new(Expr { ptr: buffer.as_mut_ptr() });

                        template.substitute(&refs.iter().map(|o| Expr { ptr: unsafe { loc.ptr.offset(*o as _) } }).collect::<Vec<_>>()[..], &mut oz);

                        trace!(target: "transform", "S {i} out {:?}", oz.root);
                        wz.move_to_path(&buffer[template_prefixes[subsumption[i]].len()..oz.loc]);
                        any_new |= wz.set_val(()).is_none();
                    }
                    true
                }
                Err((ref bindings, mut oi, mut ni, mut assignments)) => {
                    #[cfg(debug_assertions)]
                    bindings.iter().for_each(|(v, ee)| trace!(target: "transform", "binding {:?} {}", *v, ee.show()));

                    for (i, (prefix, template)) in template_prefixes.iter().zip(templates.iter()).enumerate() {
                        let wz = &mut template_wzs[subsumption[i]];
                        let mut oz = ExprZipper::new(Expr { ptr: buffer.as_mut_ptr() });

                        trace!(target: "transform", "{i} template {} @ ({oi} {ni})", serialize(unsafe { template.span().as_ref().unwrap()}));

                        let res = mork_bytestring::apply(0, oi, ni, &mut ExprZipper::new(*template), bindings, &mut oz, &mut BTreeMap::new(), &mut astack, &mut ass);
                        ass.clear();
                        astack.clear();
                        // println!("res {:?}", res);

                        // loc.transformed(template,)
                        trace!(target: "transform", "U {i} out {:?}", oz.root);
                        wz.move_to_path(&buffer[template_prefixes[subsumption[i]].len()..oz.loc]);
                        any_new |= wz.set_val(()).is_none();
                    }
                    true
                }
            }
        });
        (touched, any_new)
    }


    // pub fn transform_multi(&mut self, patterns: &[Expr], template: Expr) -> (usize, bool) {
    //     self.transform_multi_multi(patterns, &[template])
    // }

    // pub fn transform(&mut self, pattern: Expr, template: Expr) -> (usize, bool) {
    //     self.transform_multi_multi(&[pattern], &[template])
    // }

    // pub fn query<F : FnMut(&[ExprEnv], Expr) -> ()>(&mut self, pattern: Expr, mut effect: F) {
    //     Self::query_multi(&self.btm, &[pattern], |refs, e| { effect(refs.unwrap(), e); Ok::<(), ()>(()) } ).unwrap();
    // }

    // (exec <loc> (, <src1> <src2> <srcn>)
    //             (, <dst1> <dst2> <dstm>))
    pub fn interpret(&mut self, rt: Expr) {
        let mut rtz = ExprZipper::new(rt);
        info!(target: "interpret", "interpreting {:?}", serialize(unsafe { rt.span().as_ref().unwrap() }));
        let mut rz = self.btm.read_zipper();
        while rz.to_next_val() {
            trace!(target: "interpret", "on space {:?}", serialize(unsafe { rz.path() }));
        }
        drop(rz);
        assert_eq!(rtz.item(), Ok(Tag::Arity(4)));
        assert!(rtz.next());
        assert_eq!(unsafe { rtz.subexpr().span().as_ref().unwrap() }, unsafe { expr!(self, "exec").span().as_ref().unwrap() });
        assert!(rtz.next());
        let loc = rtz.subexpr();

        assert!(rtz.next_child());
        let pat_expr = rtz.subexpr();
        assert!(rtz.next_child());
        let mut dstz = ExprZipper::new(rtz.subexpr());
        let Ok(Tag::Arity(m)) = dstz.item() else { panic!() };
        let mut dsts = Vec::with_capacity(m as usize - 1);
        dstz.next();
        assert_eq!(unsafe { dstz.subexpr().span().as_ref().unwrap() }, unsafe { expr!(self, ",").span().as_ref().unwrap() });
        for j in 0..m as usize - 1 {
            dstz.next_child();
            // println!("dst {j} {:?}", unsafe { serialize(dstz.subexpr().span().as_ref().unwrap()) });
            // println!("dst {j} {:?}", dstz.subexpr());
            dsts.push(dstz.subexpr());
        }

        let res = self.transform_multi_multi_(pat_expr, &dsts[..], rt);
        trace!(target: "interpret", "(run, changed) = {:?}", res);
    }

    // pub fn interpret_datalog(&mut self, rt: Expr) -> bool {
    //     let mut rtz = ExprZipper::new(rt);
    //     assert_eq!(rtz.item(), Ok(Tag::Arity(3)));
    //     assert!(rtz.next());
    //     assert_eq!(unsafe { rtz.subexpr().span().as_ref().unwrap() }, unsafe { expr!(self, "-:").span().as_ref().unwrap() });
    //     assert!(rtz.next_child());
    //     let mut dstz = ExprZipper::new(rtz.subexpr());
    //     let Ok(Tag::Arity(m)) = dstz.item() else { panic!() };
    //     let mut dsts = Vec::with_capacity(m as usize - 1);
    //     dstz.next();
    //     assert_eq!(unsafe { dstz.subexpr().span().as_ref().unwrap() }, unsafe { expr!(self, ",").span().as_ref().unwrap() });
    //     for j in 0..m as usize - 1 {
    //         dstz.next_child();
    //         dsts.push(dstz.subexpr());
    //     }
    //     assert!(rtz.next_child());
    //     let mut res = rtz.subexpr();
    //
    //     self.transform_multi(&dsts[..], res).1
    // }

    // pub fn datalog(&mut self, statements: &[Expr]) {
    //     let mut changed = true;
    //     while changed {
    //         changed = false;
    //         for statement in statements {
    //             changed |= self.interpret_datalog(*statement);
    //         }
    //     }
    // }

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

    pub fn metta_calculus(&mut self, steps: usize) -> usize {
        let mut done = 0;
        let prefix_e = expr!(self, "[4] exec $ $ $");
        let prefix = unsafe { prefix_e.prefix().unwrap().as_ref().unwrap() };
        let mut path = Vec::with_capacity(4096);

        while {
            let mut rz = self.btm.read_zipper_at_borrowed_path(prefix);
            if rz.to_next_val() {
                // cannot be here `rz` conflicts potentially with zippers(rz.path())
                path.clear();
                path.extend_from_slice(rz.origin_path());
                drop(rz);
                self.btm.remove(&path[..]);
                self.interpret(Expr{ ptr: path.as_mut_ptr() });
                done < steps
            } else {
                false
            }
        } { done += 1 }

        done
    }

    // pub fn prefix_forks(&self, e: Expr) -> (Vec<u8>, Vec<Expr>) {
    //     let Ok(prefix) = e.prefix() else {
    //         return (vec![], vec![e])
    //     };
    //
    //     let mut rz = self.btm.read_zipper_at_path(unsafe { prefix.as_ref().unwrap() });
    //     rz.descend_to([0; 4096]);
    //     rz.reset();
    //
    //     if rz.path_exists() {
    //         let mut buf = vec![];
    //         let mut es = vec![];
    //
    //         rz.descend_until();
    //
    //         // rz.child_mask()
    //
    //         (buf, es)
    //     } else {
    //         (vec![], vec![])
    //     }
    // }
    
    pub fn token_bfs(&self, token: &[u8], pattern: Expr) -> Vec<(Vec<u8>, Expr)> {

        // let mut stack = vec![0; 1];
        // stack[0] = ACTION;
        // 
        // let prefix = unsafe { pattern.prefix().unwrap_or_else(|x| pattern.span()).as_ref().unwrap() };
        // let shared = pathmap::utils::find_prefix_overlap(&token[..], prefix);
        // stack.extend_from_slice(&referential_bidirectional_matching_stack_traverse(pattern, prefix.len())[..]);
        // // println!("show {}", show_stack(&stack[..]));
        // stack.reserve(4096);
        

        let mut rz = self.btm.read_zipper_at_path(&token[..]);
        rz.reserve_buffers(4096, 64);

        rz.descend_until();
        
        let cm = rz.child_mask();
        let mut it = cm.iter();
        
        let mut res = vec![];
        
        
        while let Some(b) = it.next() {
            rz.descend_to_byte(b);
            
            let mut rzc = rz.clone();
            rzc.to_next_val();
            let e = Expr { ptr: rzc.origin_path().to_vec().leak().as_ptr().cast_mut() };
            if e.unifiable(pattern) {
                let v = rz.origin_path().to_vec();
                // println!("token {:?}", &v[..]);
                // println!("expr  {:?}", e);
                res.push((v, e));
            }
            rz.ascend_byte();
        }
        
        res
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
