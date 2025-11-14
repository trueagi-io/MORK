use std::io::{BufRead, Read, Write};
use std::{mem, process, ptr};
use std::any::Any;
use std::collections::{BTreeMap, HashMap};
use std::collections::hash_map::Entry;
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
use mork_expr::{byte_item, Expr, ExprZipper, ExtractFailure, item_byte, parse, serialize, Tag, traverseh, ExprEnv, unify, UnificationFailure, apply, destruct};
use mork_frontend::bytestring_parser::{Parser, ParserError, Context};
use mork_interning::{WritePermit, SharedMapping, SharedMappingHandle};
use pathmap::utils::{BitMask, ByteMask};
use pathmap::zipper::*;
use pathmap::arena_compact::ArenaCompactTree;
use pathmap::PathMap;
use mork_frontend::json_parser::Transcriber;
use log::*;

pub static mut transitions: usize = 0;
pub static mut unifications: usize = 0;
pub static mut writes: usize = 0;

pub static ACT_PATH: &'static str = "/dev/shm/";
// pub static ACT_PATH: &'static str = "/mnt/data/";

pub struct Space {
    pub btm: PathMap<()>,
    pub sm: SharedMappingHandle,
    pub mmaps: HashMap<&'static str, ArenaCompactTree<memmap2::Mmap>>
}

pub(crate) const SIZES: [u64; 4] = {
    let mut ret = [0u64; 4];
    let mut size = 1;
    while size < 64 {
        let k = item_byte(Tag::SymbolSize(size));
        ret[((k & 0b11000000) >> 6) as usize] |= 1u64 << (k & 0b00111111);
        size += 1;
    }
    ret
};
pub(crate) const ARITIES: [u64; 4] = {
    let mut ret = [0u64; 4];
    let mut arity = 1;
    while arity < 64 {
        let k = item_byte(Tag::Arity(arity));
        ret[((k & 0b11000000) >> 6) as usize] |= 1u64 << (k & 0b00111111);
        arity += 1;
    }
    ret
};
pub(crate) const VARS: [u64; 4] = {
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
// - use u16 x u16 compressed byte mask to reduce stack size, or to_next_sibling?
// - decrease the size of ExprEnv; it's too rich for this function
// - this function gets massive (many thousands of instructions) but can do with less checked functions
// - ascends may be avoided by using RZ refs instead of re-ascending in some cases
// - the adiabatic crate may be used to get rid of the recursion (though currently the recursion is significantly faster)
// - `references` can be elided by not putting the virtual $ Expr's on the `stack` such that _k maps directly to the indices
// - keeping a needle instead of a stack to avoid the `reverse` (would also create the opportunity to be even more lazy about instruction gen)
// - use descend_to and re-evaluated the added sub-path to do much better on long paths
fn coreferential_transition<Z : ZipperMoving + Zipper + ZipperAbsolutePath + ZipperIteration, F: FnMut(&mut Z) -> ()>(
    loc: &mut Z, mut stack: &mut Vec<ExprEnv>, references: &mut Vec<u32>, f: &mut F) {
    macro_rules! vs {
        ($e:expr, $nv:expr) => {{
            let m = loc.child_mask().and(&ByteMask(VARS));
            let mut it = m.iter();

            while let Some(b) = it.next() {
                // technically requires us to replace references to this NewVar on the stack with e
                // if !$nv && item_byte(Tag::NewVar) == b {
                //     if $e.n == 0 {
                //         references.push(u32::MAX);
                //     }
                // }
                loc.descend_to_byte(b);
                debug_assert!(loc.path_exists());
                coreferential_transition(loc, stack, references, f);
                if !loc.ascend_byte() { unreachable_unchecked() };
            }
        }};
    }
    unsafe {
    trace!(target: "coref trans", "loc {}    len {}", serialize(loc.path()), loc.path().len());
    // trace!(target: "coref trans", "loc {} ({:?})    len {}    ops {:?} ({:?})", serialize(loc.path()), loc.path(), loc.path().len(), loc.child_mask(), loc.child_mask().iter().map(byte_item).collect::<Vec<_>>());
    trace!(target: "coref trans", "top {}", stack.last().map(|x| x.show()).unwrap_or_else(|| "empty".into()));
    unsafe { transitions += 1 };
    match stack.pop() {
        None => { f(loc) }
        Some(e) => {
            let e_byte = *e.base.ptr.add(e.offset as usize);

            match byte_item(e_byte) {
                Tag::NewVar => {
                    if e.n == 0 {
                        references.push(loc.path().len() as u32);
                    } else {
                        trace!(target: "coref trans", "not putting {} {}", e.n, e.show());
                        // trace!(target: "coref trans", "not putting against {:?}", loc.child_mask());
                    }
                    vs!(e, true);

                    let m = loc.child_mask().and(&ByteMask(SIZES));
                    let mut it = m.iter();
                    while let Some(b) = it.next() {
                        let Tag::SymbolSize(size) = byte_item(b) else { unreachable_unchecked() };
                        loc.descend_to_byte(b);
                        debug_assert!(loc.path_exists());
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
                        loc.descend_to_byte(b);
                        debug_assert!(loc.path_exists());
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
                    // let addition = if e.n == 0 && references[i as usize] != u32::MAX {
                    let addition = if e.n == 0 {
                        trace!(target: "coref trans", "varref {i} at {} pushing {}", references[i as usize], serialize(&loc.path()[references[i as usize] as usize..]));
                        trace!(target: "coref trans", "varref {i} {:?}", &loc.path()[references[i as usize] as usize..]);
                        // trace!(target: "coref trans", "varref against {:?}", loc.child_mask());
                        // trace!(target: "coref trans", "varref path {:?}", serialize(loc.origin_path()));
                        ExprEnv{ n: 254, v: 0, offset: 0, base: Expr{ ptr: loc.path().as_ptr().cast_mut().offset(references[i as usize] as _) } }
                    } else {
                        trace!(target: "coref trans", "varref <{},{i}> 'any'", e.n);
                        static nv: u8 = item_byte(Tag::NewVar);
                        ExprEnv{ n: 255, v: 0, offset: 0, base: Expr{ ptr: ((&nv) as *const u8).cast_mut() } }
                    };
                    stack.push(addition);
                    vs!(e, false);
                    coreferential_transition(loc, stack, references, f);
                    stack.pop();
                }
                Tag::SymbolSize(size) => {
                    vs!(e, false);
                    if loc.descend_to_existing_byte(e_byte) {
                        if loc.descend_to_check(&*slice_from_raw_parts(e.base.ptr.byte_add(e.offset as usize + 1), size as usize)) {
                            coreferential_transition(loc, stack, references, f);
                        }
                        loc.ascend((size as usize) + 1); // The expression length + the e_byte
                    }
                }
                Tag::Arity(arity) => {
                    vs!(e, false);
                    if loc.descend_to_existing_byte(e_byte) {
                        let stackl = stack.len();
                        e.args(&mut stack);
                        stack[stackl..].reverse();
                        coreferential_transition(loc, stack, references, f);
                        stack.truncate(stack.len() - arity as usize);
                        loc.ascend_byte();
                    }
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
impl <'a, 'b, 'c> mork_frontend::json_parser::Transcriber for SpaceTranscriber<'a, 'b, 'c> {
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
    fn destruct(self) -> (usize, &'c mut Vec<u8>, ParDataParser<'a>) {
        (self.count, self.wz, self.pdp)
    }
}
impl <'a, 'c> mork_frontend::json_parser::ATranscriber<&'static [u8]> for ASpaceTranscriber<'a, 'c> {
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
        let mut src = mork_expr::parse!($s);
        let q = mork_expr::Expr{ ptr: src.as_mut_ptr() };
        let table = $space.sym_table();
        let mut pdp = $crate::space::ParDataParser::new(&table);
        let mut buf = [0u8; 4096];
        let p = mork_expr::Expr{ ptr: buf.as_mut_ptr() };
        let used = q.substitute_symbols(&mut mork_expr::ExprZipper::new(p), |x| <_ as mork_frontend::bytestring_parser::Parser>::tokenizer(&mut pdp, x));
        unsafe {
            let b = std::alloc::alloc(std::alloc::Layout::array::<u8>(used.len()).unwrap());
            std::ptr::copy_nonoverlapping(p.ptr, b, used.len());
            mork_expr::Expr{ ptr: b }
        }
    }};
    ($space:ident, $s:expr) => {{
        let mut src = mork_expr::parse::<4096>($s);
        let q = mork_expr::Expr{ ptr: src.as_mut_ptr() };
        let table = $space.sym_table();
        let mut pdp = $crate::space::ParDataParser::new(&table);
        let mut buf = [0u8; 4096];
        let p = mork_expr::Expr{ ptr: buf.as_mut_ptr() };
        let used = q.substitute_symbols(&mut mork_expr::ExprZipper::new(p), |x| <_ as mork_frontend::bytestring_parser::Parser>::tokenizer(&mut pdp, x));
        unsafe {
            let b = std::alloc::alloc(std::alloc::Layout::array::<u8>(used.len()).unwrap());
            std::ptr::copy_nonoverlapping(p.ptr, b, used.len());
            mork_expr::Expr{ ptr: b }
        }
    }};

}

#[macro_export]
macro_rules! sexpr {
    ($space:ident, $e:expr) => {{
        let mut v = vec![];
        let e: mork_expr::Expr = $e;
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
        String::from_utf8(v).unwrap_or_else(|_| unsafe { e.span().as_ref()}.map(mork_expr::serialize).unwrap_or("<null>".to_string()))
    }};
}

impl Space {
    pub fn new() -> Self {
        Self { btm: PathMap::new(), sm: SharedMapping::new(), mmaps: HashMap::new() }
    }

    pub fn parse_sexpr(&mut self, r: &[u8], buf: *mut u8) -> Result<(Expr, usize), ParserError> {
        let mut it = Context::new(r);
        let mut parser = ParDataParser::new(&self.sm);
        let mut ez = ExprZipper::new(Expr{ ptr: buf });
        parser.sexpr(&mut it, &mut ez).map(|_| (Expr{ ptr: buf }, ez.loc))
    }

    /// Remy :I want to really discourage the use of this method, it needs to be exposed if we want to use the debugging macros `expr` and `sexpr` without giving acces directly to the field
    #[doc(hidden)]
    pub fn sym_table(&self)->SharedMappingHandle{
        self.sm.clone()
    }

    pub fn statistics(&self) {
        println!("val count {}", self.btm.val_count());
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
        let mut wz = self.btm.write_zipper_at_path(constant_template_prefix);
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
        let mut wz = self.btm.write_zipper();
        let mut st = SpaceTranscriber{ count: 0, wz: &mut wz, pdp: ParDataParser::new(&self.sm) };
        let mut p = mork_frontend::json_parser::Parser::new(unsafe { std::str::from_utf8_unchecked(r) });
        p.parse(&mut st).unwrap();
        Ok(st.count)
    }

    pub fn json_to_paths<W : std::io::Write>(&mut self, r: &[u8], d: &mut W) -> Result<usize, String> {
        let mut sink = pathmap::paths_serialization::paths_serialization_sink(d);

        let mut wz = Vec::with_capacity(4096);
        let mut st = ASpaceTranscriber{ count: 0, wz: &mut wz, pdp: ParDataParser::new(&self.sm) };

        let mut p = mork_frontend::json_parser::Parser::new(unsafe { std::str::from_utf8_unchecked(r) });
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

    pub fn jsonl_to_paths<W : std::io::Write>(&mut self, r: &[u8], d: &mut W) -> Result<(usize, usize), String> {
        let mut lines = 0usize;
        let mut count = 0usize;
        let mut sink = pathmap::paths_serialization::paths_serialization_sink(d);
        let mut mpdp = Some(ParDataParser::new(&self.sm));
        let mut wz = Vec::with_capacity(4096);
        let jsonl_symbol = mpdp.as_mut().unwrap().tokenizer("JSONL".as_bytes());
        wz.push(item_byte(Tag::Arity(3)));
        wz.push(item_byte(Tag::SymbolSize(jsonl_symbol.len() as u8)));
        wz.extend_from_slice(jsonl_symbol);
        wz.push(item_byte(Tag::SymbolSize(8)));

        for line in unsafe { std::str::from_utf8_unchecked(r).lines() } {
            wz.extend_from_slice(lines.to_be_bytes().as_slice());
            let mut st = ASpaceTranscriber{ count: 0, wz: &mut wz, pdp: mpdp.take().unwrap() };

            let mut p = mork_frontend::json_parser::Parser::new(line);
            let mut coro = p.parse_stream(&mut st);
            while let CoroutineState::Yielded(n) = Pin::new(&mut coro).resume(()) {
                println!("jsonl {}", serialize(n));
                Pin::new(&mut sink).resume(Some(n));
            }
            drop(coro);
            let (line_count, _, pdp) = st.destruct();
            wz.truncate(wz.len() - 8);
            lines += 1;
            count += line_count;
            mpdp.insert(pdp);
        }
        match Pin::new(&mut sink).resume(None) {
            CoroutineState::Yielded(_) => { panic!() }
            CoroutineState::Complete(summary) => { println!("{:?}", summary) }
        }
        Ok((lines, count))
    }

    pub fn load_jsonl(&mut self, r: &[u8]) -> Result<(usize, usize), String> {
        let mut wz = self.btm.write_zipper();
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
            let mut p = mork_frontend::json_parser::Parser::new(line);
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
        let mut wz = self.btm.write_zipper_at_path(constant_template_prefix);

        let mut st = SpaceTranscriber{ count: 0, wz: &mut wz, pdp: ParDataParser::new(&self.sm) };
        let mut p = mork_frontend::json_parser::Parser::new(unsafe { std::str::from_utf8_unchecked(r) });
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

    pub fn add_all_sexpr(&mut self, r: &[u8]) -> Result<usize, String> { self.load_all_sexpr_impl(r, true) }
    pub fn remove_all_sexpr(&mut self, r: &[u8]) -> Result<usize, String> { self.load_all_sexpr_impl(r, false) }
    pub fn load_all_sexpr_impl(&mut self, r: &[u8], add: bool) -> Result<usize, String> {
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
                    if add { self.btm.insert(data, ()); }
                    else { self.btm.remove(data); }
                }
                Err(ParserError::InputFinished) => { break }
                Err(other) => { panic!("{:?}", other) }
            }
            i += 1;
            it.variables.clear();
        }
        Ok(i)
    }

    pub fn add_sexpr(&mut self, r: &[u8], pattern: Expr, template: Expr) -> Result<usize, String> { self.load_sexpr_impl(r, pattern, template, true) }
    pub fn remove_sexpr(&mut self, r: &[u8], pattern: Expr, template: Expr) -> Result<usize, String> { self.load_sexpr_impl(r, pattern, template, false) }
    pub fn load_sexpr_impl(&mut self, r: &[u8], pattern: Expr, template: Expr, add: bool) -> Result<usize, String> {
        let constant_template_prefix = unsafe { template.prefix().unwrap_or_else(|_| template.span()).as_ref().unwrap() };
        let mut wz = self.btm.write_zipper_at_path(constant_template_prefix);
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
                    wz.move_to_path(&new_data[constant_template_prefix.len()..]);
                    if add { wz.set_val(()); }
                    else { wz.remove_val(true); }
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
            // println!("{}", serialize(rz.path()));
            Expr{ ptr: rz.path().as_ptr().cast_mut() }.serialize2(w, |s| {
                #[cfg(feature="interning")]
                {
                    let symbol = i64::from_be_bytes(s.try_into().unwrap()).to_be_bytes();
                    let mstr = self.sm.get_bytes(symbol).map(unsafe { |x| std::str::from_utf8_unchecked(x) });
                    // println!("symbol {symbol:?}, bytes {mstr:?}");
                    unsafe { std::mem::transmute(mstr.expect(format!("failed to look up {:?}", symbol).as_str())) }
                }
                #[cfg(not(feature="interning"))]
                unsafe { std::mem::transmute(std::str::from_utf8_unchecked(s)) }
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
                    assert!(false)
                }
                Err(ref bindings) => {
                    let (oi, ni) = {
                        let mut cycled = BTreeMap::<(u8, u8), u8>::new();
                        let r = apply(0, 0, 0, &mut ExprZipper::new(pattern), &bindings, &mut ExprZipper::new(Expr{ ptr: buffer.as_mut_ptr() }), &mut cycled, &mut vec![], &mut vec![]);
                        r
                    };
                    mork_expr::apply(0, oi, ni, &mut ExprZipper::new(template), bindings, &mut oz, &mut BTreeMap::new(), &mut vec![], &mut vec![]);
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

    pub fn query_multi<F : FnMut(Result<&[u32], BTreeMap<(u8, u8), ExprEnv>>, Expr) -> bool>(btm: &PathMap<()>, pat_expr: Expr, mut effect: F) -> usize {
        let pat_newvars = pat_expr.newvars();
        trace!(target: "query_multi", "pattern (newvars={}) {:?}", pat_newvars, serialize(unsafe { pat_expr.span().as_ref().unwrap() }));
        let mut pat_args = vec![];
        ExprEnv::new(0, pat_expr).args(&mut pat_args);

        if pat_args.len() <= 1 { return 0 }

        let mut prz = ProductZipper::new(btm.read_zipper(), (0..(pat_args.len() - 2)).map(|i| {
            btm.read_zipper()
        }));
        prz.reserve_buffers(1 << 32, 32);

        Self::query_multi_raw(&mut prz, &pat_args[1..], effect)
    }

    pub fn query_multi_i<F : FnMut(Result<&[u32], BTreeMap<(u8, u8), ExprEnv>>, Expr) -> bool>(mut mmaps: &mut HashMap<&'static str, ArenaCompactTree<memmap2::Mmap>>, btm: &PathMap<()>, pat_expr: Expr, mut effect: F) -> usize {
        use crate::sources::{ASource, Resource, ResourceRequest, Source};

        let pat_newvars = pat_expr.newvars();
        trace!(target: "query_multi_i", "pattern (newvars={}) {:?}", pat_newvars, serialize(unsafe { pat_expr.span().as_ref().unwrap() }));
        let mut pat_args = vec![]; // todo use arity tag to prepare vec (or even stackalloc?)
        ExprEnv::new(0, pat_expr).args(&mut pat_args);

        if pat_args.len() <= 1 { return 0 }
        let mmaps_ptr = mmaps as *mut HashMap<&'static str, ArenaCompactTree<memmap2::Mmap>>;

        let mut srcs: Vec<_> = vec![];
        let mut factors: Vec<_> = vec![];
        for e in pat_args[1..].iter() {
            let mut src = ASource::new(e.subsexpr());
            factors.push(src.source(src.request().map(|request| {
                match request {
                    ResourceRequest::BTM(prefix) => { Resource::BTM(btm.read_zipper_at_path(prefix)) }
                    ResourceRequest::ACT(name) => {
                        let act = unsafe { mmaps_ptr.as_mut().unwrap() }.entry(name).or_insert_with(|| {
                            trace!(target: "query_multi_i", "open new ACT {}", name);
                            ArenaCompactTree::open_mmap(format!("{ACT_PATH}{name}.act")).unwrap()
                        });
                        trace!(target: "query_multi_i", "taking RZ of {}", name);
                        Resource::ACT(act.read_zipper())
                    }
                }
            })));
            srcs.push(src);
        }

        let mut prz = ProductZipperG::new(factors.remove(0), &mut factors[..]);
        prz.reserve_buffers(1 << 32, 32);

        Self::query_multi_raw(&mut prz, &pat_args[1..], effect)
    }

    #[cfg(feature="no_search")]
    #[inline(always)]
    pub fn query_multi_raw<PZ : ZipperProduct, F : FnMut(Result<&[u32], (BTreeMap<(u8, u8), ExprEnv>, u8, u8, &[(u8, u8)])>, Expr) -> bool>(mut prz: &mut PZ, sources: &[ExprEnv], mut effect: F) -> usize {
        let mut scratch = Vec::with_capacity(1 << 32);

        let mut assignments: Vec<(u8, u8)> = vec![];
        let mut trace: Vec<(u8, u8)> = vec![];
        let mut candidate = 0;

        
        while prz.to_next_val() {
            if prz.focus_factor() != prz.factor_count() - 1 { continue };
            let e = Expr { ptr: prz.origin_path().as_ptr().cast_mut() };
            trace!(target: "query_multi_ref", "pi {:?}", prz.path_indices());
            trace!(target: "query_multi_ref", "at {:?}", e);
            for &other_i in prz.path_indices() {
                trace!(target: "query_multi_ref", "at {:?}",
                    Expr { ptr: unsafe { prz.origin_path().as_ptr().cast_mut().add(other_i) } });
            }
            unsafe { unifications += 1; }
            // if e.variables() != 0 {

            let mut pairs = vec![(sources[0], ExprEnv::new(1, e))];

            for (&pa, &other_i) in sources[1..].iter().zip(prz.path_indices()) {
                let fe = ExprEnv::new((pairs.len() + 1) as u8,
                                      Expr { ptr: unsafe { prz.origin_path().as_ptr().cast_mut().add(other_i) } });
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
                        break
                    }
                }
                Err(failed) => {
                    trace!(target: "query_multi_ref", "U failed {:?}", failed)
                }
            }

        }
       
        candidate
    }

    #[cfg(not(feature="no_search"))]
    #[inline(always)]
    pub fn query_multi_raw<PZ : ZipperProduct, F : FnMut(Result<&[u32], BTreeMap<(u8, u8), ExprEnv>>, Expr) -> bool>(mut prz: &mut PZ, sources: &[ExprEnv], mut effect: F) -> usize {
        let mut stack = sources[0..].iter().rev().cloned().collect::<Vec<_>>();

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
                    unsafe { unifications += 1; }
                    // if e.variables() != 0 {
                    if true {
                        let mut pairs = vec![(sources[0], ExprEnv::new(1, e))];

                        for (&pa, &other_i) in sources[1..].iter().zip(loc.path_indices()) {
                            let fe = ExprEnv::new((pairs.len() + 1) as u8,
                                                  Expr { ptr: unsafe { loc.origin_path().as_ptr().cast_mut().add(other_i) } });
                            pairs.push((pa, fe))
                        }

                        // pairs.iter().for_each(|(x, y)| println!("pair {} {}", x.show(), y.show()));

                        let bindings = unify(pairs);

                        match bindings {
                            Ok(bs) => {
                                unsafe { std::ptr::write_volatile(&mut candidate, std::ptr::read_volatile(&candidate) + 1); }
                                if !effect(Err(bs), e) {
                                    unsafe { longjmp(a, 1) }
                                }
                            }
                            Err(failed) => {
                                trace!(target: "query_multi", "U failed {:?}", failed)
                            }
                        }
                    } else {
                        trace!(target: "query_multi", "#variables==0 {:?}", e);
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

    // pub fn prefix_subsumption_resources(prefixes: &[crate::sinks::WriteResourceRequest]) -> Vec<usize> {
    //     let n = prefixes.len();
    //     let mut out = Vec::with_capacity(n);
    //
    //     for (i, &cur) in prefixes.iter().enumerate() {
    //         let mut best_idx = i;
    //         let mut best_len = cur.len();
    //
    //         for (j, &cand) in prefixes.iter().enumerate() {
    //             // cand \/ cur == cand
    //             // x <= y  <=>  (x \/ y) == y
    //             if pathmap::utils::find_prefix_overlap(cand, cur) == cand.len() {
    //                 let cand_len = cand.len();
    //
    //                 // cand < best || (cand == best &&)
    //                 if cand_len < best_len || (cand_len == best_len && j < best_idx) {
    //                     best_idx = j;
    //                     best_len = cand_len;
    //                 }
    //             }
    //         }
    //
    //         out.push(best_idx);
    //     }
    //
    //     out
    // }

    pub fn transform_multi_multi_(&mut self, pat_expr: Expr, tpl_expr: Expr, add: Expr) -> (usize, bool) {
        let mut buffer = Vec::with_capacity(1 << 32);
        unsafe { buffer.set_len(1 << 32); }
        let mut tpl_args = Vec::with_capacity(64);
        ExprEnv::new(0, tpl_expr).args(&mut tpl_args);
        let mut templates: Vec<_> = tpl_args[1..].iter().map(|ee| ee.subsexpr()).collect();
        let mut template_prefixes: Vec<_> = templates.iter().map(|e| unsafe { e.prefix().unwrap_or_else(|x| e.span()).as_ref().unwrap() }).collect();
        let mut subsumption = Self::prefix_subsumption(&template_prefixes[..]);
        let mut placements = subsumption.clone();
        let mut read_copy = self.btm.clone();
        let mut zh = self.btm.zipper_head();
        read_copy.insert(unsafe { add.span().as_ref().unwrap() }, ());
        let mut template_wzs: Vec<_> = Vec::with_capacity(64);
        template_prefixes.iter().enumerate().for_each(|(i, x)| {
            if subsumption[i] == i {
                placements[i] = template_wzs.len();
                template_wzs.push(unsafe { zh.write_zipper_at_exclusive_path_unchecked(x) });
            }
        });
        for i in 0..subsumption.len() {
            subsumption[i] = placements[subsumption[i]]
        }
        trace!(target: "transform", "templates {:?}", templates);
        trace!(target: "transform", "prefixes {:?}", template_prefixes);
        trace!(target: "transform", "subsumption {:?}", subsumption);
        // let pvs = pat_expr.variables();
        // let mut pvc = 0;
        // let mut psubs = vec![0; 64];
        // static nv: u8 = item_byte(Tag::NewVar);
        // let mut refs_es = (0..64).map(|_|  Expr{ ptr: ((&nv) as *const u8).cast_mut() }).collect::<Vec<_>>();
        // pat_expr.substitute_de_bruijn_ivc(&refs_es[..], &mut ExprZipper::new(Expr{ ptr: vec![0; 512].leak().as_mut_ptr() }), &mut pvc, &mut psubs[..]);
        // for l in psubs.iter_mut() { *l -= pvs as u8; }

        let mut scratch = Vec::with_capacity(1 << 32);

        let mut assignments: Vec<(u8, u8)> = vec![];
        let mut trace: Vec<(u8, u8)> = vec![];

        let mut oz = ExprZipper::new(Expr { ptr: buffer.as_mut_ptr() });

        let mut ass = Vec::with_capacity(64);
        let mut astack = Vec::with_capacity(64);

        let mut any_new = false;
        let touched = Self::query_multi(&read_copy, pat_expr, |refs_bindings, loc| {
            trace!(target: "transform", "data {}", serialize(unsafe { loc.span().as_ref().unwrap()}));
            unsafe { writes += template_prefixes.len(); }
            match refs_bindings {
                Ok(refs) => {
                    // refs_es.clear();
                    // refs_es.extend(refs.iter().map(|o| Expr { ptr: unsafe { loc.ptr.offset(*o as _) } }));
                    // refs_es.extend((0..(64-refs.len())).map(|_|  Expr{ ptr: ((&nv) as *const u8).cast_mut() }));
                    // trace!(target: "transform", "S refs out {:?}", refs_es);
                    // trace!(target: "transform", "S refs pat {:?} {pvs}", pat_expr);
                    //
                    // for (i, template) in templates.iter().enumerate() {
                    //     let wz = &mut template_wzs[subsumption[i]];
                    //     oz.reset();
                    //
                    //     trace!(target: "transform", "S refs tpl {:?}", template);
                    //     template.substitute_de_bruijn_ivc(&refs_es[..], &mut oz, &mut pvc.clone(), &mut psubs.clone());
                    //
                    //     trace!(target: "transform", "S {i} out {:?}", oz.root);
                    //     wz.move_to_path(&buffer[wz.root_prefix_path().len()..oz.loc]);
                    //     any_new |= wz.set_val(()).is_none();
                    // }
                    true
                }
                Err((ref bindings)) => {
                    #[cfg(debug_assertions)]
                    bindings.iter().for_each(|(v, ee)| trace!(target: "transform", "binding {:?} {}", *v, ee.show()));

                    let (oi, ni) = {
                        let mut cycled = BTreeMap::<(u8, u8), u8>::new();
                        let r = apply(0, 0, 0, &mut ExprZipper::new(pat_expr), &bindings, &mut ExprZipper::new(Expr{ ptr: scratch.as_mut_ptr() }), &mut cycled, &mut trace, &mut assignments);
                        trace.clear();
                        assignments.clear();
                        // println!("scratch {:?}", Expr { ptr: scratch.as_mut_ptr() });
                        r
                    };

                    for (i, template) in templates.iter().enumerate() {
                        let wz = &mut template_wzs[subsumption[i]];
                        oz.reset();

                        trace!(target: "transform", "{i} template {} @ ({oi} {ni})", serialize(unsafe { template.span().as_ref().unwrap()}));

                        let res = mork_expr::apply_e(0, oi, ni, *template, bindings, &mut oz, &mut BTreeMap::new(), &mut astack, &mut ass);
                        ass.clear();
                        astack.clear();

                        trace!(target: "transform", "U {i} out {:?}", oz.root);
                        wz.move_to_path(&buffer[wz.root_prefix_path().len()..oz.loc]);
                        any_new |= wz.set_val(()).is_none();
                    }
                    true
                }
            }
        });
        for wz in template_wzs {
            zh.cleanup_write_zipper(wz);
        }
        (touched, any_new)
    }

    pub fn transform_multi_multi_i(&mut self, pat_expr: Expr, tpl_expr: Expr, add: Expr) -> (usize, bool) {
        let mut buffer = Vec::with_capacity(1 << 32);
        unsafe { buffer.set_len(1 << 32); }
        let mut tpl_args = Vec::with_capacity(64);
        ExprEnv::new(0, tpl_expr).args(&mut tpl_args);
        let mut templates: Vec<_> = tpl_args[1..].iter().map(|ee| ee.subsexpr()).collect();
        let mut template_prefixes: Vec<_> = templates.iter().map(|e| unsafe { e.prefix().unwrap_or_else(|x| e.span()).as_ref().unwrap() }).collect();
        let mut subsumption = Self::prefix_subsumption(&template_prefixes[..]);
        let mut placements = subsumption.clone();
        let mut read_copy = self.btm.clone();
        let mut zh = self.btm.zipper_head();
        read_copy.insert(unsafe { add.span().as_ref().unwrap() }, ());
        let mut template_wzs: Vec<_> = Vec::with_capacity(64);
        template_prefixes.iter().enumerate().for_each(|(i, x)| {
            if subsumption[i] == i {
                placements[i] = template_wzs.len();
                template_wzs.push(unsafe { zh.write_zipper_at_exclusive_path_unchecked(x) });
            }
        });
        for i in 0..subsumption.len() {
            subsumption[i] = placements[subsumption[i]]
        }
        trace!(target: "transform", "templates {:?}", templates);
        trace!(target: "transform", "prefixes {:?}", template_prefixes);
        trace!(target: "transform", "subsumption {:?}", subsumption);
        // let pvs = pat_expr.variables();
        // let mut pvc = 0;
        // let mut psubs = vec![0; 64];
        // static nv: u8 = item_byte(Tag::NewVar);
        // let mut refs_es = (0..64).map(|_|  Expr{ ptr: ((&nv) as *const u8).cast_mut() }).collect::<Vec<_>>();
        // pat_expr.substitute_de_bruijn_ivc(&refs_es[..], &mut ExprZipper::new(Expr{ ptr: vec![0; 512].leak().as_mut_ptr() }), &mut pvc, &mut psubs[..]);
        // for l in psubs.iter_mut() { *l -= pvs as u8; }

        let mut scratch = Vec::with_capacity(1 << 32);

        let mut assignments: Vec<(u8, u8)> = vec![];
        let mut trace: Vec<(u8, u8)> = vec![];

        let mut oz = ExprZipper::new(Expr { ptr: buffer.as_mut_ptr() });

        let mut ass = Vec::with_capacity(64);
        let mut astack = Vec::with_capacity(64);

        let mut any_new = false;
        let touched = Self::query_multi_i(&mut self.mmaps, &read_copy, pat_expr, |refs_bindings, loc| {
            trace!(target: "transform", "data {}", serialize(unsafe { loc.span().as_ref().unwrap()}));
            unsafe { writes += template_prefixes.len(); }
            match refs_bindings {
                Ok(refs) => {
                    // refs_es.clear();
                    // refs_es.extend(refs.iter().map(|o| Expr { ptr: unsafe { loc.ptr.offset(*o as _) } }));
                    // refs_es.extend((0..(64-refs.len())).map(|_|  Expr{ ptr: ((&nv) as *const u8).cast_mut() }));
                    // trace!(target: "transform", "S refs out {:?}", refs_es);
                    // trace!(target: "transform", "S refs pat {:?} {pvs}", pat_expr);
                    // 
                    // for (i, template) in templates.iter().enumerate() {
                    //     let wz = &mut template_wzs[subsumption[i]];
                    //     oz.reset();
                    // 
                    //     trace!(target: "transform", "S refs tpl {:?}", template);
                    //     template.substitute_de_bruijn_ivc(&refs_es[..], &mut oz, &mut pvc.clone(), &mut psubs.clone());
                    // 
                    //     trace!(target: "transform", "S {i} out {:?}", oz.root);
                    //     wz.move_to_path(&buffer[wz.root_prefix_path().len()..oz.loc]);
                    //     any_new |= wz.set_val(()).is_none();
                    // }
                    true
                }
                Err((ref bindings)) => {
                    #[cfg(debug_assertions)]
                    bindings.iter().for_each(|(v, ee)| trace!(target: "transform", "binding {:?} {}", *v, ee.show()));

                    let (oi, ni) = {
                        let mut cycled = BTreeMap::<(u8, u8), u8>::new();
                        let r = apply(0, 0, 0, &mut ExprZipper::new(pat_expr), &bindings, &mut ExprZipper::new(Expr{ ptr: scratch.as_mut_ptr() }), &mut cycled, &mut trace, &mut assignments);
                        trace.clear();
                        assignments.clear();
                        // println!("scratch {:?}", Expr { ptr: scratch.as_mut_ptr() });
                        r
                    };

                    for (i, template) in templates.iter().enumerate() {
                        let wz = &mut template_wzs[subsumption[i]];
                        oz.reset();

                        trace!(target: "transform", "{i} template {} @ ({oi} {ni})", serialize(unsafe { template.span().as_ref().unwrap()}));

                        let res = mork_expr::apply_e(0, oi, ni, *template, bindings, &mut oz, &mut BTreeMap::new(), &mut astack, &mut ass);
                        ass.clear();
                        astack.clear();

                        trace!(target: "transform", "U {i} out {:?}", oz.root);
                        wz.move_to_path(&buffer[wz.root_prefix_path().len()..oz.loc]);
                        any_new |= wz.set_val(()).is_none();
                    }
                    true
                }
            }
        });
        for wz in template_wzs {
            zh.cleanup_write_zipper(wz);
        }
        (touched, any_new)
    }


    pub fn transform_multi_multi_o(&mut self, pat_expr: Expr, tpl_expr: Expr, add: Expr) -> (usize, bool) {
        use crate::sinks::*;
        let mut buffer = Vec::with_capacity(1 << 32);
        unsafe { buffer.set_len(1 << 32); }
        let mut tpl_args = Vec::with_capacity(64);
        ExprEnv::new(0, tpl_expr).args(&mut tpl_args);
        let mut templates: Vec<_> = tpl_args[1..].iter().map(|ee| ee.subsexpr()).collect();
        let mut sinks: Vec<_> = templates.iter().map(|e| ASink::new(*e)).collect();
        let mut template_prefixes: Vec<_> = sinks.iter().map(|sink|
            match sink.request().next().unwrap() {
                WriteResourceRequest::BTM(p) => p,
                WriteResourceRequest::ACT(_) => unreachable!()
            }
        ).collect();
        let mut subsumption = Self::prefix_subsumption(&template_prefixes[..]);
        let mut placements = subsumption.clone();
        let mut read_copy = self.btm.clone();
        let mut zh = self.btm.zipper_head();
        read_copy.insert(unsafe { add.span().as_ref().unwrap() }, ());
        let mut template_wzs: Vec<_> = Vec::with_capacity(64);
        template_prefixes.iter().enumerate().for_each(|(i, x)| {
            if subsumption[i] == i {
                placements[i] = template_wzs.len();
                template_wzs.push(unsafe { zh.write_zipper_at_exclusive_path_unchecked(x) });
            }
        });
        for i in 0..subsumption.len() {
            subsumption[i] = placements[subsumption[i]]
        }
        trace!(target: "transform", "templates {:?}", templates);
        trace!(target: "transform", "prefixes {:?}", template_prefixes);
        trace!(target: "transform", "subsumption {:?}", subsumption);
        // let pvs = pat_expr.variables();
        // let mut pvc = 0;
        // let mut psubs = vec![0; 64];
        // static nv: u8 = item_byte(Tag::NewVar);
        // let mut refs_es = (0..64).map(|_|  Expr{ ptr: ((&nv) as *const u8).cast_mut() }).collect::<Vec<_>>();
        // pat_expr.substitute_de_bruijn_ivc(&refs_es[..], &mut ExprZipper::new(Expr{ ptr: vec![0; 512].leak().as_mut_ptr() }), &mut pvc, &mut psubs[..]);
        // for l in psubs.iter_mut() { *l -= pvs as u8; }

        let mut scratch = Vec::with_capacity(1 << 32);

        let mut assignments: Vec<(u8, u8)> = vec![];
        let mut trace: Vec<(u8, u8)> = vec![];
        
        let mut oz = ExprZipper::new(Expr { ptr: buffer.as_mut_ptr() });

        let mut ass = Vec::with_capacity(64);
        let mut astack = Vec::with_capacity(64);

        let mut any_new = false;
        let touched = Self::query_multi(&read_copy, pat_expr, |refs_bindings, loc| {
            trace!(target: "transform", "data {}", serialize(unsafe { loc.span().as_ref().unwrap()}));
            unsafe { writes += template_prefixes.len(); }
            match refs_bindings {
                Ok(refs) => {
                    // refs_es.clear();
                    // refs_es.extend(refs.iter().map(|o| Expr { ptr: unsafe { loc.ptr.offset(*o as _) } }));
                    // refs_es.extend((0..(64-refs.len())).map(|_|  Expr{ ptr: ((&nv) as *const u8).cast_mut() }));
                    // trace!(target: "transform", "S refs out {:?}", refs_es);
                    // trace!(target: "transform", "S refs pat {:?} {pvs}", pat_expr);
                    // 
                    // for (i, template) in templates.iter().enumerate() {
                    //     let wz = &mut template_wzs[subsumption[i]];
                    //     oz.reset();
                    // 
                    //     trace!(target: "transform", "S refs tpl {:?}", template);
                    //     template.substitute_de_bruijn_ivc(&refs_es[..], &mut oz, &mut pvc.clone(), &mut psubs.clone());
                    // 
                    //     trace!(target: "transform", "S {i} out {:?}", oz.root);
                    //     sinks[i].sink(std::iter::once(wz), &buffer[..oz.loc]);
                    // }
                    true
                }
                Err(ref bindings) => {
                    #[cfg(debug_assertions)]
                    bindings.iter().for_each(|(v, ee)| trace!(target: "transform", "binding {:?} {}", *v, ee.show()));

                    let (oi, ni) = {
                        let mut cycled = BTreeMap::<(u8, u8), u8>::new();
                        let r = apply(0, 0, 0, &mut ExprZipper::new(pat_expr), &bindings, &mut ExprZipper::new(Expr{ ptr: scratch.as_mut_ptr() }), &mut cycled, &mut trace, &mut assignments);
                        trace.clear();
                        assignments.clear();
                        // println!("scratch {:?}", Expr { ptr: scratch.as_mut_ptr() });
                        r
                    };
                
                    for (i, template) in templates.iter().enumerate() {
                        let wz = &mut template_wzs[subsumption[i]];
                        oz.reset();

                        trace!(target: "transform", "{i} template {} @ ({oi} {ni})", serialize(unsafe { template.span().as_ref().unwrap()}));

                        let res = mork_expr::apply_e(0, oi, ni, *template, bindings, &mut oz, &mut BTreeMap::new(), &mut astack, &mut ass);
                        ass.clear();
                        astack.clear();

                        trace!(target: "transform", "U {i} out {:?}", oz.root);
                        sinks[i].sink(std::iter::once(WriteResource::BTM(wz)), &buffer[..oz.loc]);
                    }
                    true
                }
            }
        });

        for (i, s) in sinks.iter_mut().enumerate() {
            let wz = &mut template_wzs[subsumption[i]];
            any_new |= s.finalize(std::iter::once(WriteResource::BTM(wz)));
        }
        for wz in template_wzs {
            zh.cleanup_write_zipper(wz);
        }

        (touched, any_new)
    }

    pub fn transform_multi_multi_io(&mut self, pat_expr: Expr, tpl_expr: Expr, add: Expr) -> (usize, bool) {
        use crate::sinks::*;
        let mut buffer = Vec::with_capacity(1 << 32);
        unsafe { buffer.set_len(1 << 32); }
        let mut tpl_args = Vec::with_capacity(64);
        ExprEnv::new(0, tpl_expr).args(&mut tpl_args);
        let mut templates: Vec<_> = tpl_args[1..].iter().map(|ee| ee.subsexpr()).collect();
        let mut sinks: Vec<_> = templates.iter().map(|e| ASink::new(*e)).collect();
        let mut template_prefixes: Vec<_> = sinks.iter().map(|sink|
            match sink.request().next().unwrap() {
                WriteResourceRequest::BTM(p) => p,
                WriteResourceRequest::ACT(_) => unreachable!()
            }
        ).collect();
        let mut subsumption = Self::prefix_subsumption(&template_prefixes[..]);
        let mut placements = subsumption.clone();
        let mut read_copy = self.btm.clone();
        let mut zh = self.btm.zipper_head();
        read_copy.insert(unsafe { add.span().as_ref().unwrap() }, ());
        let mut template_wzs: Vec<_> = Vec::with_capacity(64);
        template_prefixes.iter().enumerate().for_each(|(i, x)| {
            if subsumption[i] == i {
                placements[i] = template_wzs.len();
                template_wzs.push(unsafe { zh.write_zipper_at_exclusive_path_unchecked(x) });
            }
        });
        for i in 0..subsumption.len() {
            subsumption[i] = placements[subsumption[i]]
        }
        trace!(target: "transform", "templates {:?}", templates);
        trace!(target: "transform", "prefixes {:?}", template_prefixes);
        trace!(target: "transform", "subsumption {:?}", subsumption);
        // let pvs = pat_expr.variables();
        // let mut pvc = 0;
        // let mut psubs = vec![0; 64];
        // static nv: u8 = item_byte(Tag::NewVar);
        // let mut refs_es = (0..64).map(|_|  Expr{ ptr: ((&nv) as *const u8).cast_mut() }).collect::<Vec<_>>();
        // pat_expr.substitute_de_bruijn_ivc(&refs_es[..], &mut ExprZipper::new(Expr{ ptr: vec![0; 512].leak().as_mut_ptr() }), &mut pvc, &mut psubs[..]);
        // for l in psubs.iter_mut() { *l -= pvs as u8; }

        let mut scratch = Vec::with_capacity(1 << 32);

        let mut assignments: Vec<(u8, u8)> = vec![];
        let mut trace: Vec<(u8, u8)> = vec![];

        let mut oz = ExprZipper::new(Expr { ptr: buffer.as_mut_ptr() });

        let mut ass = Vec::with_capacity(64);
        let mut astack = Vec::with_capacity(64);

        let mut any_new = false;
        let touched = Self::query_multi_i(&mut self.mmaps, &read_copy, pat_expr, |refs_bindings, loc| {
            trace!(target: "transform", "data {}", serialize(unsafe { loc.span().as_ref().unwrap()}));
            unsafe { writes += template_prefixes.len(); }
            match refs_bindings {
                Ok(refs) => {
                    // refs_es.clear();
                    // refs_es.extend(refs.iter().map(|o| Expr { ptr: unsafe { loc.ptr.offset(*o as _) } }));
                    // refs_es.extend((0..(64-refs.len())).map(|_|  Expr{ ptr: ((&nv) as *const u8).cast_mut() }));
                    // trace!(target: "transform", "S refs out {:?}", refs_es);
                    // trace!(target: "transform", "S refs pat {:?} {pvs}", pat_expr);
                    //
                    // for (i, template) in templates.iter().enumerate() {
                    //     let wz = &mut template_wzs[subsumption[i]];
                    //     oz.reset();
                    //
                    //     trace!(target: "transform", "S refs tpl {:?}", template);
                    //     template.substitute_de_bruijn_ivc(&refs_es[..], &mut oz, &mut pvc.clone(), &mut psubs.clone());
                    //
                    //     trace!(target: "transform", "S {i} out {:?}", oz.root);
                    //     sinks[i].sink(std::iter::once(wz), &buffer[..oz.loc]);
                    // }
                    true
                }
                Err(ref bindings) => {
                    #[cfg(debug_assertions)]
                    bindings.iter().for_each(|(v, ee)| trace!(target: "transform", "binding {:?} {}", *v, ee.show()));

                    let (oi, ni) = {
                        let mut cycled = BTreeMap::<(u8, u8), u8>::new();
                        let r = apply(0, 0, 0, &mut ExprZipper::new(pat_expr), &bindings, &mut ExprZipper::new(Expr{ ptr: scratch.as_mut_ptr() }), &mut cycled, &mut trace, &mut assignments);
                        trace.clear();
                        assignments.clear();
                        // println!("scratch {:?}", Expr { ptr: scratch.as_mut_ptr() });
                        r
                    };

                    for (i, template) in templates.iter().enumerate() {
                        let wz = &mut template_wzs[subsumption[i]];
                        oz.reset();

                        trace!(target: "transform", "{i} template {} @ ({oi} {ni})", serialize(unsafe { template.span().as_ref().unwrap()}));

                        let res = mork_expr::apply_e(0, oi, ni, *template, bindings, &mut oz, &mut BTreeMap::new(), &mut astack, &mut ass);
                        ass.clear();
                        astack.clear();

                        trace!(target: "transform", "U {i} out {:?}", oz.root);
                        sinks[i].sink(std::iter::once(WriteResource::BTM(wz)), &buffer[..oz.loc]);
                    }
                    true
                }
            }
        });

        for (i, s) in sinks.iter_mut().enumerate() {
            let wz = &mut template_wzs[subsumption[i]];
            any_new |= s.finalize(std::iter::once(WriteResource::BTM(wz)));
        }
        for wz in template_wzs {
            zh.cleanup_write_zipper(wz);
        }

        (touched, any_new)
    }
    
    // (exec <loc> (, <src1> <src2> <srcn>)
    //             (, <dst1> <dst2> <dstm>))
    pub fn interpret(&mut self, rt: Expr) {
        debug!(target: "interpret", "interpreting {:?}", serialize(unsafe { rt.span().as_ref().unwrap() }));
        #[cfg(debug_assertions)]
        { let mut rz = self.btm.read_zipper(); while rz.to_next_val() { trace!(target: "interpret", "on space {:?}", serialize(unsafe { rz.path() })); }; drop(rz); }
        destruct!(rt, ("exec" loc pat_expr tpl_expr), unsafe {
            if let Tag::Arity(i) = byte_item(*pat_expr.ptr) { if i == 0 { panic!("pattern expression can not be empty"); } } else { panic!("pattern must be an expression, not {:?}", pat_expr) }
            if *pat_expr.ptr.add(1) != item_byte(Tag::SymbolSize(1)) { panic!("pattern functor can only be , or I") }

            if let Tag::Arity(i) = byte_item(*tpl_expr.ptr) { if i == 0 { panic!("template expression can not be empty"); } } else { panic!("template must be an expression") }
            if *tpl_expr.ptr.add(1) != item_byte(Tag::SymbolSize(1)) { panic!("template functor can only be , or O") }

            let res = match (*pat_expr.ptr.add(2), *tpl_expr.ptr.add(2)) {
                (b',', b',') => { self.transform_multi_multi_(pat_expr, tpl_expr, rt) }
                (b'I', b',') => { self.transform_multi_multi_i(pat_expr, tpl_expr, rt) }
                (b',', b'O') => { self.transform_multi_multi_o(pat_expr, tpl_expr, rt) }
                (b'I', b'O') => { self.transform_multi_multi_io(pat_expr, tpl_expr, rt) }
                (_, _) => { panic!("pattern functor can only be , or I and template functor can only be , or O") }
            };
            trace!(target: "interpret", "(run, changed) = {:?}", res);
        }, _err => panic!("exec shape (exec <loc> <patterns> <templates>)"));
    }

    pub fn metta_calculus(&mut self, steps: usize) -> usize {
        let mut done = 0;
        let prefix_e = expr!(self, "[4] exec $ $ $");
        let prefix = unsafe { prefix_e.prefix().unwrap().as_ref().unwrap() };

        while {
            let mut rz = self.btm.read_zipper_at_borrowed_path(prefix);
            if rz.to_next_val() {
                // cannot be here `rz` conflicts potentially with zippers(rz.path())
                let mut x: Box<[u8]> = rz.origin_path().into(); // should use local buffer
                drop(rz);
                self.btm.remove(&x[..]);
                // println!("expr {:?}", Expr{ ptr: x.as_mut_ptr() });
                self.interpret(Expr{ ptr: x.as_mut_ptr() });
                done < steps
            } else {
                false
            }
        } { done += 1 }

        done
    }
    
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
