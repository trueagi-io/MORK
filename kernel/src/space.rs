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
use std::str::Utf8Error;
use std::task::Poll;
use std::time::Instant;
use futures::StreamExt;
use pathmap::ring::{AlgebraicStatus, Lattice};
use mork_expr::{byte_item, Expr, ExprZipper, ExtractFailure, item_byte, parse, serialize, Tag, traverseh, ExprEnv, unify, UnificationFailure, apply, destruct, OwnedSourceItem};
use mork_frontend::bytestring_parser::{Parser, ParserError, Context};
use mork_interning::{WritePermit, SharedMapping, SharedMappingHandle};
use pathmap::utils::{BitMask, ByteMask};
use pathmap::zipper::*;
use pathmap::arena_compact::ArenaCompactTree;
use pathmap::{zipper, PathMap};
use mork_frontend::json_parser::Transcriber;
use log::*;
use subprocess::{Popen, PopenConfig, Redirection};
use subprocess::unix::PopenExt;
use crate::sinks::{WriteResource, WriteResourceRequest};
use crate::sources::{AFactor, Resource, ResourceRequest};

pub static mut transitions: usize = 0;
pub static mut unifications: usize = 0;
pub static mut writes: usize = 0;

pub static ACT_PATH: &'static str = "/dev/shm/";
// pub static ACT_PATH: &'static str = "/mnt/data/";

pub struct Space {
    /// Per-rule frontiers for the semi-naive immediate-consequence delta, armed by
    /// `metta_calculus` for the duration of its loop (None on every other caller, so
    /// every default path stays the naive full-space match).
    #[cfg(feature = "semi_naive_ic")]
    sni_rule_seen: Option<HashMap<Vec<u8>, SniRuleEntry>>,
    /// Latched when a removal ran inside the current IC loop: the per-rule delta is
    /// the monotone semi-naive recurrence, byte-identical to naive only while
    /// evaluation is add-only, so any removal routes the rest of the loop to naive.
    #[cfg(feature = "semi_naive_ic")]
    sni_removal_seen: bool,
    /// Runtime revert: force the naive loop even with the feature compiled in.
    #[cfg(feature = "semi_naive_ic")]
    pub sni_force_naive: bool,
    /// Count of `,`->`,` firings this space routed through the delta transform
    /// (race-free engagement signal for tests; the global counters are shared).
    #[cfg(feature = "semi_naive_ic")]
    pub sni_semi_firings: usize,
    /// `,`->`,` firings inside the current IC loop, reset at arming; drives the
    /// give-up disarm below.
    #[cfg(feature = "semi_naive_ic")]
    sni_loop_firings: usize,
    pub btm: PathMap<()>,
    pub sm: SharedMappingHandle,
    pub mmaps: HashMap<OwnedSourceItem, ArenaCompactTree<memmap2::Mmap>>,
    pub z3s: HashMap<OwnedSourceItem, Box<Popen>>,
    pub last_merkleize: Instant,
    pub timing: bool
}

/// One rule's semi-naive frontier: the match input (`btm` plus the consumed exec)
/// the last time this rule fired, and its cached fact count so the cost gate never
/// pays an O(dish) walk on later firings.
#[cfg(feature = "semi_naive_ic")]
pub(crate) struct SniRuleEntry {
    /// The rule's frontier: the match input the last time this rule fired.
    pub(crate) snapshot: PathMap<()>,
    /// Fact count of `snapshot`, computed LAZILY on the rule's second firing (a
    /// first firing routes to naive regardless, so paying an O(dish) walk for a
    /// rule that never fires again -- e.g. programs that respawn counter-carrying
    /// rules every round -- would be pure overhead).
    pub(crate) dish_count: Option<usize>,
}

#[cfg(feature = "semi_naive_ic")]
thread_local! {
    /// Revert for the semi-naive IC delta: when true, `metta_calculus` forces the
    /// naive loop even with `semi_naive_ic` compiled in (the second revert next to
    /// removing the feature; `MORK_SNI=0` is the process-wide form, checked at
    /// arming). Thread-local so a test pinning the reference path never disarms a
    /// concurrently running test's loop.
    pub static SNI_DISARM: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
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
    let mut arity = 0;
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
                    let restore = if e.n == 0 {
                        let idx = e.v as usize;
                        if references.len() <= idx { references.resize(idx + 1, u32::MAX) }
                        let prev = references[idx];
                        references[idx] = loc.path().len() as u32;
                        Some((idx, prev))
                    } else { None };

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

                    if let Some((idx, prev)) = restore { references[idx] = prev; }
                }
                Tag::VarRef(i) => {
                    // The bound branch re-matches the RECORDED data subterm. Its bytes
                    // live in `loc`'s path buffer, which the recursion below GROWS; past
                    // the reserved capacity the buffer REALLOCATES and a raw pointer into
                    // it dangles, decoding garbage tag bytes on deep terms (a `byte_item`
                    // "reserved" panic; a delta-reordered descent reaches this with deep
                    // bound payloads). Copy the subterm into an owned buffer that lives
                    // across the recursion and point the re-match at that.
                    let mut _bound_owned: Vec<u8> = Vec::new();
                    let addition = if e.n == 0 && (i as usize) < references.len() && references[i as usize] != u32::MAX {
                        if i as usize >= references.len() {
                            trace!(target: "coref trans", "i {i} #references {}", references.len());
                            stack.push(e);
                            return;
                        }
                        trace!(target: "coref trans", "varref {i} at {} pushing {}", references[i as usize], serialize(&loc.path()[references[i as usize] as usize..]));
                        trace!(target: "coref trans", "varref {i} {:?}", &loc.path()[references[i as usize] as usize..]);
                        let bound = Expr{ ptr: loc.path().as_ptr().cast_mut().offset(references[i as usize] as _) };
                        _bound_owned = slice_from_raw_parts(bound.ptr, bound.span().as_ref().unwrap().len()).as_ref().unwrap().to_vec();
                        ExprEnv{ n: 254, v: 0, offset: 0, base: Expr{ ptr: _bound_owned.as_ptr().cast_mut() } }
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
        Self {
            #[cfg(feature = "semi_naive_ic")]
            sni_rule_seen: None,
            #[cfg(feature = "semi_naive_ic")]
            sni_removal_seen: false,
            #[cfg(feature = "semi_naive_ic")]
            sni_force_naive: false,
            #[cfg(feature = "semi_naive_ic")]
            sni_semi_firings: 0,
            #[cfg(feature = "semi_naive_ic")]
            sni_loop_firings: 0,
            btm: PathMap::new(), sm: SharedMapping::new(), mmaps: HashMap::new(), z3s: HashMap::new(), last_merkleize: Instant::now(), timing: false }
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
                Err(other) => { return Err(format!("{:?}", other)) }
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

        let mut buffer = Vec::with_capacity(1 << 32);
        unsafe { buffer.set_len(1 << 32); }
        let mut pat = vec![item_byte(Tag::Arity(2)), item_byte(Tag::SymbolSize(1)), b','];
        pat.extend_from_slice(unsafe { pattern.span().as_ref().unwrap() });

        let mut stack       = Vec::new();
        let mut assignments = Vec::new();
        Self::query_multi(&self.btm, Expr{ ptr: pat.leak().as_mut_ptr() }, |refs_bindings, loc| 'query : {
            let mut oz = ExprZipper::new(Expr { ptr: buffer.as_mut_ptr() });

            match refs_bindings {
                Ok(refs) => {
                    assert!(false)
                }
                Err(ref bindings) => {
                    buffer.clear();

                    let (oi, ni, true) = mork_expr::apply_e_clears_stacks_and_cycles_check!(0,0,0, pattern, bindings, buffer, stack, assignments)
                    else { break 'query true};

                    buffer.clear();

                    let (_,_,true) = mork_expr::apply_e_clears_stacks_and_cycles_check!(0,oi,ni, template, bindings, buffer, stack, assignments)
                    else { break 'query true;};
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
                unsafe { std::mem::transmute(std::str::from_utf8_unchecked(s)) }
            }, |i, intro| { Expr::VARNAMES[i as usize] });
            let mut buffer_slice = &mut buffer[..];
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
        let n_factors = pat_expr.arity().unwrap() as usize;
        debug_assert!(n_factors > 0);
        if n_factors == 1 {
            effect(Err(BTreeMap::new()), pat_expr);
            return 1;
        }
        let mut pat_args = Vec::with_capacity(n_factors);
        ExprEnv::new(0, pat_expr).args(&mut pat_args);

        let mut prz = ProductZipper::new(btm.read_zipper(), (0..(pat_args.len() - 2)).map(|i| {
            btm.read_zipper()
        }));
        prz.reserve_buffers(1 << 32, 32);

        Self::query_multi_raw(&mut prz, &pat_args[1..], effect)
    }

    #[inline]
    unsafe fn read_handler<'trie, 'path>(btm: *const PathMap<()>,
                    mmaps: *mut HashMap<OwnedSourceItem, ArenaCompactTree<memmap2::Mmap>>,
                    z3s: *mut HashMap<OwnedSourceItem, Box<Popen>>,
                    request: ResourceRequest) -> Resource<'trie, 'path> {
        match request {
            ResourceRequest::BTM(prefix) => {
                Resource::BTM(btm.as_ref().unwrap().read_zipper_at_path(prefix))
            }
            ResourceRequest::ACT(name) => {
                let act = mmaps.as_mut().unwrap().entry(OwnedSourceItem::from(name)).or_insert_with(|| {
                    trace!(target: "query_multi_i", "open new ACT {}", name);
                    ArenaCompactTree::open_mmap(format!("{ACT_PATH}{name}.act")).unwrap()
                });
                trace!(target: "query_multi_i", "taking RZ of {}", name);
                Resource::ACT(act.read_zipper())
            }
            ResourceRequest::Z3(instance) => {
                trace!(target: "query_multi_i", "getting z3 instance");
                let mut z3 = z3s.as_mut().unwrap().get_mut(&OwnedSourceItem::from(instance)).unwrap_or_else(|| panic!("non existent z3 {}", instance));
                z3.stdin.as_mut().expect("access to z3 stdin").write_all("(check-sat)\n".as_bytes()).expect("written all");
                z3.stdin.as_mut().expect("access to z3 stdin").write_all("(get-model)\n".as_bytes()).expect("written all");
                z3.stdin.as_mut().expect("access to z3 stdin").flush().expect("flushed all");
                trace!(target: "query_multi_i", "z3 ran (check-sat) and (get-model)");
                let mut v = String::new();
                let mut reader = std::io::BufReader::new(z3.stdout.as_mut().expect("access to z3 stdout"));
                reader.read_line(&mut v).unwrap();
                if &v == "sat\n" {
                    v.clear();
                    let mut last = 0;
                    while &v.as_bytes()[last..] != b")\n" {
                        last = v.as_bytes().len();
                        reader.read_line(&mut v).unwrap();
                    }
                    trace!(target: "query_multi_i", "z3 read '{}'", &v[1..last]);
                    let mut s = Space::new();
                    s.add_all_sexpr(&v.as_bytes()[1..last]);
                    // let mut v_ = Vec::new();
                    // s.dump_all_sexpr(&mut v_);
                    // trace!(target: "query_multi_i", "z3 read '{}'", std::str::from_utf8(&v_[..]).unwrap());
                    let btm = std::mem::take(&mut s.btm);
                    let rz = btm.into_read_zipper(&[]);
                    Resource::Z3(rz)
                } else {
                    trace!(target: "query_multi_i", "z3 problem not sat: {}", v);
                    Resource::Z3(PathMap::new().into_read_zipper(&[]))
                }
            }
        }
    }

    #[inline]
    unsafe fn write_handler<'w, 'a, 'k>(zh_wzs: (*mut ZipperHead<'w, 'a, ()>, *mut Vec<WriteZipperTracked<'a, 'k, ()>>),
                mmaps: *mut HashMap<OwnedSourceItem, ArenaCompactTree<memmap2::Mmap>>,
                z3s: *mut HashMap<OwnedSourceItem, Box<Popen>>,
                request: &WriteResourceRequest) -> WriteResource<'w, 'a, 'k> where 'w : 'a {
        match *request {
            WriteResourceRequest::BTM(p) => {
                let zh = zh_wzs.0.as_mut().unwrap();
                let wzs = zh_wzs.1.as_mut::<'w>().unwrap();
                wzs.push(zh.write_zipper_at_exclusive_path_unchecked(p));
                WriteResource::BTM(wzs.last_mut().unwrap())
            }
            WriteResourceRequest::ACT(f) => {
                WriteResource::ACT(())
            }
            WriteResourceRequest::Z3(f) => {
                let mut cfg = PopenConfig::default();
                cfg.stdin = Redirection::Pipe;
                cfg.stdout = Redirection::Pipe;
                trace!(target: "transform", "retrieving z3 instance");
                let instance = z3s.as_mut().unwrap().entry(OwnedSourceItem::from(f)).or_insert_with(|| {
                    trace!(target: "transform", "creating new z3 popen");
                    // let bpopen = Box::new(Popen::create(&["python", "resources/fake_cli.py", "-in", "-smt2"], cfg).unwrap());
                    let bpopen = Box::new(Popen::create(&["z3", "-in", "-smt2"], cfg).expect("z3: command not found"));
                    trace!(target: "transform", "created new z3 popen");
                    bpopen
                }).as_mut();
                WriteResource::Z3(instance)
            }
        }
    }

    pub fn query_multi_i<F : FnMut(Result<&[u32], BTreeMap<(u8, u8), ExprEnv>>, Expr) -> bool>(no_source: bool,
            mmaps: &mut HashMap<OwnedSourceItem, ArenaCompactTree<memmap2::Mmap>>,
            z3s: &mut HashMap<OwnedSourceItem, Box<Popen>>,
            btm: &PathMap<()>, pat_expr: Expr, mut effect: F) -> usize {
        use crate::sources::{ASource, Resource, ResourceRequest, Source};

        let pat_newvars = pat_expr.newvars();
        trace!(target: "query_multi_i", "pattern (newvars={}) {:?}", pat_newvars, serialize(unsafe { pat_expr.span().as_ref().unwrap() }));
        let n_factors = pat_expr.arity().unwrap() as usize;
        debug_assert!(n_factors > 0);
        if n_factors == 1 {
            effect(Err(BTreeMap::new()), pat_expr);
            return 1;
        }
        let mut pat_args = Vec::with_capacity(n_factors);
        ExprEnv::new(0, pat_expr).args(&mut pat_args);

        trace!(target: "query_multi_i", "z3s {:?}", z3s.keys().collect::<Vec<_>>());
        let mut srcs: Vec<_> = Vec::with_capacity(n_factors);
        let mut factors: Vec<_> = Vec::with_capacity(n_factors);
        for e in pat_args[1..].iter() {
            let mut src = if no_source { ASource::compat(e.subsexpr()) } else { ASource::new(e.subsexpr()) };
            factors.push(src.source(src.request().map(|request| unsafe { Self::read_handler(btm, mmaps, z3s, request) })));
            srcs.push(src);
        }

        match factors.remove(0)  {
            AFactor::CompatSource(primary) => {
                let mut prz = ProductZipper::new(primary, &mut factors[..]);
                prz.reserve_buffers(1 << 32, 32);
                Self::query_multi_raw(&mut prz, &pat_args[1..], effect)
            }
            primary => {
                trace!(target: "query_multi_i", "PZG of {:?}", factors.len() + 1);
                let mut prz = ProductZipperG::new(primary, &mut factors[..]);
                prz.reserve_buffers(1 << 32, 32);
                Self::query_multi_raw(&mut prz, &pat_args[1..], effect)
            }
        }
    }

    #[cfg(feature="no_search")]
    #[inline(always)]
    pub fn query_multi_raw_with_unification_sources<PZ : ZipperProduct, F : FnMut(Result<&[u32], BTreeMap<(u8, u8), ExprEnv>>, Expr) -> bool>(mut prz: &mut PZ, search_sources: &[ExprEnv], unify_sources: &[ExprEnv], mut effect: F) -> usize {
        let _ = search_sources;
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

            let mut pairs = vec![(unify_sources[0], ExprEnv::new(1, e))];

            for (&pa, &other_i) in unify_sources[1..].iter().zip(prz.path_indices()) {
                let fe = ExprEnv::new((pairs.len() + 1) as u8,
                                      Expr { ptr: unsafe { prz.origin_path().as_ptr().cast_mut().add(other_i) } });
                pairs.push((pa, fe))
            }

            // pairs.iter().for_each(|(x, y)| println!("pair {} {}", x.show(), y.show()));

            let bindings = unify(pairs);

            match bindings {
                Ok(bs) => {

                    unsafe { std::ptr::write_volatile(&mut candidate, std::ptr::read_volatile(&candidate) + 1); }
                    if !effect(Err(bs), e) {
                        break
                    }
                }
                Err(failed) => {
                    match failed {
                        UnificationFailure::Occurs(v, e) => {
                            trace!(target: "query_multi", "U {:?} occurs in {}", v, e.show())
                        }
                        UnificationFailure::Difference(lhs, rhs) => {
                            trace!(target: "query_multi", "U {} differs from {}", lhs.show(), rhs.show())
                        }
                        UnificationFailure::MaxIter(iter) => {
                            trace!(target: "query_multi", "U reached max iter {}", iter)
                        }
                    }
                }
            }

        }
       
        candidate
    }

    #[cfg(not(feature="no_search"))]
    #[inline(always)]
    pub fn query_multi_raw_with_unification_sources<PZ : ZipperProduct, F : FnMut(Result<&[u32], BTreeMap<(u8, u8), ExprEnv>>, Expr) -> bool>(mut prz: &mut PZ, search_sources: &[ExprEnv], unify_sources: &[ExprEnv], mut effect: F) -> usize {
        let mut stack = search_sources[0..].iter().rev().cloned().collect::<Vec<_>>();

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
                        let mut pairs = vec![(unify_sources[0], ExprEnv::new(1, e))];

                        for (&pa, &other_i) in unify_sources[1..].iter().zip(loc.path_indices()) {
                            let fe = ExprEnv::new((pairs.len() + 1) as u8,
                                                  Expr { ptr: unsafe { loc.origin_path().as_ptr().cast_mut().add(other_i) } });
                            pairs.push((pa, fe))
                        }

                        // pairs.iter().for_each(|(x, y)| println!("pair {} {}", x.show(), y.show()));

                        let bindings = unify(&mut pairs);

                        match bindings {
                            Ok(bs) => {
                                unsafe { std::ptr::write_volatile(&mut candidate, std::ptr::read_volatile(&candidate) + 1); }
                                if !effect(Err(bs), e) {
                                    unsafe { longjmp(a, 1) }
                                }
                            }
                            Err(failed) => {
                                match failed {
                                    UnificationFailure::Occurs(v, e) => {
                                        trace!(target: "query_multi", "U {:?} occurs in {}", v, e.show())
                                    }
                                    UnificationFailure::Difference(lhs, rhs) => {
                                        trace!(target: "query_multi", "U {} differs from {}", lhs.show(), rhs.show())
                                    }
                                    UnificationFailure::MaxIter(iter) => {
                                        trace!(target: "query_multi", "U reached max iter {}", iter)
                                    }
                                }
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


    /// The identity-sourced form: descend and unify against the same factor list.
    /// The `_with_unification_sources` variant lets a caller descend RENORMALIZED
    /// factors (reordered, variables renumbered) while unifying and keying the
    /// bindings in the ORIGINAL pattern namespace.
    #[inline(always)]
    pub fn query_multi_raw<PZ : ZipperProduct, F : FnMut(Result<&[u32], BTreeMap<(u8, u8), ExprEnv>>, Expr) -> bool>(prz: &mut PZ, sources: &[ExprEnv], effect: F) -> usize {
        Self::query_multi_raw_with_unification_sources(prz, sources, sources, effect)
    }


    fn append_renormalized_query_var(
        out: &mut Vec<u8>,
        var_map: &mut [u8; 64],
        next_var: &mut u8,
        original_var: usize,
    ) -> Option<()> {
        if original_var >= var_map.len() {
            return None;
        }
        match var_map[original_var] {
            u8::MAX => {
                if (*next_var as usize) >= var_map.len() {
                    return None;
                }
                var_map[original_var] = *next_var;
                *next_var += 1;
                out.push(item_byte(Tag::NewVar));
            }
            planned_var => out.push(item_byte(Tag::VarRef(planned_var))),
        }
        Some(())
    }

    fn append_renormalized_query_factor(
        source: ExprEnv,
        var_map: &mut [u8; 64],
        next_var: &mut u8,
        out: &mut Vec<u8>,
    ) -> Option<()> {
        let mut ez = ExprZipper::new(source.subsexpr());
        let mut local_newvars = source.v;
        loop {
            match ez.tag() {
                Tag::NewVar => {
                    Self::append_renormalized_query_var(
                        out,
                        var_map,
                        next_var,
                        local_newvars as usize,
                    )?;
                    local_newvars = local_newvars.checked_add(1)?;
                }
                Tag::VarRef(original_var) => {
                    Self::append_renormalized_query_var(
                        out,
                        var_map,
                        next_var,
                        original_var as usize,
                    )?;
                }
                Tag::SymbolSize(size) => unsafe {
                    out.extend_from_slice(
                        slice_from_raw_parts(ez.root.ptr.byte_add(ez.loc), size as usize + 1)
                            .as_ref()
                            .unwrap(),
                    );
                },
                Tag::Arity(arity) => out.push(item_byte(Tag::Arity(arity))),
            }
            if !ez.next() {
                break;
            }
        }
        Some(())
    }

    /// Re-encodes `sources` in `plan` order with variables renumbered to that order:
    /// the first factor's variables become the leading NewVars and later factors'
    /// shared variables become VarRefs back to them, so a reordered descent keeps
    /// coreference intact. Returns the backing buffers plus the re-based ExprEnvs, or
    /// None when the renumbering does not re-encode (>= 64 distinct variables).
    fn renormalize_query_factors(
        sources: &[ExprEnv],
        plan: &[usize],
    ) -> Option<(Vec<Vec<u8>>, Vec<ExprEnv>)> {
        let mut var_map = [u8::MAX; 64];
        let mut next_var = 0;
        let mut buffers = Vec::with_capacity(plan.len());
        let mut bases = Vec::with_capacity(plan.len());

        for &source_idx in plan {
            let source = sources[source_idx];
            let capacity = unsafe { source.subsexpr().span().as_ref().unwrap().len() };
            let mut buffer = Vec::with_capacity(capacity);
            let base = next_var;
            Self::append_renormalized_query_factor(source, &mut var_map, &mut next_var, &mut buffer)?;
            buffers.push(buffer);
            bases.push(base);
        }

        let planned_sources = buffers
            .iter()
            .zip(bases)
            .map(|(buffer, v)| ExprEnv {
                n: 0,
                v,
                offset: 0,
                base: Expr {
                    ptr: buffer.as_ptr().cast_mut(),
                },
            })
            .collect();
        Some((buffers, planned_sources))
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

    pub fn prefix_subsumption_resources(requests: &[crate::sinks::WriteResourceRequest]) -> Vec<usize> {
        let n = requests.len();
        let mut out = Vec::with_capacity(n);

        for (i, cur) in requests.iter().enumerate() {
            let mut best_idx = i;
            let mut best = cur;

            for (j, cand) in requests.iter().enumerate() {
                if cand.pjoin(&cur).as_ref() == Some(cand) {
                    if cand < best || (cand == best && j < best_idx) {
                        best_idx = j;
                        best = cand;
                    }
                }
            }
            
            out.push(best_idx);
        }

        out
    }

    #[cfg(feature="specialize_io")]
    pub fn transform_multi_multi_(&mut self, pat_expr: Expr, tpl_expr: Expr, add: Expr) -> (usize, bool) {
        // Semi-naive immediate-consequence step (feature `semi_naive_ic`). Inside the
        // IC loop (`sni_rule_seen` is Some) fire the m-delta-rule transform: match each
        // body factor against THIS rule's delta in turn (facts added since it last
        // fired) with the other factors on the full space, and union (the idempotent
        // insert dedups). A first-seen rule has no snapshot, so the cost gate routes it
        // to the naive full match; every later monotone firing costs O(delta) instead
        // of O(dish). Any removal in the loop latches `sni_removal_seen` and the rest
        // of the loop stays naive (the per-rule delta recurrence is only byte-identical
        // to naive while evaluation is add-only). `sni_rule_seen == None` (every
        // non-IC caller, every default build) falls through to the naive match.
        #[cfg(feature = "semi_naive_ic")]
        if let Some(seen) = self.sni_rule_seen.take() {
            if self.sni_force_naive || self.sni_removal_seen {
                self.sni_rule_seen = Some(seen);
            } else if {
                // Give up on loops that never route a firing to the delta: a program
                // that respawns fresh-keyed rules every round (or whose rules the
                // spike guard always rejects) pays per-firing bookkeeping for
                // nothing. 512 firings with zero delta routes disarms the rest of
                // the loop; profitable loops route within their first few firings.
                self.sni_loop_firings += 1;
                self.sni_semi_firings == 0 && self.sni_loop_firings >= 512
            } {
                // disarmed: drop the frontier state, run pure baseline from here on.
            } else {
                let (semi_result, _key) = self.sni_delta_fire(seen, pat_expr, tpl_expr, add);
                if let Some(result) = semi_result {
                    self.sni_semi_firings += 1;
                    return result;
                }
                return self.transform_multi_multi_naive(pat_expr, tpl_expr, add);
            }
        }
        self.transform_multi_multi_naive(pat_expr, tpl_expr, add)
    }

    /// The naive full-space match for a `,`->`,` rule: match the whole body against
    /// `btm` plus the consumed exec and emit every template instantiation. The
    /// unconditional, always-correct path every default caller and every semi-naive
    /// fall-through routes to.
    pub fn transform_multi_multi_naive(&mut self, pat_expr: Expr, tpl_expr: Expr, add: Expr) -> (usize, bool) {
        let mut buffer = Vec::with_capacity(1 << 32);
        unsafe { buffer.set_len(1 << 32); }
        let mut tpl_args = Vec::with_capacity(64);
        ExprEnv::new(0, tpl_expr).args(&mut tpl_args);
        let mut templates: Vec<_> = tpl_args[1..].iter().map(|ee| ee.subsexpr()).collect();
        let mut template_prefixes: Vec<_> = templates.iter().map(|e| unsafe { e.prefix().unwrap_or_else(|x| x).as_ref().unwrap() }).collect();
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

        let mut assignments: Vec<(u8, u8)> = vec![];
        let mut trace: Vec<(u8, u8)> = vec![];
        
        let mut ass = Vec::with_capacity(64);
        let mut astack = Vec::with_capacity(64);

        let mut any_new = false;
        let touched = Self::query_multi(&read_copy, pat_expr, |refs_bindings, loc| 'query:{
            trace!(target: "transform", "data {}", serialize(unsafe { loc.span().as_ref().unwrap()}));
            unsafe { writes += template_prefixes.len(); }
            match refs_bindings {
                Ok(refs) => {
                    unreachable!()
                }
                Err((ref bindings)) => {
                    #[cfg(debug_assertions)]
                    bindings.iter().for_each(|(v, ee)| trace!(target: "transform", "binding {:?} {}", *v, ee.show()));

                    let (mut oi, ni, true) = ({
                        let mut void = std::io::sink();
                        mork_expr::apply_e_clears_stacks_and_cycles_check!(0,0,0,pat_expr,bindings,void,trace,assignments)
                    }) else {break 'query true;};

                    'writes : for (i, template) in templates.iter().enumerate() {
                        let wz = &mut template_wzs[subsumption[i]];

                        trace!(target: "transform", "{i} template {} @ ({oi} {ni})", serialize(unsafe { template.span().as_ref().unwrap()}));


                        buffer.clear();
                        let (toi, _, true) = mork_expr::apply_e_clears_stacks_and_cycles_check!(0,oi,ni,*template,bindings,buffer,astack,ass) else { continue 'writes; };
                        oi = toi;


                        trace!(target: "transform", "U {i} out {:?}", Expr{ ptr: buffer.as_mut_ptr() });
                        wz.move_to_path(&buffer[wz.root_prefix_path().len()..]);
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

    /// Route one firing. Returns `(Some(result), key)` when the m-delta-rule ran and
    /// `(None, key)` when the router chose the naive full match (the caller runs and
    /// measures it). Either way the rule's snapshot is refreshed to this firing's
    /// match input, so the NEXT delta only carries facts added after it, and
    /// `sni_rule_seen` is put back.
    ///
    /// Routing is by MEASURED cost, not a size model: each route's last firing
    /// records its `transitions` (descent steps), and the cheaper route wins. A size
    /// model in fact counts mis-prices narrow-prefix rules (their naive match visits
    /// a small subtrie of a large dish). The measurements bootstrap naive-first
    /// (which also seeds the snapshot), probe semi once when the m*delta < dish
    /// pre-filter allows, and re-probe the losing route every 257th firing so a
    /// workload shift flips the routing back; both routes emit identical facts, so a
    /// probe never changes results. m*delta >= dish (a delta spike, e.g. bulk load)
    /// forces naive regardless of history.
    #[cfg(feature = "semi_naive_ic")]
    fn sni_delta_fire(
        &mut self,
        mut seen: HashMap<Vec<u8>, SniRuleEntry>,
        pat_expr: Expr,
        tpl_expr: Expr,
        add: Expr,
    ) -> (Option<(usize, bool)>, Vec<u8>) {
        // Rule key: pattern bytes then template bytes; stable across the exec
        // re-arming (the wrapper changes round to round, the `,`-body does not).
        let pat_span = unsafe { pat_expr.span().as_ref().unwrap() };
        let tpl_span = unsafe { tpl_expr.span().as_ref().unwrap() };
        let mut key = Vec::with_capacity(pat_span.len() + tpl_span.len() + 1);
        key.extend_from_slice(pat_span);
        key.push(0xff);
        key.extend_from_slice(tpl_span);

        // The rule's match input, built only once the rule recurs: cloning the dish
        // and inserting the consumed exec per firing is pure waste for one-shot
        // (respawned fresh-keyed) rules, which dominate some programs.
        let mut read_copy_lazy: Option<PathMap<()>> = None;
        let mut read_copy = |btm: &PathMap<()>| -> PathMap<()> {
            read_copy_lazy
                .get_or_insert_with(|| {
                    let mut rc = btm.clone();
                    rc.insert(unsafe { add.span().as_ref().unwrap() }, ());
                    rc
                })
                .clone()
        };

        let mut pat_args = Vec::with_capacity(64);
        ExprEnv::new(0, pat_expr).args(&mut pat_args);
        let m = pat_args.len().saturating_sub(1);

        // Cost gate: the m-delta-rule runs m passes of ~O(delta) each versus naive's
        // single ~O(dish) pass, so route to semi only when m * delta < dish. On a
        // FIRST firing the delta IS the dish (m >= 1 pre-determines naive), so skip
        // the subtract and seed the snapshot count from one val_count. On later
        // firings both counts are O(facts changed): `subtract` on COW clones prunes
        // shared subtrees (measured ~5us diffing a 500k-fact clone-plus-one; see
        // tests/subtract_probe.rs), and dish_count = cached + delta - removed stays
        // exact because the IC driver consumes exec facts between firings (the dish
        // is not add-only).
        let (delta, delta_count, dish_count) = match seen.get(&key) {
            // First sighting: the delta IS the dish, so `m >= 1` pre-determines naive;
            // no snapshot exists and none is diffed (the clone starts next firing).
            None => (None, 0, None),
            Some(entry) => {
                let snapshot = &entry.snapshot;
                let rc = read_copy(&self.btm);
                let delta = rc.subtract(snapshot);
                let delta_count = delta.val_count();
                let removed_count = snapshot.subtract(&rc).val_count();
                // The base count pays its one O(dish) walk here, on the rule's
                // first diffed firing -- one-shot rules never do.
                let base = entry.dish_count.unwrap_or_else(|| snapshot.val_count());
                debug_assert!(base + delta_count >= removed_count);
                (Some(delta), delta_count, Some(base + delta_count - removed_count))
            }
        };

        // Deterministic cost gate: the m-delta-rule runs m passes of ~O(delta) each
        // versus naive's single ~O(dish) pass. First firing (no delta) is naive.
        let go_semi = matches!(
            (&delta, dish_count),
            (Some(_), Some(dish)) if m.saturating_mul(delta_count) < dish
        );

        // Bound the frontier map: a program that respawns fresh-keyed rules every
        // round (counter-carrying inner execs) would otherwise accumulate one
        // snapshot per round. Clearing resets every frontier to "first firing"
        // (naive on next fire), which only costs speed, never correctness.
        const SNI_MAX_RULES: usize = 256;
        if seen.len() >= SNI_MAX_RULES && !seen.contains_key(&key) {
            seen.clear();
        }
        let delta_for_fire = if go_semi { delta } else { None };
        // Every rule keeps its frontier: the snapshot IS the semi-naive state.
        seen.insert(
            key.clone(),
            SniRuleEntry { snapshot: read_copy(&self.btm), dish_count },
        );
        self.sni_rule_seen = Some(seen);

        let result = delta_for_fire.map(|delta| {
            let rc = read_copy(&self.btm);
            self.transform_multi_multi_delta(&rc, &delta, pat_expr, tpl_expr)
        });
        (result, key)
    }

    /// The m-delta-rule transform: one pass per body factor j, matching factor j
    /// against the per-rule `delta` and the remaining factors against the full
    /// `read_copy`, emitting exactly as the naive path does (the idempotent insert
    /// dedups the pass overlap). Per pass the factors are REORDERED so the delta
    /// factor drives the descent (the small outer loop) and re-encoded so its
    /// variables become the leading NewVars (`renormalize_query_factors`); the
    /// per-candidate unification still runs over the ORIGINAL sources, so bindings
    /// stay keyed in the pattern's own namespace and the emit below is byte-identical
    /// to the naive path's. A plan whose variables do not re-encode falls back to the
    /// identity order for that pass (correct, only slower).
    #[cfg(feature = "semi_naive_ic")]
    pub fn transform_multi_multi_delta(
        &mut self,
        read_copy: &PathMap<()>,
        delta: &PathMap<()>,
        pat_expr: Expr,
        tpl_expr: Expr,
    ) -> (usize, bool) {
        let mut buffer = Vec::with_capacity(1 << 32);
        unsafe { buffer.set_len(1 << 32); }
        let mut tpl_args = Vec::with_capacity(64);
        ExprEnv::new(0, tpl_expr).args(&mut tpl_args);
        let templates: Vec<_> = tpl_args[1..].iter().map(|ee| ee.subsexpr()).collect();
        let template_prefixes: Vec<_> = templates.iter().map(|e| unsafe { e.prefix().unwrap_or_else(|x| x).as_ref().unwrap() }).collect();
        let mut subsumption = Self::prefix_subsumption(&template_prefixes[..]);
        let mut placements = subsumption.clone();
        let mut zh = self.btm.zipper_head();
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

        let mut assignments: Vec<(u8, u8)> = vec![];
        let mut trace: Vec<(u8, u8)> = vec![];
        let mut ass = Vec::with_capacity(64);
        let mut astack = Vec::with_capacity(64);

        let mut pat_args = Vec::with_capacity(64);
        ExprEnv::new(0, pat_expr).args(&mut pat_args);
        let sources: Vec<ExprEnv> = pat_args[1..].to_vec();
        let n_factors = sources.len();

        let mut any_new = false;
        let mut total_candidates = 0usize;

        for j in 0..n_factors {
            // Pass j only finds matches whose factor-j fact lies in the delta; when
            // the delta holds nothing under that factor's constant prefix the pass
            // is empty, so skip it (the delta is small: the probe is O(delta)). A
            // prefixless factor (variable-headed) never skips.
            {
                let sub = sources[j].subsexpr();
                let pfx = unsafe { sub.prefix().unwrap_or_else(|x| x).as_ref().unwrap() };
                if !pfx.is_empty() && delta.read_zipper_at_path(pfx).val_count() == 0 {
                    continue;
                }
            }

            // Plan: factor j first, the rest in identity order. For j == 0 that IS
            // the identity plan, so skip the re-encode entirely.
            let plan_j: Vec<usize> =
                std::iter::once(j).chain((0..n_factors).filter(|&i| i != j)).collect();

            // (map per PZ position, search sources, unify sources) for this pass.
            let (maps, _search_buffers, search_sources, unify_sources): (
                Vec<&PathMap<()>>,
                Vec<Vec<u8>>,
                Vec<ExprEnv>,
                Vec<ExprEnv>,
            ) = if j == 0 {
                (
                    (0..n_factors).map(|i| if i == j { delta } else { read_copy }).collect(),
                    Vec::new(),
                    sources.clone(),
                    sources.clone(),
                )
            } else {
                match Self::renormalize_query_factors(&sources, &plan_j) {
                    Some((buffers, planned)) => (
                        plan_j.iter().map(|&i| if i == j { delta } else { read_copy }).collect(),
                        buffers,
                        planned,
                        plan_j.iter().map(|&i| sources[i]).collect(),
                    ),
                    None => (
                        // Identity fallback: the delta zipper sits at PZ position j.
                        (0..n_factors).map(|i| if i == j { delta } else { read_copy }).collect(),
                        Vec::new(),
                        sources.clone(),
                        sources.clone(),
                    ),
                }
            };

            let mut prz = ProductZipper::new(
                maps[0].read_zipper(),
                (1..n_factors).map(|k| maps[k].read_zipper()),
            );
            prz.reserve_buffers(1 << 32, 32);

            total_candidates += Self::query_multi_raw_with_unification_sources(
                &mut prz,
                &search_sources,
                &unify_sources,
                |refs_bindings, loc| 'query: {
                    trace!(target: "transform", "delta data {}", serialize(unsafe { loc.span().as_ref().unwrap()}));
                    unsafe { writes += template_prefixes.len(); }
                    match refs_bindings {
                        Ok(_refs) => {
                            unreachable!()
                        }
                        Err(ref bindings) => {
                            #[cfg(debug_assertions)]
                            bindings.iter().for_each(|(v, ee)| trace!(target: "transform", "delta binding {:?} {}", *v, ee.show()));

                            // Per-match seed recompute, exactly as the naive emit: no
                            // caching, so schematic matches can never inherit a stale
                            // ground seed.
                            let (mut oi, ni, true) = ({
                                let mut void = std::io::sink();
                                mork_expr::apply_e_clears_stacks_and_cycles_check!(0,0,0,pat_expr,bindings,void,trace,assignments)
                            }) else { break 'query true; };

                            'writes: for (i, template) in templates.iter().enumerate() {
                                let wz = &mut template_wzs[subsumption[i]];
                                buffer.clear();
                                let (toi, _, true) = mork_expr::apply_e_clears_stacks_and_cycles_check!(0,oi,ni,*template,bindings,buffer,astack,ass) else { continue 'writes; };
                                oi = toi;
                                wz.move_to_path(&buffer[wz.root_prefix_path().len()..]);
                                any_new |= wz.set_val(()).is_none();
                            }
                            true
                        }
                    }
                },
            );
        }

        for wz in template_wzs {
            zh.cleanup_write_zipper(wz);
        }
        (total_candidates, any_new)
    }

    #[cfg(feature="specialize_io")]
    pub fn transform_multi_multi_i(&mut self, pat_expr: Expr, tpl_expr: Expr, add: Expr) -> (usize, bool) {
        let mut buffer = Vec::with_capacity(1 << 32);
        unsafe { buffer.set_len(1 << 32); }
        let mut tpl_args = Vec::with_capacity(64);
        ExprEnv::new(0, tpl_expr).args(&mut tpl_args);
        let mut templates: Vec<_> = tpl_args[1..].iter().map(|ee| ee.subsexpr()).collect();
        let mut template_prefixes: Vec<_> = templates.iter().map(|e| unsafe { e.prefix().unwrap_or_else(|x| x).as_ref().unwrap() }).collect();
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

        let mut assignments: Vec<(u8, u8)> = vec![];
        let mut trace: Vec<(u8, u8)> = vec![];
        
        let mut ass = Vec::with_capacity(64);
        let mut astack = Vec::with_capacity(64);

        let mut any_new = false;
        let touched = Self::query_multi_i(false, &mut self.mmaps, &mut self.z3s, &read_copy, pat_expr, |refs_bindings, _loc| 'query : {
            // trace!(target: "transform", "data {}", serialize(unsafe { loc.span().as_ref().unwrap()}));
            unsafe { writes += template_prefixes.len(); }
            match refs_bindings {
                Ok(refs) => {
                    unreachable!()
                }
                Err((ref bindings)) => {
                    #[cfg(debug_assertions)]
                    bindings.iter().for_each(|(v, ee)| trace!(target: "transform", "binding {:?} {}", *v, ee.show()));

                    let (mut oi, ni, true) = ({
                        let mut void = std::io::sink();
                        mork_expr::apply_e_clears_stacks_and_cycles_check!(0,0,0,pat_expr,bindings,void,trace,assignments)
                    }) else {break 'query true;};

                    'writes : for (i, template) in templates.iter().enumerate() {
                        let wz = &mut template_wzs[subsumption[i]];

                        trace!(target: "transform", "{i} template {} @ ({oi} {ni})", serialize(unsafe { template.span().as_ref().unwrap()}));

                        buffer.clear();
                        let (toi, _, true) = mork_expr::apply_e_clears_stacks_and_cycles_check!(0,oi,ni,*template,bindings,buffer,astack,ass) else { continue 'writes; };
                        oi = toi;


                        trace!(target: "transform", "U {i} out {:?}", Expr{ ptr: buffer.as_mut_ptr() });
                        wz.move_to_path(&buffer[wz.root_prefix_path().len()..]);
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

    #[cfg(feature="specialize_io")]
    pub fn transform_multi_multi_o(&mut self, pat_expr: Expr, tpl_expr: Expr, add: Expr) -> (usize, bool) {
        use crate::sinks::*;
        let mut buffer = Vec::with_capacity(1 << 32);
        unsafe { buffer.set_len(1 << 32); }
        let mut tpl_args = Vec::with_capacity(64);
        ExprEnv::new(0, tpl_expr).args(&mut tpl_args);
        let mut templates: Vec<_> = tpl_args[1..].iter().map(|ee| ee.subsexpr()).collect();
        let mut sinks: Vec<_> = templates.iter().map(|e| ASink::new(*e)).collect();
        // A remove sink makes this loop non-monotone: latch the semi-naive soundness
        // gate (conservatively, on presence) so later `,`->`,` rules route to naive.
        #[cfg(feature = "semi_naive_ic")]
        {
            self.sni_removal_seen |= sinks.iter().any(|s| matches!(s, crate::sinks::ASink::RemoveSink(_)));
        }
        let mut template_prefixes: Vec<_> = sinks.iter().map(|sink|
            sink.request().next().unwrap()
        ).collect();
        let mut subsumption = Self::prefix_subsumption_resources(&template_prefixes[..]);
        let mut placements = subsumption.clone();
        let mut read_copy = self.btm.clone();
        let mut zh = self.btm.zipper_head();
        let zh_ptr = ((&zh) as *const ZipperHead<()>).cast_mut();
        read_copy.insert(unsafe { add.span().as_ref().unwrap() }, ());
        let mut template_resources: Vec<_> = Vec::with_capacity(64);
        let mut outstanding_wzs = Vec::with_capacity(64);
        let outstanding_wzs_ptr = ((&outstanding_wzs) as *const Vec<WriteZipperTracked<()>>).cast_mut();
        let acts_ptr = ((&self.mmaps) as *const HashMap<OwnedSourceItem, _>).cast_mut();
        let z3s_ptr = ((&self.z3s) as *const HashMap<OwnedSourceItem, Box<Popen>>).cast_mut();
        template_prefixes.iter().enumerate().for_each(|(i, request)| {
            if subsumption[i] == i {
                placements[i] = template_resources.len();
                template_resources.push(unsafe { Self::write_handler((zh_ptr, outstanding_wzs_ptr), acts_ptr, z3s_ptr, request) });
            }
        });
        for i in 0..subsumption.len() {
            subsumption[i] = placements[subsumption[i]]
        }
        trace!(target: "transform", "templates {:?}", templates);
        trace!(target: "transform", "prefixes {:?}", template_prefixes);
        trace!(target: "transform", "subsumption {:?}", subsumption);

        let mut assignments: Vec<(u8, u8)> = vec![];
        let mut trace: Vec<(u8, u8)> = vec![];
        
        let mut ass = Vec::with_capacity(64);
        let mut astack = Vec::with_capacity(64);

        let mut any_new = false;
        let touched = Self::query_multi(&read_copy, pat_expr, |refs_bindings, loc| 'query : {
            trace!(target: "transform", "data {}", serialize(unsafe { loc.span().as_ref().unwrap()}));
            unsafe { writes += template_prefixes.len(); }
            match refs_bindings {
                Ok(refs) => {
                    unreachable!()
                }
                Err(ref bindings) => {
                    #[cfg(debug_assertions)]
                    bindings.iter().for_each(|(v, ee)| trace!(target: "transform", "binding {:?} {}", *v, ee.show()));

                    let (mut oi, ni, true) = ({
                        let mut void = std::io::sink();
                        mork_expr::apply_e_clears_stacks_and_cycles_check!(0,0,0,pat_expr,bindings,void,trace,assignments)
                    }) else {break 'query true;};

                    'writes : for (i, template) in templates.iter().enumerate() {
                        let wz = unsafe { std::ptr::read(&template_resources[subsumption[i]]) };

                        trace!(target: "transform", "{i} template {} @ ({oi} {ni})", serialize(unsafe { template.span().as_ref().unwrap()}));

                        buffer.clear();
                        let (toi, _, true) = mork_expr::apply_e_clears_stacks_and_cycles_check!(0,oi,ni,*template,bindings,buffer,astack,ass) else { continue 'writes; };
                        oi = toi;

                        trace!(target: "transform", "U {i} out {:?}", Expr{ ptr: buffer.as_mut_ptr() });
                        sinks[i].sink(std::iter::once(wz), &buffer[..]);
                    }
                    true
                }
            }
        });

        for (i, s) in sinks.iter_mut().enumerate() {
            let wz = unsafe { std::ptr::read(&template_resources[subsumption[i]]) };
            any_new |= s.finalize(std::iter::once(wz));
        }
        for wz in outstanding_wzs.iter_mut() {
            zh.cleanup_write_zipper(wz);
        }

        (touched, any_new)
    }

    pub fn transform_multi_multi_io(&mut self, pat_expr: Expr, tpl_expr: Expr, add: Expr, no_source: bool, no_sink: bool) -> (usize, bool) {
        use crate::sinks::*;
        let mut buffer = Vec::with_capacity(1 << 32);
        unsafe { buffer.set_len(1 << 32); }
        let mut tpl_args = Vec::with_capacity(64);
        ExprEnv::new(0, tpl_expr).args(&mut tpl_args);
        let mut templates: Vec<_> = tpl_args[1..].iter().map(|ee| ee.subsexpr()).collect();
        let mut sinks: Vec<_> = templates.iter().map(|e| { if no_sink { ASink::compat(*e) } else { ASink::new(*e) } }).collect();
        #[cfg(feature = "semi_naive_ic")]
        {
            self.sni_removal_seen |= sinks.iter().any(|s| matches!(s, crate::sinks::ASink::RemoveSink(_)));
        }
        let mut template_prefixes: Vec<_> = sinks.iter().map(|sink|
            sink.request().next().unwrap()
        ).collect();
        let mut subsumption = Self::prefix_subsumption_resources(&template_prefixes[..]);
        let mut placements = subsumption.clone();
        let mut read_copy = self.btm.clone();
        let mut zh = self.btm.zipper_head();
        let zh_ptr = ((&zh) as *const ZipperHead<()>).cast_mut();
        read_copy.insert(unsafe { add.span().as_ref().unwrap() }, ());
        let mut template_resources: Vec<_> = Vec::with_capacity(64);
        let mut outstanding_wzs = Vec::with_capacity(64);
        let outstanding_wzs_ptr = ((&outstanding_wzs) as *const Vec<WriteZipperTracked<()>>).cast_mut();
        let acts_ptr = ((&self.mmaps) as *const HashMap<OwnedSourceItem, _>).cast_mut();
        let z3s_ptr = ((&self.z3s) as *const HashMap<OwnedSourceItem, Box<Popen>>).cast_mut();
        template_prefixes.iter().enumerate().for_each(|(i, request)| {
            if subsumption[i] == i {
                placements[i] = template_resources.len();
                template_resources.push(unsafe { Self::write_handler((zh_ptr, outstanding_wzs_ptr), acts_ptr, z3s_ptr, request) });
            }
        });
        for i in 0..subsumption.len() {
            subsumption[i] = placements[subsumption[i]]
        }
        trace!(target: "transform", "templates {:?}", templates);
        trace!(target: "transform", "prefixes {:?}", template_prefixes);
        trace!(target: "transform", "subsumption {:?}", subsumption);

        let mut assignments: Vec<(u8, u8)> = vec![];
        let mut trace: Vec<(u8, u8)> = vec![];

        let mut ass = Vec::with_capacity(64);
        let mut astack = Vec::with_capacity(64);

        let mut any_new = false;
        let touched = Self::query_multi_i(no_source, &mut self.mmaps, &mut self.z3s, &read_copy, pat_expr, |refs_bindings, loc| 'query : {
            trace!(target: "transform", "data {}", serialize(unsafe { loc.span().as_ref().unwrap()}));
            unsafe { writes += template_prefixes.len(); }
            match refs_bindings {
                Ok(refs) => {
                    unreachable!()
                }
                Err(ref bindings) => {
                    #[cfg(debug_assertions)]
                    bindings.iter().for_each(|(v, ee)| trace!(target: "transform", "binding {:?} {}", *v, ee.show()));

                    let (mut oi, ni, true) = ({
                        let mut void = std::io::sink();
                        mork_expr::apply_e_clears_stacks_and_cycles_check!(0,0,0,pat_expr,bindings,void,trace,assignments)
                    }) else {break 'query true;};

                    'writes : for (i, template) in templates.iter().enumerate() {
                        let wz = unsafe { std::ptr::read(&template_resources[subsumption[i]]) };

                        trace!(target: "transform", "{i} template {} @ ({oi} {ni})", serialize(unsafe { template.span().as_ref().unwrap()}));

                        buffer.clear();
                        let (toi, _, true) = mork_expr::apply_e_clears_stacks_and_cycles_check!(0,oi,ni,*template,bindings,buffer,astack,ass) else { continue 'writes; };

                        trace!(target: "transform", "U {i} out {:?}", Expr{ ptr: buffer.as_mut_ptr() });
                        sinks[i].sink(std::iter::once(wz), &buffer[..]);
                    }
                    true
                }
            }
        });

        for (i, s) in sinks.iter_mut().enumerate() {
            let wz = unsafe { std::ptr::read(&template_resources[subsumption[i]]) };
            any_new |= s.finalize(std::iter::once(wz));
        }
        for wz in outstanding_wzs.iter_mut() {
            zh.cleanup_write_zipper(wz);
        }

        (touched, any_new)
    }
    
    // (exec <loc> (, <src1> <src2> <srcn>)
    //             (, <dst1> <dst2> <dstm>))
    pub fn interpret(&mut self, rt: Expr) -> Result<(), &'static str> {
        #[cfg(feature = "periodic_merkleize")]
        if self.last_merkleize.elapsed().as_secs() > 10 {
            self.btm.merkleize();
            self.last_merkleize = Instant::now()
        }
        debug!(target: "interpret", "interpreting {:?}", serialize(unsafe { rt.span().as_ref().unwrap() }));
        #[cfg(debug_assertions)]
        { let mut rz = self.btm.read_zipper(); while rz.to_next_val() { trace!(target: "interpret", "on space {:?}", serialize(unsafe { rz.path() })); }; drop(rz); }
        destruct!(rt, ("exec" loc pat_expr tpl_expr), unsafe {
            debug_assert!(loc.variables() == 0);
            if let Tag::Arity(i) = byte_item(*pat_expr.ptr) { if i == 0 { return Err("pattern expression can not be empty"); } } else { return Err("pattern must be an expression, not a symbol or variables") }
            if *pat_expr.ptr.add(1) != item_byte(Tag::SymbolSize(1)) { return Err("pattern functor can only be , or I") }

            if let Tag::Arity(i) = byte_item(*tpl_expr.ptr) { if i == 0 { return Err("template expression can not be empty"); } } else { return Err("template must be an expression, not a symbol or variables") }
            if *tpl_expr.ptr.add(1) != item_byte(Tag::SymbolSize(1)) { return Err("template functor can only be , or O") }

            #[cfg(feature="specialize_io")]
            let res = match (*pat_expr.ptr.add(2), *tpl_expr.ptr.add(2)) {
                (b',', b',') => { self.transform_multi_multi_(pat_expr, tpl_expr, rt) }
                (b'I', b',') => { self.transform_multi_multi_i(pat_expr, tpl_expr, rt) }
                (b',', b'O') => { self.transform_multi_multi_o(pat_expr, tpl_expr, rt) }
                (b'I', b'O') => { self.transform_multi_multi_io(pat_expr, tpl_expr, rt, false, false) }
                (_, _) => { return Err("pattern functor can only be , or I and template functor can only be , or O") }
            };
            #[cfg(not(feature="specialize_io"))]
            let res = match (*pat_expr.ptr.add(2), *tpl_expr.ptr.add(2)) {
                (b',', b',') => { self.transform_multi_multi_io(pat_expr, tpl_expr, rt, true, true) }
                (b'I', b',') => { self.transform_multi_multi_io(pat_expr, tpl_expr, rt, false, true) }
                (b',', b'O') => { self.transform_multi_multi_io(pat_expr, tpl_expr, rt, true, false) }
                (b'I', b'O') => { self.transform_multi_multi_io(pat_expr, tpl_expr, rt, false, false) }
                (_, _) => { return Err("pattern functor can only be , or I and template functor can only be , or O") }
            };

            trace!(target: "interpret", "(run, changed) = {:?}", res);
            return Ok(())
        }, _err => return Err("exec shape (exec <loc> <patterns> <templates>)"))
    }

    pub fn metta_calculus(&mut self, steps: usize) -> usize {
        let mut done: usize = 0;
        const PREFIX: [u8; 6] = const { [item_byte(Tag::Arity(4)), item_byte(Tag::SymbolSize(4)), b'e', b'x', b'e', b'c' ] };

        // Arm the semi-naive immediate-consequence delta for the duration of this
        // loop; every `,`->`,` rule then matches only what changed since IT last
        // fired (see `transform_multi_multi_`). Restored on exit so nested and later
        // transform calls stay naive. The default build never arms it.
        #[cfg(feature = "semi_naive_ic")]
        let sni_outer = self.sni_rule_seen.take();
        #[cfg(feature = "semi_naive_ic")]
        {
            self.sni_rule_seen = Some(HashMap::new());
            self.sni_removal_seen = false;
            self.sni_loop_firings = 0;
            self.sni_force_naive = self.sni_force_naive
                || SNI_DISARM.with(|c| c.get())
                || std::env::var("MORK_SNI").as_deref() == Ok("0");
        }

        while {
            let mut rz = self.btm.read_zipper_at_borrowed_path(&PREFIX[..]);
            if rz.to_next_val() {
                // cannot be here `rz` conflicts potentially with zippers(rz.path())
                let mut x: Vec<u8> = rz.into_path(); // should use local buffer
                self.btm.remove(&x[..]);
                let mut xe = Expr{ ptr: x.as_mut_ptr() };
                let start = Instant::now();
                if let Err(e) = self.interpret(xe) {
                    debug!(target: "interpret", "not interpreting: {}", e);
                }
                if self.timing {
                    let start_string = start.elapsed().as_nanos().to_string();
                    let start_str = start_string.as_str();
                    let done_string = done.to_string();
                    let done_str = done_string.as_str();
                    let buf = mork_expr::construct!("timing" xe done_str start_str).unwrap();
                    self.btm.insert(&buf[..], ());
                    trace!(target: "interpret", "interpret took {} ns", start_str);
                }
                done < steps
            } else {
                false
            }
        } { done += 1 }

        #[cfg(feature = "semi_naive_ic")]
        {
            self.sni_rule_seen = sni_outer;
        }

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
        
        let mut stack       : Vec<(u8, u8)>           = Vec::new();
        let mut assignments : Vec<(u8, u8)>           = Vec::new();
        let mut expr_env    : Vec<(ExprEnv, ExprEnv)> = Vec::new();
        while let Some(b) = it.next() {
            rz.descend_to_byte(b);
            
            let mut rzc = rz.clone();
            rzc.to_next_val();
            let e = Expr { ptr: rzc.origin_path().to_vec().leak().as_ptr().cast_mut() };
            if mork_expr::unifiable_reuse_state(e, pattern, &mut expr_env, &mut stack, &mut assignments) {
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

impl Drop for Space {
    fn drop(&mut self) {
        for (_, z3) in self.z3s.iter_mut() {
            // z3.terminate();
            drop(z3.stdin.take())
        }
    }
}
#[cfg(all(test, feature = "semi_naive_ic"))]
mod semi_naive_tests {
    use super::*;
    use std::collections::BTreeSet;

    fn query_pattern_and_sources(space: &mut Space, pattern: &'static str) -> (Expr, Vec<ExprEnv>) {
        let pat_expr = crate::expr!(space, pattern);
        let mut args = Vec::new();
        ExprEnv::new(0, pat_expr).args(&mut args);
        (pat_expr, args[1..].to_vec())
    }

    fn peano_sexpr(x: usize) -> String {
        if x == 0 { "Z".to_string() } else { format!("(S {})", peano_sexpr(x - 1)) }
    }

    fn collect_facts(btm: &PathMap<()>) -> BTreeSet<Vec<u8>> {
        let mut facts = BTreeSet::new();
        let mut rz = btm.read_zipper();
        while rz.to_next_val() {
            facts.insert(rz.origin_path().to_vec());
        }
        facts
    }

    /// Mirrors `metta_calculus`'s exec-taking: pop the first `(exec ...)` fact, if any.
    fn take_first_exec(s: &mut Space, out: &mut Vec<u8>) -> bool {
        const PREFIX: [u8; 6] =
            [item_byte(Tag::Arity(4)), item_byte(Tag::SymbolSize(4)), b'e', b'x', b'e', b'c'];
        let has = {
            let mut rz = s.btm.read_zipper_at_borrowed_path(&PREFIX[..]);
            if rz.to_next_val() {
                *out = rz.into_path();
                true
            } else {
                false
            }
        };
        if has {
            s.btm.remove(&out[..]);
        }
        has
    }

    /// The naive one-step emit set over `btm` (the oracle): the same per-match seed
    /// recompute and template application `transform_multi_multi_naive` performs,
    /// collecting the output paths instead of inserting them.
    fn naive_emit_set(
        space: &mut Space,
        btm: &PathMap<()>,
        body: &'static str,
        template: &'static str,
    ) -> BTreeSet<Vec<u8>> {
        let (pat_expr, _) = query_pattern_and_sources(space, body);
        let (tpl_expr, _) = query_pattern_and_sources(space, template);
        let mut tpl_args = Vec::new();
        ExprEnv::new(0, tpl_expr).args(&mut tpl_args);
        let templates: Vec<Expr> = tpl_args[1..].iter().map(|ee| ee.subsexpr()).collect();
        let mut outputs = BTreeSet::new();
        let mut buffer: Vec<u8> = Vec::with_capacity(1 << 20);
        let mut trace: Vec<(u8, u8)> = vec![];
        let mut assignments: Vec<(u8, u8)> = vec![];
        let mut ass = Vec::with_capacity(64);
        let mut astack = Vec::with_capacity(64);
        Space::query_multi(btm, pat_expr, |refs_bindings, _loc| 'query: {
            let Err(ref bindings) = refs_bindings else { break 'query true; };
            let (mut oi, ni, true) = ({
                let mut void = std::io::sink();
                mork_expr::apply_e_clears_stacks_and_cycles_check!(0, 0, 0, pat_expr, bindings, void, trace, assignments)
            }) else {
                break 'query true;
            };
            for template in templates.iter() {
                buffer.clear();
                let (toi, _, true) = mork_expr::apply_e_clears_stacks_and_cycles_check!(0, oi, ni, *template, bindings, buffer, astack, ass) else {
                    continue;
                };
                oi = toi;
                outputs.insert(buffer.clone());
            }
            true
        });
        outputs
    }

    /// The m-delta-rule emit set: the facts `transform_multi_multi_delta` writes into
    /// a space initialized to `post` (the full post-step space), given `delta`.
    fn delta_emit_set(
        post: &PathMap<()>,
        delta: &PathMap<()>,
        pat_expr: Expr,
        tpl_expr: Expr,
    ) -> BTreeSet<Vec<u8>> {
        let mut space = Space::new();
        space.btm = post.clone();
        let read_copy = space.btm.clone();
        let before = space.btm.clone();
        space.transform_multi_multi_delta(&read_copy, delta, pat_expr, tpl_expr);
        collect_facts(&space.btm.subtract(&before))
    }

    /// (post-step space, pre-step space, delta) from sexpr blocks.
    fn build_step_spaces(base: &[u8], added: &[u8]) -> (PathMap<()>, PathMap<()>, PathMap<()>) {
        let mut pre = Space::new();
        pre.add_all_sexpr(base).unwrap();
        let pre_btm = pre.btm.clone();

        let mut post = Space::new();
        post.add_all_sexpr(base).unwrap();
        post.add_all_sexpr(added).unwrap();
        let post_btm = post.btm.clone();

        let delta = post_btm.subtract(&pre_btm);
        (post_btm, pre_btm, delta)
    }

    /// The core m-delta-rule invariant on one body, asserted two ways:
    ///   (soundness)   delta_emit is a subset of naive(post)
    ///   (semi-naive)  delta_emit + naive(pre) == naive(post)
    /// With injective template instantiation (`exact_difference`) the stronger form
    /// also holds: delta_emit == naive(post) \ naive(pre).
    fn assert_m_delta_invariant(
        base: &[u8],
        added: &[u8],
        body: &'static str,
        template: &'static str,
        exact_difference: bool,
    ) {
        let (post, pre, delta) = build_step_spaces(base, added);

        let mut space = Space::new();
        let (pat_expr, _) = query_pattern_and_sources(&mut space, body);
        let (tpl_expr, _) = query_pattern_and_sources(&mut space, template);

        let naive_pre = naive_emit_set(&mut space, &pre, body, template);
        let naive_post = naive_emit_set(&mut space, &post, body, template);
        let delta_out = delta_emit_set(&post, &delta, pat_expr, tpl_expr);

        assert!(
            delta_out.is_subset(&naive_post),
            "delta-rule emitted a fact the naive full match does not"
        );
        let recovered: BTreeSet<Vec<u8>> = delta_out.union(&naive_pre).cloned().collect();
        assert_eq!(recovered, naive_post, "delta_emit + naive(pre) must equal naive(post)");
        if exact_difference {
            let naive_new: BTreeSet<Vec<u8>> =
                naive_post.difference(&naive_pre).cloned().collect();
            assert_eq!(delta_out, naive_new, "with injective output, delta_emit == naive(post) \\ naive(pre)");
        }
    }

    #[test]
    fn m_delta_rule_per_step_invariant_ground() {
        let base = br#"
(path a b)
(path b c)
(path c d)
"#;
        let added = b"(path d e)\n";
        assert_m_delta_invariant(base, added, "[3] , [3] path $ $ [3] path _2 $", "[2] , [3] path _1 _3", false);
        assert_m_delta_invariant(base, added, "[3] , [3] path $ $ [3] path _2 $", "[2] , [3] reach _1 _3", true);
        assert_m_delta_invariant(
            base,
            added,
            "[4] , [3] path $ $ [3] path _2 $ [3] path _3 $",
            "[2] , [3] tri _1 _4",
            true,
        );
    }

    #[test]
    fn m_delta_rule_per_step_invariant_schematic() {
        // Variable-bearing receiver joined with a message on shared channel+payload:
        // real unification on the delta-restricted factor, both factors over the
        // mutated relation so the m-delta-rule loops both.
        let base = br#"
(petri (? chan one (done one)))
(petri (! chan one))
"#;
        let added = br#"
(petri (? other ($v) (got $v)))
(petri (! other (Z)))
"#;
        assert_m_delta_invariant(
            base,
            added,
            "[3] , [2] petri [4] ? $ $ $ [2] petri [3] ! _1 _2",
            "[2] , [2] petri _3",
            false,
        );
    }

    #[test]
    fn m_delta_rule_preserves_free_data_vars_in_split_templates() {
        // A single-factor body over a schematic fact whose second component carries a
        // FREE data variable plus a back-reference, split by two templates: pins the
        // split emit byte-for-byte against the naive full match.
        let base = br#"
(petri (| (msg a) (recv a)))
"#;
        let added = br#"
(petri (| (! chan pay) (? chan $a (send (S $a)))))
"#;
        assert_m_delta_invariant(
            base,
            added,
            "[2] , [2] petri [3] | $ $",
            "[3] , [2] petri _1 [2] petri _2",
            false,
        );
    }

    fn process_calculus_setup_sexpr(steps: usize, x: usize, y: usize) -> String {
        format!(
            r#"
(exec (IC 0 1 {})
               (, (exec (IC $x $y (S $c)) $sp $st)
                  ((exec $x) $p $t))
               (, (exec (IC $y $x $c) $sp $st)
                  (exec (R $x) $p $t)))

((exec 0)
      (, (petri (? $channel $payload $body))
         (petri (! $channel $payload)) )
      (, (petri $body)))
((exec 1)
      (, (petri (| $lprocess $rprocess)))
      (, (petri $lprocess)
         (petri $rprocess)))

(petri (? (add $ret) ((S $x) $y) (| (! (add (PN $x $y)) ($x $y))
                                    (? (PN $x $y) $z (! $ret (S $z)))  )  ))
(petri (? (add $ret) (Z $y) (! $ret $y)))
(petri (! (add result) ({} {})))
    "#,
            peano_sexpr(steps),
            peano_sexpr(x),
            peano_sexpr(y)
        )
    }

    fn build(setup: &str) -> Space {
        let mut s = Space::new();
        let pat = crate::expr!(s, "$");
        let tpl = crate::expr!(s, "_1");
        s.add_sexpr(setup.as_bytes(), pat, tpl).unwrap();
        s
    }

    /// The IC loop with the delta hook inert (`sni_rule_seen` stays None): the
    /// feature-off reference, driven by hand.
    fn run_naive(setup: &str) -> Space {
        let mut s = build(setup);
        let mut exec_path = Vec::new();
        while take_first_exec(&mut s, &mut exec_path) {
            let xe = Expr { ptr: exec_path.as_mut_ptr() };
            let _ = s.interpret(xe);
            debug_assert!(s.sni_rule_seen.is_none());
        }
        s
    }

    fn project_result(s: &mut Space) -> String {
        let pat = crate::expr!(s, "[2] petri [3] ! result $");
        let tpl = crate::expr!(s, "_1");
        let mut v = Vec::new();
        s.dump_sexpr(pat, tpl, &mut v);
        String::from_utf8_lossy(&v).into_owned()
    }

    /// The load-bearing end-to-end oracle: the full process_calculus IC loop run
    /// naive (hand-driven, delta inert) and semi-naive (`metta_calculus`, which arms
    /// the per-rule deltas) must produce a BYTE-IDENTICAL final dish, and both must
    /// land peano(x+y) on the result channel.
    #[test]
    fn metta_calculus_semi_naive_matches_naive() {
        for (x, y) in [(8usize, 8usize), (16, 16)] {
            let setup = process_calculus_setup_sexpr(100, x, y);
            let mut naive = run_naive(&setup);
            let mut semi = build(&setup);
            semi.metta_calculus(1_000_000_000_000_000);
            // Engagement: byte-identity alone would also pass if the router never
            // chose the delta; require that it actually fired.
            assert!(
                semi.sni_semi_firings > 0,
                "x={x} y={y}: the measured-cost router never routed a firing to the delta"
            );

            let mut nv = Vec::new();
            naive.dump_all_sexpr(&mut nv).unwrap();
            let mut sv = Vec::new();
            semi.dump_all_sexpr(&mut sv).unwrap();
            assert_eq!(
                String::from_utf8_lossy(&nv),
                String::from_utf8_lossy(&sv),
                "process_calculus x={x} y={y}: semi-naive IC loop must be byte-identical to naive"
            );

            let want = format!("{}\n", peano_sexpr(x + y));
            assert_eq!(project_result(&mut naive), want);
            assert_eq!(project_result(&mut semi), want);
        }
    }

    /// Per-step oracle: drive the naive loop and an armed semi loop in lockstep and
    /// compare the whole dish after EVERY exec step, so a divergence is pinned to the
    /// first step that produced it, with the offending facts and raw byte layouts.
    #[test]
    fn semi_naive_ic_lockstep_with_naive_per_step() {
        for (x, y) in [(3usize, 3usize), (8, 8)] {
            let setup = process_calculus_setup_sexpr(100, x, y);
            let mut naive = build(&setup);
            let mut semi = build(&setup);
            // Arm the semi space exactly as metta_calculus does for its loop.
            semi.sni_rule_seen = Some(HashMap::new());
            semi.sni_removal_seen = false;

            let mut exec_path = Vec::new();
            let mut step = 0usize;
            loop {
                step += 1;
                let n_has = take_first_exec(&mut naive, &mut exec_path);
                if n_has {
                    let xe = Expr { ptr: exec_path.as_mut_ptr() };
                    let _ = naive.interpret(xe);
                }
                let s_has = take_first_exec(&mut semi, &mut exec_path);
                if s_has {
                    let xe = Expr { ptr: exec_path.as_mut_ptr() };
                    let _ = semi.interpret(xe);
                }
                assert_eq!(n_has, s_has, "x={x} y={y} step {step}: one loop ran dry first");
                let mut nv = Vec::new();
                naive.dump_all_sexpr(&mut nv).unwrap();
                let mut sv = Vec::new();
                semi.dump_all_sexpr(&mut sv).unwrap();
                if nv != sv {
                    let ns: BTreeSet<String> =
                        String::from_utf8_lossy(&nv).lines().map(|l| l.to_string()).collect();
                    let ss: BTreeSet<String> =
                        String::from_utf8_lossy(&sv).lines().map(|l| l.to_string()).collect();
                    let only_n: Vec<String> = ns.difference(&ss).take(4).cloned().collect();
                    let only_s: Vec<String> = ss.difference(&ns).take(4).cloned().collect();
                    let mut raw = String::new();
                    raw.push_str(&format!("exec: {:02x?}\n", &exec_path[..]));
                    for (label, space) in [("naive", &naive), ("semi", &semi)] {
                        let mut rz = space.btm.read_zipper();
                        while rz.to_next_val() {
                            let p = rz.origin_path();
                            let shown = serialize(p);
                            if only_n.iter().any(|l| *l == shown) || only_s.iter().any(|l| *l == shown) {
                                raw.push_str(&format!("{label} {shown}\n  = {p:02x?}\n"));
                            }
                        }
                    }
                    panic!(
                        "x={x} y={y}: first divergence at step {step}\nonly naive:\n  {}\nonly semi:\n  {}\n{raw}",
                        only_n.join("\n  "),
                        only_s.join("\n  ")
                    );
                }
                if !n_has {
                    break;
                }
            }
        }
    }

    /// An `O (- ...)` removal inside the loop makes evaluation non-monotone; the
    /// soundness gate must latch and every later `,`->`,` rule route to naive, so
    /// the loop stays byte-identical to the hand-driven naive one.
    #[test]
    fn removal_latches_the_soundness_gate() {
        fn setup() -> Space {
            let mut s = Space::new();
            s.add_all_sexpr(
                br#"
(fact a)
(fact b)
(kill a)
(exec 0 (, (kill $x)) (O (- (fact $x))))
(exec 1 (, (fact $x)) (, (copy $x)))
"#,
            )
            .unwrap();
            s
        }
        let mut naive = setup();
        let mut exec_path = Vec::new();
        while take_first_exec(&mut naive, &mut exec_path) {
            let xe = Expr { ptr: exec_path.as_mut_ptr() };
            let _ = naive.interpret(xe);
        }

        let mut semi = setup();
        semi.metta_calculus(1_000_000);
        assert!(semi.sni_removal_seen, "the O(-) removal must latch the soundness gate");

        let mut nv = Vec::new();
        naive.dump_all_sexpr(&mut nv).unwrap();
        let mut sv = Vec::new();
        semi.dump_all_sexpr(&mut sv).unwrap();
        assert_eq!(String::from_utf8_lossy(&nv), String::from_utf8_lossy(&sv));
    }

    /// Regression guard for the use-after-realloc in `coreferential_transition`'s
    /// VarRef recheck: the bound subterm pointed into the ProductZipper path buffer
    /// and the recursion below realloc'd it on deep terms (peano(1000) IC counter
    /// plus the add(n,n) cascade at n=175 pushes past the reserved capacity).
    /// Pre-fix this panicked (`byte_item` "reserved"); post-fix both loops are
    /// byte-identical.
    #[test]
    fn coreferential_recheck_survives_path_buffer_realloc_on_deep_terms() {
        std::thread::Builder::new()
            .stack_size(1 << 31)
            .spawn(|| {
                let n = 175usize;
                let setup = process_calculus_setup_sexpr(1000, n, n);
                let mut naive = run_naive(&setup);
                let mut semi = build(&setup);
                semi.metta_calculus(1_000_000_000_000_000);
                let mut nv = Vec::new();
                naive.dump_all_sexpr(&mut nv).unwrap();
                let mut sv = Vec::new();
                semi.dump_all_sexpr(&mut sv).unwrap();
                assert_eq!(nv, sv, "deep-term IC loop must stay byte-identical");
            })
            .unwrap()
            .join()
            .unwrap();
    }
}
