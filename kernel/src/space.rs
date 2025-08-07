use core::assert_eq;
use core::result::Result::{Err, Ok};
use std::io::{BufRead, Write};
use std::{process, usize};
use std::collections::BTreeMap;
use std::fs::File;
use std::sync::{Arc, Mutex};

use mork_bytestring::{byte_item, Expr, OwnedExpr, ExprZipper, ExprTrait, serialize, Tag, ExprEnv, unify, apply};
use mork_frontend::bytestring_parser::{Parser, ParserError, ParserErrorType, ParseContext};
use bucket_map::{WritePermit, SharedMapping, SharedMappingHandle};
use pathmap::PathMap;
use pathmap::utils::{BitMask, ByteMask};
use pathmap::zipper::*;
use log::*;

pub use crate::space_temporary::{
    PathCount,
    NodeCount,
    AttributeCount,
    SExprCount,
    Space,
    PermissionArb,
    PathPermissionErr,
    SpaceReaderZipper,
};
use crate::{space_temporary, SpaceWriterZipper};

/// A default minimalist implementation of [Space]
pub struct DefaultSpace {
    /// The [PathMap] containing everything in the space
    pub map: Arc<ZipperHeadOwned<()>>,
    /// Guards access to create new permissions, so we can ensure high level operations
    /// that involve exchanging permissions are atomic
    permission_guard: Mutex<()>,
    /// A global symbol table
    sm: SharedMappingHandle,
}

impl DefaultSpace {
    /// Creates a new empty `DefaultSpace`
    pub fn new() -> Self {
        Self {
            map: Arc::new(PathMap::new().into_zipper_head([])),
            permission_guard: Mutex::new(()),
            sm: SharedMapping::new(),
        }
    }
}

/// Read Permission object in a [DefaultSpace]
pub struct DefaultSpaceReader<'space>(ReadZipperTracked<'space, 'static, ()>);

/// Write Permission object in a [DefaultSpace]
pub struct DefaultSpaceWriter<'space> {
    z: WriteZipperTracked<'space, 'static, ()>,
    zh: Arc<ZipperHeadOwned<()>>,
}

/// PermissionHead object for [DefaultSpace]
pub struct DefaultPermissionHead<'space>(&'space DefaultSpace);

impl<'space> PermissionArb<'space, DefaultSpace> for DefaultPermissionHead<'space> {
    fn new_reader(&self, path: &[u8], _auth: &()) -> Result<DefaultSpaceReader<'space>, DefaultPermissionErr> {
        let reader = DefaultSpaceReader(self.0.map.read_zipper_at_path(path).map_err(|e| {
            DefaultPermissionErr {
                message: format!("Conflict trying to acquire read zipper at {path:?}, {e}"),
                path: path.to_vec()
            }
        })?);
        Ok(reader)
    }

    /// Requests a new [Space::Writer] from the `Space`
    fn new_writer(&self, path: &[u8], _auth: &()) -> Result<DefaultSpaceWriter<'space>, DefaultPermissionErr> {
        let writer = DefaultSpaceWriter {
            z: self.0.map.write_zipper_at_exclusive_path(path).map_err(|e| {
                DefaultPermissionErr {
                    message: format!("Conflict trying to acquire write zipper at {path:?}, {e}"),
                    path: path.to_vec()
                }
            })?,
            zh: self.0.map.clone(),
        };
        Ok(writer)
    }
}

/// [PathPermissionErr] in a [DefaultSpace]
#[derive(Debug)]
pub struct DefaultPermissionErr {
    path: Vec<u8>,
    message: String,
}

impl PathPermissionErr for DefaultPermissionErr {
    fn path(&self) -> &[u8] {
        &self.path
    }
}

impl core::fmt::Display for DefaultPermissionErr {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        self.message.fmt(f)
    }
}

impl From<DefaultPermissionErr> for String {
    fn from(perm_err: DefaultPermissionErr) -> Self {
        perm_err.message
    }
}

impl Space for DefaultSpace {
    type Auth = ();
    type Reader<'space> = DefaultSpaceReader<'space>;
    type Writer<'space> = DefaultSpaceWriter<'space>;
    type PermissionHead<'space> = DefaultPermissionHead<'space>;
    type PermissionErr = DefaultPermissionErr;

    fn new_multiple<'space, F: FnOnce(&Self::PermissionHead<'space>)->Result<(), Self::PermissionErr>>(&'space self, f: F) -> Result<(), Self::PermissionErr> {
        let guard = self.permission_guard.lock().unwrap();
        let perm_head = DefaultPermissionHead(self);
        f(&perm_head)?;
        drop(guard);
        Ok(())
    }

    fn cleanup_write_zipper(&self, _wz: impl ZipperMoving + ZipperWriting<()> + ZipperForking<()> + ZipperAbsolutePath) {
        //No-op for DefaultSpace, because the permission *is* the zipper
    }
    fn read_zipper<'r, 's: 'r>(&'s self, reader: &'r mut Self::Reader<'s>) -> impl SpaceReaderZipper<'s> {
        reader.0.reset();
        &mut reader.0
    }
    fn write_zipper<'w, 's: 'w>(&'s self, writer: &'w mut Self::Writer<'s>) -> impl SpaceWriterZipper + 'w {
        writer.z.reset();
        &mut writer.z
    }
    fn symbol_table(&self) -> &SharedMappingHandle {
        &self.sm
    }
}

impl Drop for DefaultSpaceWriter<'_> {
    fn drop(&mut self) {
        self.zh.cleanup_write_zipper(&mut self.z);
    }
}

const SIZES: [u64; 4] = {
    use mork_bytestring::Tag;

    let mut ret = [0u64; 4];
    let mut size = 1;
    while size < 64 {
        let k = Tag::SymbolSize(size).byte();
        ret[((k & 0b11000000) >> 6) as usize] |= 1u64 << (k & 0b00111111);
        size += 1;
    }
    ret
};
const ARITIES: [u64; 4] = {
    use mork_bytestring::Tag;

    let mut ret = [0u64; 4];
    let mut arity = 1;
    while arity < 64 {
        let k = Tag::Arity(arity).byte();
        ret[((k & 0b11000000) >> 6) as usize] |= 1u64 << (k & 0b00111111);
        arity += 1;
    }
    ret
};
const VARS: [u64; 4] = {
    use mork_bytestring::Tag;

    let mut ret = [0u64; 4];
    let nv_byte = Tag::NewVar.byte();
    ret[((nv_byte & 0b11000000) >> 6) as usize] |= 1u64 << (nv_byte & 0b00111111);
    let mut size = 0;
    while size < 64 {
        let k = Tag::VarRef(size).byte();
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

fn show_stack<R:AsRef<[u8]>>(s: R) -> String {
    s.as_ref().iter().copied().map(label).reduce(|mut x, y| {
        x.push(' ');
        x.push_str(y.as_str());
        x
    }).unwrap()
}

fn referential_transition<Z : ZipperMoving + Zipper + ZipperAbsolutePath, F: FnMut(&[ExprEnv], u8, &mut Z) -> ()>(mut last: *mut u8, loc: &mut Z, references: &mut Vec<ExprEnv>, introduced: u8, f: &mut F) {
    unsafe {
    macro_rules! unroll {
    (ACTION $recursive:expr) => {
        trace!(target: "transition", "introduced {} in {}", introduced, serialize(loc.origin_path()));
        f(&references[..], introduced, loc);
    };
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
                referential_transition(last, loc, references, introduced, f);
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
          referential_transition(last, loc, references, introduced, f);
        } else {
            for _ in 0..arity-1 {
                last = last.offset(1);
                *last = ITER_EXPR;
            }
            unroll!(ITER_EXPR referential_transition(last, loc, references, introduced, f));

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
                    referential_transition(last, loc, references, introduced, f);
                    last = last.offset(-1);
                    last = last.offset(-1);
                    last = last.offset(1); *last = lastv;
                }
                loc.ascend_byte();
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
                let intro = if matches!(byte_item(b), Tag::NewVar) {
                    introduced + 1
                } else { introduced };
                referential_transition(last, loc, references, intro, f);
            }
            loc.ascend_byte();
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
                    referential_transition(last, loc, references, introduced, f);
                    last = last.offset(-1);
                    last = last.offset(-1);
                    last = last.offset(1); *last = lastv;
                }
                loc.ascend_byte();
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

        if loc.descend_to_byte(Tag::SymbolSize(size).byte()) {
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

        if loc.descend_to_byte(Tag::SymbolSize(size).byte()) {
            if loc.descend_to(&v[..size as usize]) {
                referential_transition(last, loc, references, introduced, f);
            }
            loc.ascend(size as usize);
        }
        loc.ascend_byte();
        for i in 0..size { last = last.offset(1); *last = *v.get_unchecked((size - i - 1) as usize) }
        last = last.offset(1); *last = size;
    };
    (ITER_ARITY $recursive:expr) => {
        let arity = *last; last = last.offset(-1);
        if loc.descend_to_byte(Tag::Arity(arity).byte()) {
            referential_transition(last, loc, references, introduced, f);
        }
        loc.ascend_byte();
        last = last.offset(1); *last = arity;
    };
    (ITER_VAR_ARITY $recursive:expr) => {
        let arity = *last; last = last.offset(-1);

        unroll!(ITER_VARIABLES $recursive);

        if loc.descend_to_byte(Tag::Arity(arity).byte()) {
            referential_transition(last, loc, references, introduced, f);
        }
        loc.ascend_byte();
        last = last.offset(1); *last = arity;
    };
    (BEGIN_RANGE $recursive:expr) => {
        // references.push((loc.path().len() as u32, 0));
        let p = loc.origin_path();
        references.push(ExprEnv { n: 0, v: introduced, offset: p.len() as u32, base: Expr{ ptr: p.as_ptr().cast_mut() } });
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
        let subexpr = references[index as usize].subsexpr();
        let mut ez = ExprZipper::new(subexpr);
        let v0 = last;
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
    #[cfg(debug_assertions)]
    unroll!(CALL referential_transition(last, loc, references, introduced, f));
    #[cfg(not(debug_assertions))]
    unroll!(CALL unroll!(CALL referential_transition(last, loc, references, introduced, f)));
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
            // likely wrong, what happens if `from` lies inside of a symbol?
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
        use mork_bytestring::Tag;

        let token = self.pdp.tokenizer(s.into().as_bytes());
        let path = if token.len() == 0 { vec![Tag::Arity(0).byte()] } else {
        let mut p = vec![Tag::SymbolSize(token.len() as u8).byte()];
        p.extend(token); p };
        self.wz.descend_to(&path[..]);
        self.wz.set_val(());
        self.wz.ascend(path.len());
    }
}
impl <'a, 'c, WZ> crate::json_parser::Transcriber for SpaceTranscriber<'a, 'c, WZ> where WZ : Zipper + ZipperMoving + ZipperWriting<()> {
    #[inline(always)] fn descend_index(&mut self, i: usize, first: bool) -> () {
        use mork_bytestring::Tag;

        if first { self.wz.descend_to(&[Tag::Arity(2).byte()]); }
        let token = self.pdp.tokenizer(i.to_string().as_bytes());
        self.wz.descend_to(&[Tag::SymbolSize(token.len() as u8).byte()]);
        self.wz.descend_to(token);
    }
    #[inline(always)] fn ascend_index(&mut self, i: usize, last: bool) -> () {
        self.wz.ascend(self.pdp.tokenizer(i.to_string().as_bytes()).len() + 1);
        if last { self.wz.ascend(1); }
    }
    #[inline(always)] fn write_empty_array(&mut self) -> () { self.write("[]"); self.path_count += 1; }
    #[inline(always)] fn descend_key(&mut self, k: &str, first: bool) -> () {
        use mork_bytestring::Tag;

        if first { self.wz.descend_to(&[Tag::Arity(2).byte()]); }
        let token = self.pdp.tokenizer(k.to_string().as_bytes());
        // let token = k.to_string();
        self.wz.descend_to(&[Tag::SymbolSize(token.len() as u8).byte()]);
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
    ($space:expr, $s:literal) => {{
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

impl DefaultSpace {

    pub fn statistics(&self) {
        println!("val count {}", self.map.read_zipper_at_borrowed_path(&[]).unwrap().val_count());
    }

    pub fn load_csv_simple<SrcStream: BufRead>(&mut self, src: SrcStream, pattern: Expr, template: Expr, seperator: u8, include_line_nums: bool) -> Result<usize, String> {
        let mut writer = self.new_writer(unsafe { &*template.prefix().unwrap_or(template.span()) }, &())?;
        self.load_csv(src, pattern, template, &mut writer, seperator, include_line_nums).map_err(|e| format!("{:?}",e))
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
                    wz.set_val(());
                    wz.reset();
                    i += 1;
                }
            }
            Err(e) => { return Err(format!("{:?}", e)) }
        }

        Ok(i)
    }
     */
}

/// Validates the format of an MM2 expression, and extracts the patterns and templates from it
fn destructure_exec_expr<S: Space>(space: &S, rt: Expr) -> Result<PatternsTemplatesExprs, ExecSyntaxError> {
    let mut rtz = ExprZipper::new(rt);

    // ////////////////////////////////////////////////////////////////////
    // Overall format and `exec` keyword
    // //////////////////////////////////////////////////////////////////

    //Make sure the expression is an arity-4
    if rtz.item() != Ok(Tag::Arity(4)) {
        return Err(ExecSyntaxError::ExpectedArity4(mork_bytestring::serialize(unsafe { rt.span().as_ref().unwrap() })));
    }
    assert!(rtz.next());

    //Check for the "exec" keyword, and step over it if we find it
    if unsafe{ rtz.subexpr().span().as_ref().unwrap() != expr!(space, "exec").span().as_ref().unwrap() } {
        return Err(ExecSyntaxError::ExpectedExecKeyword(mork_bytestring::serialize(unsafe { rt.span().as_ref().unwrap() })));
    }
    assert!(rtz.next());

    // ////////////////////////////////////////////////////////////////////
    // Validate (<thread_id>, <priority>)
    // //////////////////////////////////////////////////////////////////

    '_loc_priority_sub_expr : {
        let mut sub_ez = ExprZipper::new(rtz.subexpr());

        //Check for the (<thread_id> <priority>) pair.
        if sub_ez.item() != Ok(Tag::Arity(2)) {
            return Err(ExecSyntaxError::ExpectedThreadIdPair(mork_bytestring::serialize(unsafe { rt.span().as_ref().unwrap() })));
        }
        assert!(rtz.next());

        //Check <thread_id>.  Currently we only accept a grounded `thread_id` as the first arg,
        // although this may change in the future
        if !rtz.subexpr().is_ground() {
            return Err(ExecSyntaxError::ExpectedGroundThreadId(mork_bytestring::serialize(unsafe { rt.span().as_ref().unwrap() })));
        }
        assert!(sub_ez.next_child());

        //Check <priority> is grounded
        if !sub_ez.subexpr().is_ground() {
            return Err(ExecSyntaxError::ExpectedGroundPriority(mork_bytestring::serialize(unsafe { rt.span().as_ref().unwrap() })));
        }
    }
    assert!(rtz.next_child());

    // ////////////////////////////////////////////////////////////////////
    // Lists of patterns, and templates
    // //////////////////////////////////////////////////////////////////

    let comma_list_check = |e| {
        let mut ez = ExprZipper::new(e);
        let Ok(Tag::Arity(_)) = ez.item() else { return Err(()); };
        ez.next();

        let comma = unsafe { expr!(space, ",").span().as_ref().unwrap() };
        if unsafe { ez.subexpr().span().as_ref().unwrap() } != comma {
            return Err(());
        } else { Ok(()) }
    };

    // (, ..$patterns)
    let srcs = rtz.subexpr();
    comma_list_check(srcs).map_err(|_|ExecSyntaxError::ExpectedCommaListPatterns(mork_bytestring::serialize(unsafe { rtz.root.span().as_ref().unwrap() })))?;
    assert!(rtz.next_child());

    // (, ..$templates)
    let dsts = rtz.subexpr();
    comma_list_check(srcs).map_err(|_|ExecSyntaxError::ExpectedCommaListTemplates(mork_bytestring::serialize(unsafe { rtz.root.span().as_ref().unwrap() })))?;

    Ok(PatternsTemplatesExprs::new(srcs, dsts))
}

impl DefaultSpace {
    pub fn metta_calculus_simple(&mut self, thread_id_sexpr_str: &str) -> Result<(), String> {

        //GOAT, MM2-Syntax.  we need to lift these patterns out as constants so we can tweak the MM2 syntax without hunting through the implementation
        let status_loc_sexpr = format!("(exec {})", thread_id_sexpr_str);
        let status_loc = <_>::sexpr_to_expr(self, &status_loc_sexpr).unwrap();

        let Ok(status_writer) = self.new_writer(status_loc.as_bytes(), &()) else {
            return Err("Thread is already running at that loacation.".to_string())
        };

        self.metta_calculus(thread_id_sexpr_str, usize::MAX, &())
            .map_err(|exec_err| format!("{exec_err:?}"))?;

        drop(status_writer);
        Ok(())
    }
}

pub(crate) fn metta_calculus_impl<'s, S: Space>(
    space: &'s S, 
    thread_id_sexpr_str: &str, 
    max_retries: usize, 
    step_cnt: usize, 
    auth: &S::Auth,
) -> Result<(), ExecError<S>> {
    // Remy (2025/07/11) : if this ends up being the only caller we should inline it.
    metta_calculus::metta_calculus_impl_statemachine_poc(space, thread_id_sexpr_str, max_retries, step_cnt, auth)
}

pub(crate) fn load_csv_impl<'s, SrcStream, WZ>(
    sm       : &SharedMappingHandle,
    mut src  : SrcStream,
    pattern  : Expr,
    template : Expr,
    mut wz   : WZ,
    seperator: u8,
    include_line_nums: bool,
) -> Result<crate::space::PathCount, String>
    where
        WZ : Zipper + ZipperMoving + ZipperWriting<()> + 's,
        SrcStream: BufRead,
{
    let constant_template_prefix = unsafe { template.prefix().unwrap_or_else(|_| template.span()).as_ref().unwrap() };
    let mut src_line = vec![];

    let mut buf = [0u8; 2048];

    let mut i = 0usize;
    let mut stack = [0u8; 2048];
    let mut pdp = ParDataParser::new(sm);

    while src.read_until(b'\n', &mut src_line).map_err(|e| format!("IO error: {e}"))? > 0 {
        let mut sv = if *src_line.last().unwrap() == b'\n' {
            &src_line[..src_line.len()-1]
        } else {
            &src_line
        };
        while sv.len() > 0 && sv[0] == b'\n' {
            sv = &sv[1..];
        }
        if sv.len() == 0 { continue }
        let mut arity = 0;
        let e = Expr{ ptr: stack.as_mut_ptr() };
        let mut ez = ExprZipper::new(e);
        ez.loc += 1;

        if include_line_nums {
            let num = pdp.tokenizer(i.to_string().as_bytes());
            // ez.write_symbol(i.to_be_bytes().as_slice());
            ez.write_symbol(num);
            // ez.loc += 9;
            ez.loc += num.len() + 1;
            arity += 1;
        }

        for symbol in sv.split(|&x| x == seperator) {
            let internal = pdp.tokenizer(symbol);
            ez.write_symbol(&internal[..]);
            ez.loc += internal.len() + 1;
            arity += 1;
        }
        let total = ez.loc;
        ez.reset();
        ez.write_arity(arity);

        let data = &mut stack[..total];
        let mut oz = ExprZipper::new(Expr{ ptr: buf.as_mut_ptr() });
        match (Expr{ ptr: data.as_mut_ptr() }.transformData(pattern, template, &mut oz)) {
            Ok(()) => {}
            Err(_e) => { continue }
        }
        let new_data = &buf[..oz.loc];
        wz.descend_to(&new_data[constant_template_prefix.len()..]);
        wz.set_val(());
        wz.reset();
        i += 1;
        src_line.clear();
    }

    Ok(i)

}

impl DefaultSpace {
    pub fn load_json(&mut self, r: &str) -> Result<PathCount, String> {
        let mut writer = self.new_writer(&[], &())?;
        let mut wz = self.write_zipper(&mut writer);
        load_json_impl(&self.sm, &mut wz, r)
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

    //GOAT, re-integrate this
    //
    // pub fn load_jsonl(&mut self, r: &[u8]) -> Result<(usize, usize), String> {
    //     let mut wz = self.write_zipper_unchecked();
    //     let mut lines = 0usize;
    //     let mut count = 0usize;
    //     let mut pdp = ParDataParser::new(&self.sm);
    //     let spo_symbol = pdp.tokenizer("JSONL".as_bytes());
    //     let mut path = vec![item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(spo_symbol.len() as u8))];
    //     path.extend_from_slice(spo_symbol);
    //     wz.descend_to(&path[..]);
    //     for line in unsafe { std::str::from_utf8_unchecked(r).lines() } {
    //         wz.descend_to(lines.to_be_bytes());
    //         let mut st = SpaceTranscriber{ count: 0, wz: &mut wz, pdp: ParDataParser::new(&self.sm) };
    //         let mut p = crate::json_parser::Parser::new(line);
    //         p.parse(&mut st).unwrap();
    //         count += st.count;
    //         lines += 1;
    //         wz.ascend(8);
    //         if lines > 0 && lines % 1000_000 == 0 {
    //             println!("parsed {} JSON lines ({} paths)", lines, count);
    //         }
    //     }
    //     Ok((lines, count))
    // }

    // pub fn load_jsonl_par(&mut self, r: &[u8]) -> Result<(usize, usize), String> {
    //     let mut wz = self.write_zipper_unchecked();
    //     let mut lines = 0usize;
    //     let mut count = 0usize;
    //     let mut pdp = ParDataParser::new(&self.sm);
    //     let spo_symbol = pdp.tokenizer("JSONL".as_bytes());
    //     let mut path = vec![item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(spo_symbol.len() as u8))];
    //     path.extend_from_slice(spo_symbol);
    //     wz.descend_to(&path[..]);
    //     for line in unsafe { std::str::from_utf8_unchecked(r).lines() } {
    //         wz.descend_to(lines.to_be_bytes());
    //         let mut st = SpaceTranscriber{ count: 0, wz: &mut wz, pdp: ParDataParser::new(&self.sm) };
    //         let mut p = crate::json_parser::Parser::new(line);
    //         p.parse(&mut st).unwrap();
    //         count += st.count;
    //         lines += 1;
    //         wz.ascend(8);
    //         if lines > 0 && lines % 1000_000 == 0 {
    //             println!("parsed {} JSON lines ({} paths)", lines, count);
    //         }
    //     }
    //     Ok((lines, count))
    // }

    // pub fn load_json_(&mut self, r: &[u8], pattern: Expr, template: Expr) -> Result<usize, String> {
    //     let constant_template_prefix = unsafe { template.prefix().unwrap_or_else(|_| template.span()).as_ref().unwrap() };
    //     let mut wz = self.write_zipper_at_unchecked(constant_template_prefix);

    //     let mut st = SpaceTranscriber{ count: 0, wz: &mut wz, pdp: ParDataParser::new(&self.sm) };
    //     let mut p = crate::json_parser::Parser::new(unsafe { std::str::from_utf8_unchecked(r) });
    //     p.parse(&mut st).unwrap();
    //     Ok(st.count)
    // }

impl DefaultSpace {
    #[cfg(feature="neo4j")]
    pub fn load_neo4j_triples(&mut self, uri: &str, user: &str, pass: &str) -> Result<PathCount, String> {
        let rt = tokio::runtime::Builder::new_current_thread()
          .enable_io()
          .build()
          .unwrap();

        let mut writer = self.new_writer(&[], &())?;
        let mut wz = self.write_zipper(&mut writer);
        load_neo4j_triples_impl(&self.sm, &mut wz, &rt.handle(), uri, user, pass)
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
            wz.set_val(());
            wz.reset();

            count += 1;
        }

        drop(guard);
        Ok(count)
}
impl DefaultSpace {
    #[cfg(feature="neo4j")]
    pub fn load_neo4j_node_properties(&mut self, uri: &str, user: &str, pass: &str) -> Result<(NodeCount, AttributeCount), String> {
        let rt = tokio::runtime::Builder::new_current_thread()
          .enable_io()
          .build()
          .unwrap();

        let mut writer = self.new_writer(&[], &())?;
        let mut wz = self.write_zipper(&mut writer);
        load_neo4j_node_properties_impl(&self.sm, &mut wz, &rt.handle(), uri, user, pass)
    }
}
#[cfg(feature="neo4j")]
pub(crate) fn load_neo4j_node_properties_impl<'s, WZ>(sm : &SharedMappingHandle, wz : &mut WZ, rt : &tokio::runtime::Handle, uri: &str, user: &str, pass: &str) -> Result<(NodeCount, AttributeCount), String> 
    where
        WZ : Zipper + ZipperMoving + ZipperWriting<()>
{
        use neo4rs::*;
        use mork_bytestring::Tag;
        let graph = Graph::new(uri, user, pass).unwrap();

        let mut pdp = ParDataParser::new(sm);
        let sa_symbol = pdp.tokenizer("NKV".as_bytes());
        let mut nodes = 0;
        let mut attributes = 0;

        wz.descend_to_byte(Tag::Arity(4).byte());
        wz.descend_to_byte(Tag::SymbolSize(sa_symbol.len() as _).byte());
        wz.descend_to(sa_symbol);

        let guard = rt.enter();
        let mut result = rt.block_on(graph.execute(
            query("MATCH (s) RETURN id(s), s"))
        ).unwrap();
        while let Ok(Some(row)) = rt.block_on(result.next()) {
            let s: i64 = row.get("id(s)").unwrap();
            let internal_s = pdp.tokenizer(&s.to_be_bytes());
            wz.descend_to_byte(Tag::SymbolSize(internal_s.len() as _).byte());
            wz.descend_to(internal_s);

            let a: BoltMap = row.get("s").unwrap();

            for (bs, bt) in a.value.iter() {
                let internal_k = pdp.tokenizer(bs.value.as_bytes());
                wz.descend_to_byte(Tag::SymbolSize(internal_k.len() as _).byte());
                wz.descend_to(internal_k);

                let BoltType::String(bv) = bt else { unreachable!() };
                if bv.value.starts_with("[") && bv.value.ends_with("]") {
                    for chunk in bv.value[1..bv.value.len()-1].split(", ") {
                        let c = if chunk.starts_with("\"") && chunk.ends_with("\"") { &chunk[1..chunk.len()-1] } else { chunk };
                        let internal_v = pdp.tokenizer(c.as_bytes());
                        wz.descend_to_byte(Tag::SymbolSize(internal_v.len() as _).byte());
                        wz.descend_to(internal_v);

                        wz.set_val(());

                        wz.ascend(internal_v.len() + 1);
                    }
                } else {
                    let internal_v = pdp.tokenizer(bv.value.as_bytes());
                    wz.descend_to_byte(Tag::SymbolSize(internal_v.len() as _).byte());
                    wz.descend_to(internal_v);

                    wz.set_val(());

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
impl DefaultSpace {
    #[cfg(feature="neo4j")]
    pub fn load_neo4j_node_lables(&mut self, uri: &str, user: &str, pass: &str) -> Result<(NodeCount, AttributeCount), String> {
        let rt = tokio::runtime::Builder::new_current_thread()
          .enable_io()
          .build()
          .unwrap();

        let mut writer = self.new_writer(&[], &())?;
        let mut wz = self.write_zipper(&mut writer);
        load_neo4j_node_labels_impl(&self.sm, &mut wz, &rt.handle(), uri, user, pass)
    }
}
#[cfg(feature="neo4j")]
pub fn load_neo4j_node_labels_impl<'s, WZ>(sm : &SharedMappingHandle, wz : &mut WZ, rt : &tokio::runtime::Handle, uri: &str, user: &str, pass: &str) -> Result<(usize, usize), String> 
    where
        WZ : Zipper + ZipperMoving + ZipperWriting<()>
{
        use neo4rs::*;
        use mork_bytestring::Tag;
        let graph = Graph::new(uri, user, pass).unwrap();

        let mut pdp = ParDataParser::new(&sm);
        let sa_symbol = pdp.tokenizer("NL".as_bytes());
        let mut nodes = 0;
        let mut labels = 0;

        wz.descend_to_byte(Tag::Arity(3).byte());
        wz.descend_to_byte(Tag::SymbolSize(sa_symbol.len() as _).byte());
        wz.descend_to(sa_symbol);

        let guard = rt.enter();
        let mut result = rt.block_on(graph.execute(
            query("MATCH (s) RETURN id(s), labels(s)"))
        ).unwrap();
        while let Ok(Some(row)) = rt.block_on(result.next()) {
            let s: i64 = row.get("id(s)").unwrap();
            let internal_s = pdp.tokenizer(&s.to_be_bytes());
            wz.descend_to_byte(Tag::SymbolSize(internal_s.len() as _).byte());
            wz.descend_to(internal_s);

            let a: BoltList = row.get("labels(s)").unwrap();

            for bl in a.value.iter() {
                let BoltType::String(bv) = bl else { unreachable!() };

                let internal_v = pdp.tokenizer(bv.value.as_bytes());
                wz.descend_to_byte(Tag::SymbolSize(internal_v.len() as _).byte());
                wz.descend_to(internal_v);

                wz.set_val(());

                wz.ascend(internal_v.len() + 1);

                labels += 1;
            }

            wz.ascend(internal_s.len() + 1);
            nodes += 1;
        }
        drop(guard);
        Ok((nodes, labels))
}

impl DefaultSpace {
    pub fn load_sexpr_simple<SrcStream: BufRead>(&mut self, src: SrcStream, pattern: Expr, template: Expr) -> Result<SExprCount, String> {
        let mut writer = self.new_writer(unsafe { &*template.prefix().unwrap_or(template.span()) }, &())?;
        self.load_sexpr(src, pattern, template, &mut writer).map_err(|e| format!("{:?}", e))
    }
}
pub(crate) fn load_sexpr_impl<'s, SrcStream, WZ>(
    sm       : &SharedMappingHandle,
    src      : SrcStream,
    pattern  : Expr,
    template : Expr,
    mut wz   : WZ,
) -> Result<usize, ParserError>
where
        WZ : Zipper + ZipperMoving + ZipperWriting<()> /* + ZipperAbsolutePath */ + 's,
        SrcStream: BufRead,
{
        let constant_template_prefix = unsafe { template.prefix().unwrap_or_else(|_| template.span()).as_ref().unwrap() };
        // core::debug_assert_eq!(wz.origin_path().unwrap(), constant_template_prefix);

        let mut buffer = [0u8; 4096];
        let mut it = ParseContext::new(src);
        let mut i = 0;
        let mut stack = [0u8; 2048];
        let mut parser = ParDataParser::new(sm);
        loop {
            let mut ez = ExprZipper::new(Expr{ptr: stack.as_mut_ptr()});
            match parser.sexpr(&mut it, &mut ez) {
                Ok(()) => {
                    let data = &mut stack[..ez.loc];
                    let mut oz = ExprZipper::new(Expr{ ptr: buffer.as_mut_ptr() });
                    match (Expr{ ptr: data.as_mut_ptr() }.transformData(pattern, template, &mut oz)) {
                        Ok(()) => {}
                        Err(_e) => { continue }
                    }
                    let new_data = &buffer[..oz.loc];
                    wz.descend_to(&new_data[constant_template_prefix.len()..]);
                    wz.set_val(());
                    wz.reset();
                }
                Err(mut err) => {
                    if err.error_type == ParserErrorType::InputFinished {
                        break
                    } else {
                        err.line_idx = Some(i);
                        return Err(err)
                    }
                }
            }
            i += 1;
        }
        Ok(i)
}

pub(crate) fn token_bfs_impl<Rz>(focus_token: &[u8], pattern: Expr, mut rz: Rz) -> Vec<(Vec<u8>, OwnedExpr)>
where
    Rz: Zipper + ZipperAbsolutePath + ZipperMoving + ZipperIteration + ZipperPathBuffer + ZipperForking<()>
{

    // let mut stack = vec![0; 1];
    // stack[0] = ACTION;
    // 
    // let prefix = unsafe { pattern.prefix().unwrap_or_else(|x| pattern.span()).as_ref().unwrap() };
    // let shared = pathmap::utils::find_prefix_overlap(&token[..], prefix);
    // stack.extend_from_slice(&referential_bidirectional_matching_stack_traverse(pattern, prefix.len())[..]);
    // // println!("show {}", show_stack(&stack[..]));
    // stack.reserve(4096);

    rz.move_to_path(focus_token);
    rz.descend_until();

    let cm = rz.child_mask();
    let mut it = cm.iter();

    let mut res = vec![];

    while let Some(b) = it.next() {
        rz.descend_to_byte(b);

        let mut rzc = rz.fork_read_zipper();
        rzc.to_next_val();

        let e = OwnedExpr::from(rzc.origin_path());
        drop(rzc);

        if e.borrow().unifiable(pattern) {
            let v = rz.path().to_vec();
            // println!("token {:?}", &v[..]);
            // println!("expr  {:?}", e);
            res.push((v, e));
        }
        rz.ascend_byte();
    }

    res
}

impl DefaultSpace {

    /// GOAT, What is the point of this function?  Why doesn't it just call `dump_sexpr`??
    pub fn dump_all_sexpr<W : Write>(&self, w: &mut W) -> Result<usize, String> {
        let mut reader = self.new_reader(&[], &()).unwrap();
        let mut rz = self.read_zipper(&mut reader);
        let mut i = 0usize;
        while rz.to_next_val() {
            Expr{ ptr: rz.path().as_ptr().cast_mut() }.serialize(w, |s| {
                #[cfg(feature="interning")]
                {
                    let symbol = i64::from_be_bytes(s.try_into().unwrap()).to_be_bytes();
                    let mstr = self.sm.get_bytes(symbol).map(unsafe { |x| std::str::from_utf8_unchecked(x) });
                    // println!("symbol {symbol:?}, bytes {mstr:?}");
                    unsafe { std::mem::transmute(mstr.expect(format!("failed to look up {:?}", symbol).as_str())) }
                }
                #[cfg(not(feature="interning"))]
                unsafe { std::mem::transmute(std::str::from_utf8(s).unwrap()) }
            });
            w.write(&[b'\n']).map_err(|x| x.to_string())?;
            i += 1;
        }
        Ok(i)
    }

    pub fn dump_sexpr<W : Write>(&self, pattern: Expr, template: Expr, w: &mut W) -> Result<usize, String> {
        let mut reader = self.new_reader(unsafe { pattern.prefix().unwrap_or_else(|_| pattern.span()).as_ref().unwrap() }, &())?;
        let rz = self.read_zipper(&mut reader);

        let s = "IoWriteError";
        let mut error = false;
        let c = dump_as_sexpr_impl(
            &self.sm,
            pattern,
            rz,
            template,
            w, 
            || unsafe { std::ptr::write_volatile(&mut error, true); },
            usize::MAX
        );
        if error { Err(s.to_string()) } else { Ok(c) }
    }
}

pub(crate) fn dump_as_sexpr_impl<'s, RZ, W: std::io::Write>(
    #[allow(unused)] // Symbol table mapping only used when interning feature is enabled
    sm          : &SharedMapping,
    pattern     : Expr,
    pattern_rz  : RZ,
    template    : Expr,
    w           : &mut W,
    mut f       : impl FnMut(),
    max_write   : usize
) -> usize
    where
    RZ : ZipperMoving + ZipperReadOnlySubtries<'s, ()> + ZipperAbsolutePath
{
    // let max_write   : usize = 10;
    let mut buffer = [0u8; 4096];
    let mut i = 0usize;
    // panic!("sizeof {}", std::mem::size_of::<IoWriteError>());

    query_multi_impl(&[pattern], &[pattern_rz],|refs_bindings, _loc| {
        let mut oz = ExprZipper::new(Expr { ptr: buffer.as_mut_ptr() });

        match refs_bindings {
            Ok(refs) => {
                template.substitute(&refs.iter().map(|ee| ee.subsexpr()).collect::<Vec<_>>()[..], &mut oz);
            }
            Err((ref bindings, ti, ni, _)) => {
                mork_bytestring::apply(0, ni as u8, ti as u8, &mut ExprZipper::new(template), bindings, &mut oz, &mut BTreeMap::new(), &mut vec![], &mut vec![]);
            }
        }

        // &buffer[constant_template_prefix.len()..oz.loc]
        let mut varbuf = [0u8; 66];
        varbuf[0] = b'"';

        Expr{ ptr: buffer.as_ptr().cast_mut() }.serialize(w, |s| {
            #[cfg(feature="interning")]
            let s_slice = {
                let symbol = i64::from_be_bytes(s.try_into().unwrap()).to_be_bytes();
                let mstr = sm.get_bytes(symbol).map(unsafe { |x| std::str::from_utf8_unchecked(x) });
                // println!("symbol {symbol:?}, bytes {mstr:?}");
                unsafe { std::mem::transmute(mstr.expect(format!("failed to look up {:?}", symbol).as_str())) }
            };
            #[cfg(not(feature="interning"))]
            let s_slice: &str = unsafe { std::mem::transmute(std::str::from_utf8(s).unwrap()) };

            if s_slice.contains(|b: char| b.is_whitespace()) {
                varbuf[1..1+s.len()].copy_from_slice(s);
                varbuf[1+s.len()] = b'"';
                unsafe { std::mem::transmute(std::str::from_utf8(&varbuf[..s.len() + 2]).unwrap()) } 
            } else {
                s_slice
            }
        });

        if i < max_write {
            // GOAT, we can't make a safely move a string through that setjmp machinery without risking leaking memory
            // w.write(&[b'\n']).map_err(|x| x.to_string())?;
            match w.write(&[b'\n']) {
                Ok(_) => { i += 1; true }
                Err(_) => { f(); false }
            }
        } else {
            false
        }
    });
    i
}

pub fn serialize_sexpr_into<W : std::io::Write>(src_expr_ptr: *mut u8, dst: &mut W, sm: &SharedMapping) -> Result<(), std::io::Error> {

    Expr{ ptr: src_expr_ptr }.serialize(dst, |s| {
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

    Ok(())
}

impl DefaultSpace {
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
        let mut reader = self.new_reader(&[], &()).unwrap();
        let rz = self.read_zipper(&mut reader);
        pathmap::serialization::write_trie("neo4j triples", rz,
                                           |_v, _b| pathmap::serialization::ValueSlice::Read(&[]),
                                           path.as_ref()).map(|_| ())
    }

    pub fn restore_from_dag(&mut self, path: impl AsRef<std::path::Path>) -> Result<(), std::io::Error> {
        unimplemented!()
        // let new_map = pathmap::serialization::deserialize_file(path, |_| ())?;
        // self.map = new_map.into_zipper_head([]);
        // Ok(())
    }

    pub fn backup_tree<OutDirPath : AsRef<std::path::Path>>(&self, path: OutDirPath) -> Result<(), std::io::Error> {
        unimplemented!()
        // pathmap::arena_compact::ArenaCompactTree::dump_from_zipper(
        //     self.btm.read_zipper(), |_v| 0, path).map(|_tree| ())
    }

    pub fn restore_tree(&mut self, path: impl AsRef<std::path::Path>) -> Result<(), std::io::Error> {
        unimplemented!()
        // let tree = pathmap::arena_compact::ArenaCompactTree::open_mmap(path)?;
        // let mut rz = tree.read_zipper();
        // while rz.to_next_val() {
        //     self.btm.set_val_at(rz.path(), ());
        // }
        // Ok(())
    }

    pub fn backup_paths<OutDirPath: AsRef<std::path::Path>>(&self, path: OutDirPath) -> Result<pathmap::path_serialization::SerializationStats, std::io::Error> {
        let mut file = File::create(path).unwrap();
        let mut reader = self.new_reader(&[], &()).unwrap();
        let rz = self.read_zipper(&mut reader);
        pathmap::path_serialization::serialize_paths_(rz, &mut file)
    }

    pub fn restore_paths<OutDirPath : AsRef<std::path::Path>>(&mut self, path: OutDirPath) -> Result<pathmap::path_serialization::DeserializationStats, std::io::Error> {
        let mut file = File::open(path).unwrap();
        let mut writer = self.new_writer(&[], &()).unwrap();
        let wz = self.write_zipper(&mut writer);
        pathmap::path_serialization::deserialize_paths(wz, &mut file, |_, _| ())
    }

    pub fn query_multi<F: FnMut(Result<&[ExprEnv], (BTreeMap<(u8, u8), ExprEnv>, u8, u8, Vec<(u8, u8)>)>, Expr) -> bool>(&self, patterns: &[Expr], effect: F) -> usize {
        let mut readers = patterns.iter().map(|p| {
            self.new_reader(unsafe { p.prefix().unwrap_or_else(|_| p.span()).as_ref().unwrap() }, &()).unwrap()
        }).collect::<Vec<_>>();

        let rzs = readers.iter_mut().map(|reader| {
                self.read_zipper(reader)
        }).collect::<Vec<_>>();

        query_multi_impl(patterns, &rzs, effect)
    }
}

pub(crate) fn query_multi_impl<'s, E, RZ, F>
(
    patterns    : &[E],
    pattern_rzs : &[RZ],
    mut effect  : F,
) -> usize
where
    E: ExprTrait,
    RZ: ZipperMoving + ZipperReadOnlySubtries<'s, ()> + ZipperAbsolutePath,
    F: FnMut(Result<&[ExprEnv], (BTreeMap<(u8, u8), ExprEnv>, u8, u8, Vec<(u8, u8)>)>, Expr) -> bool,
{
        let make_prefix = |e:&Expr|  unsafe { e.prefix().unwrap_or_else(|_| e.span()).as_ref().unwrap() };

        //Sanity check.  Confirm the pattern read zippers match the expression paths
        core::debug_assert_eq!(patterns.len(), pattern_rzs.len());
        #[cfg(debug_assertions)]
        for i in 0..patterns.len() {
            core::debug_assert_eq!(
                make_prefix(&patterns[i].borrow()),
                pattern_rzs[i].origin_path()
            );
        }

        let [pat_0, pat_rest @ ..] = patterns else { return 0; };
        let [rz0, rz_rest @ ..] = pattern_rzs else { return 0; };

        let first_pattern_prefix = make_prefix(&pat_0.borrow());
        if !rz0.path_exists() { return 0; }

        //GOAT??  What is the theory behind this code???
        //It looks like it's composing an expression made out of all the pattern expressions
        let mut virtual_path = vec![Tag::Arity(patterns.len() as u8).byte()];
        let mut pattern_expr = virtual_path.clone();
        for pattern in patterns.iter() {
            trace!(target: "query_multi", "pattern {:?}", pattern);
            pattern_expr.extend_from_slice(unsafe { pattern.borrow().span().as_ref().unwrap() })
        }
        virtual_path.extend_from_slice(first_pattern_prefix);

        //Make a temp map for the first pattern
        let mut first_temp_map = PathMap::new();
        first_temp_map.write_zipper_at_path(&virtual_path[..]).graft(rz0);
        let first_rz = first_temp_map.read_zipper_at_path(&[virtual_path[0]]);

        //Make temp maps for the rest of the patterns
        let mut tmp_maps = vec![];
        for (rz, pat) in rz_rest.iter().zip(pat_rest) {
            let mut temp_map = PathMap::new();
            let prefix = make_prefix(&pat.borrow());
            if !rz.path_exists() {
                trace!("for p={:?} prefix {} not in map", pat.borrow(), serialize(prefix));
                return 0
            }
            temp_map.write_zipper_at_path(prefix).graft(rz);
            tmp_maps.push(temp_map);
        }
        let mut prz = ProductZipper::new(first_rz, patterns[1..].iter().enumerate().map(|(i, _p)| {
            // let prefix = unsafe { p.prefix().unwrap_or_else(|x| p.span()).as_ref().unwrap() };
            // tmp_maps[i].read_zipper_at_path(prefix)
            tmp_maps[i].read_zipper()
        }));
        prz.reserve_buffers(4096, 512);


        let mut stack = vec![0; 1];
        stack[0] = ACTION;

        for pattern in patterns.iter().rev() {
            // let prefix = unsafe { pattern.prefix().unwrap_or_else(|x| pattern.span()).as_ref().unwrap() };
            stack.extend_from_slice(&referential_bidirectional_matching_stack(&mut ExprZipper::new(pattern.borrow()))[..]);
            // stack.extend_from_slice(&referential_bidirectional_matching_stack_traverse(*pattern, prefix.len())[..]);
        }
        stack.reserve(4096);

        let mut references: Vec<ExprEnv> = vec![];
        let mut candidate = 0;
        let mut early = false;

        thread_local! {
            static BREAK: std::cell::RefCell<[u64; 64]> = const { std::cell::RefCell::new([0; 64]) };
        }

        let pat = Expr { ptr: pattern_expr.as_mut_ptr() };
        let pat_newvars = pat.newvars();
        trace!(target: "query_multi", "pattern (newvars={}) {:?}", pat_newvars, serialize(&pattern_expr[..]));
        let mut pat_args = vec![];
        ExprEnv::new(0, pat).args(&mut pat_args);

        BREAK.with_borrow_mut(|a| {
            if unsafe { setjmp(a) == 0 } {
                referential_transition(stack.last_mut().unwrap(), &mut prz, &mut references, 0, &mut |refs, introduced, loc| {
                    let e = Expr { ptr: loc.origin_path().as_ptr().cast_mut() };

                    if true  { // introduced != 0
                        // println!("pattern nvs {:?}", pat.newvars());
                        let mut tmp_args = vec![];
                        ExprEnv::new(1, e).args(&mut tmp_args);

                        let pairs: Vec<_> = pat_args.iter().zip(tmp_args.iter()).enumerate().map(|(i, (pat_arg, data_arg))| {
                            (*pat_arg, ExprEnv::new((i + 1) as u8, data_arg.subsexpr()))
                        }).collect();
                        // for pair in pairs[..].iter() {
                        //     println!("{}", pair.1.show());
                        // }
                        let bindings = unify(
                            pairs
                        );

                        match bindings {
                            Ok(bs) => {
                                // bs.iter().for_each(|(v, ee)| trace!(target: "query_multi", "binding {:?} {}", *v, ee.show()));
                                let mut assignments: Vec<(u8, u8)> = vec![];
                                let (oi, ni) = {
                                    let mut cycled = BTreeMap::<(u8, u8), u8>::new();
                                    let mut stack: Vec<(u8, u8)> = vec![];
                                    let mut scratch = [0u8; 512];
                                    let r = apply(0, 0, 0, &mut ExprZipper::new(pat), &bs, &mut ExprZipper::new(Expr{ ptr: scratch.as_mut_ptr() }), &mut cycled, &mut stack, &mut assignments);
                                    // println!("scratch {:?}", Expr { ptr: scratch.as_mut_ptr() });
                                    r
                                };
                                // println!("pre {:?} {:?} {}", (oi, ni), assignments, assignments.len());

                                unsafe { std::ptr::write_volatile(&mut candidate, std::ptr::read_volatile(&candidate) + 1); }
                                if !effect(Err((bs, oi, ni, assignments)), e) {
                                    unsafe { std::ptr::write_volatile(&mut early, true); }
                                    unsafe { longjmp(a, 1) }
                                }
                            }
                            Err(failed) => {
                                trace!(target: "query_multi", "failed {:?}", failed)
                            }
                        }
                    } else {
                        unsafe { std::ptr::write_volatile(&mut candidate, std::ptr::read_volatile(&candidate) + 1); }
                        if !effect(Ok(refs), e) {
                            unsafe { std::ptr::write_volatile(&mut early, true); }
                            unsafe { longjmp(a, 1) }
                        }
                    }
                })
            }
        });
    
        candidate
}

impl DefaultSpace {
    pub fn transform_multi_multi_simple(&mut self, patterns: &[Expr], templates: &[Expr]) -> (usize, bool) {

        let (read_map, template_prefixes, mut writers) = self.acquire_transform_permissions(patterns, templates, &(), ||{}).unwrap();
        self.transform_multi_multi(patterns, &read_map, templates, &template_prefixes, &mut writers)
    }
}

pub(crate) fn transform_multi_multi_impl<'s, E, RZ, WZ> (
    patterns            : &[E],
    pattern_rzs         : &[RZ],
    templates           : &[E],
    template_prefixes   : &[(usize, usize)],
    template_wzs        : &mut [WZ],
) -> (usize, bool)
    where
    E: ExprTrait,
    RZ : ZipperMoving + ZipperReadOnlySubtries<'s, ()> + ZipperAbsolutePath,
    WZ : ZipperMoving + ZipperWriting<()>
{
        let mut buffer = [0u8; 512];

        let mut any_new = false;
        let touched = query_multi_impl(patterns, pattern_rzs, |refs_bindings, loc| {

            let Err((ref bindings, mut oi, mut ni, mut assignments)) = refs_bindings else { todo!() };
            #[cfg(debug_assertions)]
            bindings.iter().for_each(|(v, ee)| trace!(target: "transform", "binding {:?} {}", *v, ee.show()));

            for (i, ((incremental_path_start, wz_idx), template)) in template_prefixes.iter().zip(templates.iter()).enumerate() {
                let wz = &mut template_wzs[*wz_idx];

                let mut oz = ExprZipper::new(Expr { ptr: buffer.as_mut_ptr() });

                trace!(target: "transform", "{i} template {} @ ({oi} {ni})", serialize(unsafe { template.borrow().span().as_ref().unwrap()}));
                // println!("ass len {}", assignments.len());
                let mut ass = if i == 0 {
                    // assignments.clone()
                    vec![]
                } else {
                    // assignments[..1].to_vec()
                    vec![]
                };
                // let mut ass = vec![];
                let res = mork_bytestring::apply(0 as u8, 0 as u8, 0, &mut ExprZipper::new(template.borrow()), bindings, &mut oz, &mut BTreeMap::new(), &mut vec![], &mut ass);
                // println!("res {:?}", res);
                // (oi, ni) = res;

                //   0      1      2      3      4      5      6      7      8      9
                //  [(1,3), (3,4), (3,5), (3,6), (3,0), (3,1), (3,7), (3,8), (3,2), (3,3)]
                // <0, 3> = (, (petri (? <3,4> <3,5> <3,6>)) (petri (! <3,0> <3,1>)) (exec PC0 <3,7> <3,8>))
                // <0, 4> = (, (petri <3,2>) (exec PC0 <3,3> <3,4>))
                // [4] exec PC0 _4 _5

                // loc.transformed(template,)
                trace!(target: "transform", "{i} out {:?}", oz.root);
                // println!("descending {:?} to {:?}", serialize(prefix), serialize(&buffer[template_prefixes[subsumption[i]].len()..oz.loc]));

                wz.descend_to(&buffer[*incremental_path_start..oz.loc]);

                // println!("wz path {} {}", serialize(template_prefixes[subsumption[i]]), serialize(wz.path()));
                // println!("insert path {}", serialize(&buffer[..oz.loc]));
                any_new |= wz.set_val(()).is_none();
                wz.reset();
            }
            true
        });

        (touched, any_new)
}

impl DefaultSpace {

    pub fn transform_multi(&mut self, patterns: &[Expr], template: Expr) -> (usize, bool) {
        self.transform_multi_multi_simple(patterns, &[template])
    }

    pub fn transform(&mut self, pattern: Expr, template: Expr) -> (usize, bool) {
        self.transform_multi_multi_simple(&[pattern], &[template])
    }

    pub fn query<F : FnMut(Expr) -> ()>(&self, pattern: Expr, mut effect: F) {
        self.query_multi(&[pattern], |_refs, e| {
            effect(e);
            true
        } );
    }

    pub fn interpret_datalog(&mut self, rt: Expr) -> bool {
        let mut rtz = ExprZipper::new(rt);
        assert_eq!(rtz.item(), Ok(Tag::Arity(3)));
        assert!(rtz.next());
        assert_eq!(unsafe { rtz.subexpr().span().as_ref().unwrap() }, unsafe { expr!(self, "-:").span().as_ref().unwrap() });

        assert!(rtz.next_child());
        let dsts = comma_fun_args_asserted(self, rtz.subexpr());

        assert!(rtz.next_child());
        let res = rtz.subexpr();

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
    
    //     for statement in statements {
    //         let patterns = f(statement);
    //         let last_wrapped_patterns = patterns;
    //         let template = g(statement);
    //         let current_wrapped_template = template;
    //         self.transform_multi(last_wrapped_patterns, current_wrapped_template);
    
    //     }
    
    //     loop {
    //         match self.btm.write_zipper_at_path(&current_wrapped[..]).join_into(&mut self.btm.write_zipper_at_path(&last_wrapped[..])) {
    //             AlgebraicStatus::Element => {}
    //             AlgebraicStatus::Identity => { break }
    //             AlgebraicStatus::None => { panic!("zero") }
    //         }
    //     }
    // }

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

    pub fn done(self) -> ! {
        // let counters = pathmap::counters::Counters::count_ocupancy(&self.btm);
        // counters.print_histogram_by_depth();
        // counters.print_run_length_histogram();
        // counters.print_list_node_stats();
        // println!("#symbols {}", self.sm.symbol_count());
        process::exit(0);
    }

    // just a helper method for debuging
    #[cfg(test)]
    pub fn dump_raw_at_root(&self) -> RawDump {
        let mut reader = self.new_reader(&[], &()).unwrap();
        let mut rz = self.read_zipper(&mut reader);
        let mut out = Vec::new();
        while rz.to_next_val() {
            out.push(rz.origin_path().to_vec());
        }
        RawDump(out)
    }
}

/// Used in debugging, for conveniently dumping the contents of a space
pub struct RawDump(Vec<Vec<u8>>);

impl core::fmt::Debug for RawDump {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> std::fmt::Result {
        for line in self.0.iter() {
            writeln!(f, "{line:?}")?;
        }
        Ok(())
    }
}

/// An error type resulting from an attempt to run an MM2 thread
pub enum ExecError<S: Space> {
    Syntax(ExecSyntaxError),
    OtherFmtErr(String),
    SystemPermissionErr(S::PermissionErr),
    UserPermissionErr(S::PermissionErr),
    RetryLimit(String),
}

pub enum ExecSyntaxError {
    ExpectedArity4(String),
    ExpectedExecKeyword(String),
    ExpectedThreadIdPair(String),
    ExpectedCommaListPatterns(String),
    ExpectedCommaListTemplates(String),
    ExpectedGroundThreadId(String),
    ExpectedGroundPriority(String),
}


impl<S: Space> ExecError<S> {
    /// Creates a new `ExecError` from a PermissionErr
    ///
    /// This function is also responsible for validating whether a whether a `PermissionErr` should be
    /// classified as a [ExecError::UserPermissionErr] or a [ExecError::SystemPermissionErr], the former
    /// indicating that another command is holding the required paths and therefore a retry is in order,
    /// while the latter indicating that an illegal request has been made.
    pub fn perm_err(space: &S, perm_err: S::PermissionErr) -> Self {
        let path = perm_err.path();

        //GOAT, MM2-Syntax.  we need to lift these patterns out as constants so we can tweak the MM2 syntax without hunting through the implementation
        let exec_status_subspace = unsafe{ expr!(space, "[2] exec $").prefix().unwrap().as_ref().unwrap() };

        //For now, we only have 2 reserved types of paths.  We may have others in the future
        if path.len() < 2 || path.starts_with(exec_status_subspace) {
            Self::SystemPermissionErr(perm_err)
        } else {
            Self::UserPermissionErr(perm_err)
        }
    }

    /// Returns a space's `PermissionErr` if the `ExecError` is a `UserPermissionErr` variant
    #[inline]
    pub fn into_perm_err(self) -> Option<S::PermissionErr> {
        match self {
            Self::SystemPermissionErr(err) => Some(err),
            Self::UserPermissionErr(err) => Some(err),
            _ => None
        }
    }
}

impl<S: Space> PartialEq<Self> for ExecError<S> {
    fn eq(&self, other: &Self) -> bool {
        match self {
            Self::Syntax(ExecSyntaxError::ExpectedArity4(_)) => {matches!(other, Self::Syntax(ExecSyntaxError::ExpectedArity4(_)))},
            Self::Syntax(ExecSyntaxError::ExpectedExecKeyword(_)) => {matches!(other, Self::Syntax(ExecSyntaxError::ExpectedExecKeyword(_)))},
            Self::Syntax(ExecSyntaxError::ExpectedThreadIdPair(_)) => {matches!(other, Self::Syntax(ExecSyntaxError::ExpectedThreadIdPair(_)))},
            Self::Syntax(ExecSyntaxError::ExpectedCommaListPatterns(_)) => {matches!(other, Self::Syntax(ExecSyntaxError::ExpectedCommaListPatterns(_)))},
            Self::Syntax(ExecSyntaxError::ExpectedCommaListTemplates(_)) => {matches!(other, Self::Syntax(ExecSyntaxError::ExpectedCommaListTemplates(_)))},
            Self::Syntax(ExecSyntaxError::ExpectedGroundPriority(_)) => {matches!(other, Self::Syntax(ExecSyntaxError::ExpectedGroundPriority(_)))},
            Self::Syntax(ExecSyntaxError::ExpectedGroundThreadId(_)) => {matches!(other, Self::Syntax(ExecSyntaxError::ExpectedGroundThreadId(_)))},
            Self::OtherFmtErr(_) => {matches!(other, Self::OtherFmtErr(_))},
            Self::SystemPermissionErr(_) => {matches!(other, Self::SystemPermissionErr(_))},
            Self::UserPermissionErr(_) => {matches!(other, Self::UserPermissionErr(_))},
            Self::RetryLimit(_) => {matches!(other, Self::RetryLimit(_))},
        }
    }
}
impl<S: Space> Eq for ExecError<S> {}

impl<S: Space> core::fmt::Debug for ExecError<S> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Syntax(ExecSyntaxError::ExpectedArity4(s)) => { format!("ExecError: ExpectedArity4 {s}").fmt(f) },
            Self::Syntax(ExecSyntaxError::ExpectedExecKeyword(s)) => { format!("ExecError: ExpectedExecKeyword {s}").fmt(f) },
            Self::Syntax(ExecSyntaxError::ExpectedThreadIdPair(s)) => { format!("ExecError: ExpectedThreadIdPair {s}").fmt(f) },
            Self::Syntax(ExecSyntaxError::ExpectedCommaListPatterns(s)) => { format!("ExecError: ExpectedCommaListPatterns {s}").fmt(f) },
            Self::Syntax(ExecSyntaxError::ExpectedCommaListTemplates(s)) => { format!("ExecError: ExpectedCommaListTemplates {s}").fmt(f) },
            Self::Syntax(ExecSyntaxError::ExpectedGroundPriority(s)) => { format!("ExecError: ExpectedGroundPriority {s}").fmt(f) },
            Self::Syntax(ExecSyntaxError::ExpectedGroundThreadId(s)) => { format!("ExecError: ExpectedGroundThreadId {s}").fmt(f) },
            Self::OtherFmtErr(s) => { format!("ExecError: OtherFmtErr {s}").fmt(f) },
            Self::SystemPermissionErr(s) => { format!("ExecError: SystemPermissionErr {s:?}").fmt(f) },
            Self::UserPermissionErr(s) => { format!("ExecError: UserPermissionErr {s:?}").fmt(f) },
            Self::RetryLimit(s) => { format!("ExecError: RetryLimit {s:?}").fmt(f) },
        }
    }
}

type PatternExpr = Expr;
type PatternsExpr = Expr;
type TemplateExpr = Expr;
type TemplatesExpr = Expr;

/// The pattern and template sets from an `exec` expression
///
/// the inner [`(PatternsExpr, TemplatesExpr)`] is guaranteed to have expr lists of the form `[<len>] , ...<Patterns | Templates>)`
#[derive(Clone, Copy)]
struct PatternsTemplatesExprs {
    patterns : PatternsExpr,
    templates : TemplatesExpr,
}
impl PatternsTemplatesExprs {
    fn new(patterns : Expr, templates : Expr) -> Self {Self { patterns: patterns, templates }}
    fn collect_inner(self) -> (Vec<PatternExpr>, Vec<TemplateExpr>) {
        ( fun_args(ExprZipper::new(self.patterns))
        , fun_args(ExprZipper::new(self.templates))
        )
    }
}
/// this function should only be called if the [`ExprZipper`] passed in is at an [`Tag::Arity`] and the first element is a "function" symbol.
fn fun_args(mut ez : ExprZipper)->Vec<Expr> {

    // [n]
    let Tag::Arity(n) = ez.tag() else { panic!() };
    ez.next_child();
    debug_assert!(n >= 1);

    // <function>
    debug_assert!(ez.subexpr().is_ground());
    ez.next_child();

    let mut srcs = Vec::with_capacity(n as usize - 1);
    for _ in 0..n as usize - 1 {
        srcs.push(ez.subexpr());
        ez.next_child();
    }
    srcs
}

fn comma_fun_args_asserted(s : &impl Space, e : Expr)->Vec<Expr> {
    let mut ez = ExprZipper::new(e);
    debug_assert!(matches!(ez.tag(), Tag::Arity(_)));
    ez.next_child();
    let comma = unsafe { expr!(s, ",").span().as_ref().unwrap() };
    assert_eq!(
        unsafe { ez.subexpr().span().as_ref().unwrap() }, 
        comma
    );
    ez.reset();
    debug_assert!(matches!(ez.tag(), Tag::Arity(_)));
    fun_args(ez)
}

#[cfg(test)]
#[test]
fn iter_reset_expr(){
    let s = DefaultSpace::new();
    let e = expr!(&s, "[3] a [2] b c d");
    let mut ez = ExprZipper::new(e);

    let mut first = String::new();
    loop {
        match ez.tag() {
            Tag::NewVar        => panic!(),
            Tag::VarRef(_)     => panic!(),
            Tag::SymbolSize(n) => first += &format!("SYM({n})"),
            Tag::Arity(n)      => first += &format!("[{}]", n),
        }
        if !ez.next() {break;}
    }

    println!("\n");
    ez.reset();

    let mut second = String::new();
    loop {
        match ez.tag() {
            Tag::NewVar        => panic!(),
            Tag::VarRef(_)     => panic!(),
            Tag::SymbolSize(n) => second += &format!("SYM({n})"),
            Tag::Arity(n)      => second += &format!("[{}]", n),
        }
        if !ez.next() {break;}
    }

    assert_eq!(first,second)
}

#[cfg(test)]
#[test]
fn bfs_test() {
    const EXPRS: &str = r#"
        (first_name John)
        (last_name Smith)
        (is_alive true)
        (address (street_address 21 2nd Street))
        (address (city New York))
        (address (state NY))
        (address (postal_code 10021-3100))
        (phone_numbers (0 (type home)))
        (phone_numbers (0 (number 212 555-1234)))
        (phone_numbers (1 (type office)))
        (phone_numbers (1 (number 646 555-4567)))
        (children (0 Catherine))
        (children (1 Thomas))
        (children (2 Trevor))
    "#;

    let space = DefaultSpace::new();
    let pattern = expr!(space, "[2] $ $");
    let template = expr!(space, "[2] $ $");
    let mut writer = space.new_writer(unsafe { &*template.prefix().unwrap() }, &()).unwrap();
    space.load_sexpr(EXPRS.as_bytes(), pattern, template, &mut writer).unwrap();
    drop(writer);

    let mut reader = space.new_reader(unsafe { &*template.prefix().unwrap_or(template.span()) }, &()).unwrap();
    let prime_results = space.token_bfs(&[], expr!(space, "$"), &mut reader);
    println!("Prime {:?}", space.token_bfs(&[], expr!(space, "$"), &mut reader));
    let [(t1, _), (t2, _), ..] = &prime_results[..] else { panic!() };
    println!("L1.0 {:?}", space.token_bfs(t1, expr!(space, "$"), &mut reader));
    println!("L1.1 {:?}", space.token_bfs(t2, expr!(space, "$"), &mut reader));
}





























pub mod metta_calculus;
