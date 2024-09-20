use std::fmt::format;
use std::hint::black_box;
use std::io::{BufRead, Read, Write};
use std::ptr;
use std::time::Instant;
use mork_bytestring::{byte_item, Expr, ExprZipper, ExtractFailure, item_byte, Tag};
use mork_bytestring::Tag::{Arity, SymbolSize};
use mork_frontend::bytestring_parser::{Parser, ParserError, BufferedIterator};
use pathmap::trie_map::BytesTrieMap;
use pathmap::zipper::{ReadZipper, WriteZipper, Zipper};


#[repr(transparent)]
pub struct Space { pub(crate) btm: BytesTrieMap<()> }

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

pub fn setup() {
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
            stack.push(ITER_VARIABLES);
            transition(stack, loc, f);
            stack.pop();

            stack.push(ITER_SYMBOL);
            transition(stack, loc, f);
            stack.pop();
        }
        ITER_ARITY => {
            let arity = stack.pop().unwrap();
            loc.descend_to(&[item_byte(Arity(arity))]);
            transition(stack, loc, f);
            loc.ascend(1);
            stack.push(arity);
        }
        ITER_VAR_ARITY => {
            stack.push(ITER_VARIABLES);
            transition(stack, loc, f);
            stack.pop();

            stack.push(ITER_ARITY);
            transition(stack, loc, f);
            stack.pop();
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

pub struct SymbolMapping {
    count: u64,
    symbols: BytesTrieMap<Vec<u8>>,
    strings: BytesTrieMap<String>,
}

impl SymbolMapping {
    pub fn new() -> Self {
        Self {
            count: 3,
            symbols: BytesTrieMap::new(),
            strings: BytesTrieMap::new(),
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

impl Parser for SymbolMapping {
    fn tokenizer(&mut self, s: String) -> Vec<u8> {
        // return s.as_bytes().to_vec();
        if let Some(r) = self.symbols.get(s.as_bytes()) {
            r.clone()
        } else {
            self.count += 1;
            let mut buf: [u8; 8] = [0; 8];
            let slice = gen_key(self.count, buf.as_mut_ptr());
            let internal = slice.to_vec();
            self.symbols.insert(s.as_bytes(), internal.clone());
            self.strings.insert(slice, s.clone());
            internal
        }
    }
}

impl SymbolMapping {
    pub fn token_lookup(&self, token: &[u8]) -> Option<&String> {
        self.strings.get(token)
    }
}


impl Space {
    pub fn new() -> Self {
        Self { btm: BytesTrieMap::new() }
    }

    // fn write_zipper_unchecked<'w>(&'w self) -> WriteZipper<'w, 'w, ()> where Self : 'w  {
    //     unsafe { (&self.btm as *const BytesTrieMap<()>).cast_mut().as_mut().unwrap().write_zipper() }
    // }
    fn write_zipper_unchecked<'a>(&'a self) -> WriteZipper<'a, 'a, ()> {
        unsafe { (&self.btm as *const BytesTrieMap<()>).cast_mut().as_mut().unwrap().write_zipper() }
    }

    pub fn load_csv<R : Read>(&mut self, mut r: R, sm: &mut SymbolMapping) -> Result<usize, String> {
        let mut i = 0;
        let mut buf = vec![];
        let mut stack = [0u8; 2048];

        match r.read_to_end(&mut buf) {
            Ok(read) => {
                for sv in buf.split(|&x| x == b'\n') {
                    if sv.len() == 0 { continue }
                    let mut a = 0;
                    let e = Expr{ ptr: stack.as_mut_ptr() };
                    let mut ez = ExprZipper::new(e);
                    ez.loc += 1;
                    for symbol in sv.split(|&x| x == b',') {
                        let internal = sm.tokenizer(unsafe { String::from_utf8_unchecked(symbol.to_vec()) });
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
            }
            Err(e) => { return Err(format!("{:?}", e)) }
        }

        Ok(i)
    }

    pub fn load_json<R : Read>(&mut self, mut r: R, sm: &'static mut SymbolMapping) -> Result<usize, String> {
    // pub fn load_json<'s, R : Read>(&'s mut self, mut r: R, sm: &'static mut SymbolMapping) -> Result<usize, String> where Self : 's {
        pub struct SpaceTranscriber<'a, 'b, 'c> { count: usize, wz: &'c mut WriteZipper<'a, 'b, ()>, sm: &'static mut SymbolMapping }
        impl <'a, 'b, 'c> SpaceTranscriber<'a, 'b, 'c> {
            #[inline(always)] fn write<S : Into<String>>(&mut self, s: S) {
                let s = s.into();
                let token = self.sm.tokenizer(s.clone());
                let mut path = vec![item_byte(Tag::SymbolSize(token.len() as u8))];
                path.extend(token);
                self.wz.descend_to(&path[..]);
                self.wz.set_value(());
                self.count += 1;
                self.wz.ascend(path.len());
            }
        }
        impl <'a, 'b, 'c> crate::json_parser::Transcriber for SpaceTranscriber<'a, 'b, 'c> {
            #[inline(always)] fn descend_index(&mut self, i: usize, first: bool) -> () {
                if first { self.wz.descend_to(&[item_byte(Tag::Arity(2))]); }
                let token = self.sm.tokenizer(i.to_string());
                self.wz.descend_to(&[item_byte(Tag::SymbolSize(token.len() as u8))]);
                self.wz.descend_to(token);
            }
            #[inline(always)] fn ascend_index(&mut self, i: usize, last: bool) -> () {
                self.wz.ascend(self.sm.tokenizer(i.to_string()).len() + 1);
                if last { self.wz.ascend(1); }
            }
            #[inline(always)] fn write_empty_array(&mut self) -> () { self.write("[]"); }
            #[inline(always)] fn descend_key(&mut self, k: &str, first: bool) -> () {
                if first { self.wz.descend_to(&[item_byte(Tag::Arity(2))]); }
                let token = self.sm.tokenizer(k.to_string());
                self.wz.descend_to(&[item_byte(Tag::SymbolSize(token.len() as u8))]);
                self.wz.descend_to(token);
            }
            #[inline(always)] fn ascend_key(&mut self, k: &str, last: bool) -> () {
                self.wz.ascend(self.sm.tokenizer(k.to_string()).len() + 1);
                if last { self.wz.ascend(1); }
            }
            #[inline(always)] fn write_empty_object(&mut self) -> () { self.write("{}"); }
            #[inline(always)] fn write_string(&mut self, s: &str) -> () { self.write(s); }
            #[inline(always)] fn write_positive(&mut self, s: u64) -> () { self.write(s.to_string()); }
            #[inline(always)] fn write_negative(&mut self, s: u64) -> () { let mut s = s.to_string(); s.insert(0, '-'); self.write(s); }
            #[inline(always)] fn write_true(&mut self) -> () { self.write("true"); }
            #[inline(always)] fn write_false(&mut self) -> () { self.write("false"); }
            #[inline(always)] fn write_null(&mut self) -> () { self.write("null"); }
            #[inline(always)] fn begin(&mut self) -> () {}
            #[inline(always)] fn end(&mut self) -> () {}
        }

        let mut wz = self.write_zipper_unchecked();
        let mut st = SpaceTranscriber{ count: 0, wz: &mut wz, sm: sm };
        let mut buf = vec![];
        match r.read_to_end(&mut buf) {
            Ok(_) => {},
            Err(e) => { return Err(format!("{:?}", e)) }
        }
        let mut p = crate::json_parser::Parser::new(unsafe { std::str::from_utf8_unchecked(&buf[..]) });
        p.parse(&mut st).unwrap();
        Ok(st.count)
    }

    pub fn load<R : Read>(&mut self, r: R, sm: &mut SymbolMapping) -> Result<usize, String> {
        let mut it = BufferedIterator::new(r);

        let t0 = Instant::now();
        let mut i = 0;
        let mut stack = [0u8; 2048];
        let mut vs = Vec::with_capacity(64);
        loop {
            let mut ez = ExprZipper::new(Expr{ptr: stack.as_mut_ptr()});
            match sm.sexprUnsafe::<R>(&mut it, &mut vs, &mut ez) {
                Ok(()) => {
                    self.btm.insert(&stack[..ez.loc], ());
                }
                Err(ParserError::InputFinished()) => { break }
                Err(other) => { return Err(format!("{:?}", other)) }
            }
            i += 1;
            vs.clear();
        }
        println!("loading took {} ms", t0.elapsed().as_millis());
        Ok(i)
    }

    pub fn dump<W : Write>(&self, w: &mut W, sm: &'static SymbolMapping) -> Result<usize, String> {
        let mut rz = self.btm.read_zipper();

        let t0 = Instant::now();
        let mut i = 0;
        loop {
            match rz.to_next_val() {
                None => { break }
                Some(()) => {
                    let path = rz.origin_path().unwrap();
                    let e = Expr { ptr: path.as_ptr().cast_mut() };
                    e.serialize(w, |s| sm.token_lookup(s).expect(format!("failed to look up \"{}\"", String::from_utf8(s.to_vec()).unwrap().as_str()).as_str()));
                    w.write(&[b'\n']).map_err(|x| x.to_string())?;
                    i += 1;
                }
            }
        }
        println!("dumping took {} ms", t0.elapsed().as_millis());
        Ok(i)
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
                    wz.descend_to(unsafe { &*oz.finish_span() });
                    wz.set_value(());
                    wz.reset()
                }
                Err(ExtractFailure::IntroducedVar()) | Err(ExtractFailure::RecurrentVar(_)) => {
                    // upgrade to full unification
                    match e.transform(pattern, template) {
                        Ok(e) => {
                            wz.descend_to(unsafe { &*e.span() });
                            wz.set_value(());
                            wz.reset()
                        }
                        _ => {}
                    }
                }
                _ => {}
            }
        });
    }
}
