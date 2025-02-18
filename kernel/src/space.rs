use std::io::{BufRead, Read, Write};
use std::{mem, process, ptr};
use std::time::Instant;
use mork_bytestring::{byte_item, Expr, ExprZipper, ExtractFailure, item_byte, parse, serialize, Tag};
use mork_bytestring::Tag::{Arity, SymbolSize};
use mork_frontend::bytestring_parser::{Parser, ParserError, Context};
use bucket_map::{WritePermit, SharedMapping, SharedMappingHandle};
use pathmap::trie_map::BytesTrieMap;
use pathmap::zipper::{ReadZipperUntracked, WriteZipper, WriteZipperUntracked, Zipper, ZipperAbsolutePath, ZipperIteration};


pub struct Space {
    pub(crate) btm: BytesTrieMap<()>,
    pub(crate) sm: SharedMappingHandle
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
    let mut size = 1;
    while size < 64 {
        let k = item_byte(Tag::VarRef(size));
        ret[((k & 0b11000000) >> 6) as usize] |= 1u64 << (k & 0b00111111);
        size += 1;
    }
    ret
};

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
            let m = mask_and(loc.child_mask(), SIZES);
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
            let m = mask_and(loc.child_mask(), VARS);
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
            let m = mask_and(loc.child_mask(), ARITIES);
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

pub(crate) struct ParDataParser<'a> { count: u64, buf: [u8; 8], write_permit: WritePermit<'a> }

impl <'a> Parser for ParDataParser<'a> {
    fn tokenizer<'r>(&mut self, s: &[u8]) -> &'r [u8] {
        self.count += 1;
        // FIXME hack until either the parser is rewritten or we can take a pointer of the symbol
        self.buf = (self.write_permit.get_sym_or_insert(s) );
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
            println!("before copy {:?}", p.span().as_ref().unwrap());
            let b = std::alloc::alloc(std::alloc::Layout::array::<u8>(used.len()).unwrap());
            std::ptr::copy_nonoverlapping(p.ptr, b, used.len());
            println!("after copy {:?}", Expr{ ptr: b }.span().as_ref().unwrap());
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

    fn write_zipper_unchecked<'a>(&'a self) -> WriteZipperUntracked<'a, 'a, ()> {
        unsafe { (&self.btm as *const BytesTrieMap<()>).cast_mut().as_mut().unwrap().write_zipper() }
    }

    pub fn load_csv(&mut self, r: &[u8]) -> Result<usize, String> {
        let mut i = 0;
        let mut stack = [0u8; 2048];
        let mut pdp = ParDataParser::new(&self.sm);
        for sv in r.split(|&x| x == b'\n') {
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

    pub fn load_json(&mut self, r: &[u8]) -> Result<usize, String> {
        pub struct SpaceTranscriber<'a, 'b, 'c> { count: usize, wz: &'c mut WriteZipperUntracked<'a, 'b, ()>, pdp: ParDataParser<'a> }
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
            #[inline(always)] fn write_empty_array(&mut self) -> () { self.write("[]"); self.count += 1; }
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

        let mut wz = self.write_zipper_unchecked();
        let mut st = SpaceTranscriber{ count: 0, wz: &mut wz, pdp: ParDataParser::new(&self.sm) };
        let mut p = crate::json_parser::Parser::new(unsafe { std::str::from_utf8_unchecked(r) });
        p.parse(&mut st).unwrap();
        Ok(st.count)
    }

    pub fn load(&mut self, r: &[u8]) -> Result<usize, String> {
        let mut it = Context::new(r);

        let t0 = Instant::now();
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
        println!("loading took {} ms", t0.elapsed().as_millis());
        Ok(i)
    }

    pub fn dump<W : Write>(&self, w: &mut W) -> Result<usize, String> {
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
                        // println!("symbol {symbol:?}, bytes {mstr:?}");
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

    pub fn done(self) -> ! {
        // let counters = pathmap::counters::Counters::count_ocupancy(&self.btm);
        // counters.print_histogram_by_depth();
        // counters.print_run_length_histogram();
        // counters.print_list_node_stats();
        // println!("#symbols {}", self.sm.symbol_count());
        process::exit(0);
    }
}
