
extern crate alloc;
use alloc::borrow::Cow;
use std::time::Instant;

use bucket_map::{SharedMapping, SharedMappingHandle};
use mork_frontend::bytestring_parser::{Parser, ParserError, Context};
use mork_bytestring::{Expr, ExprZipper};
use pathmap::{trie_map::BytesTrieMap, zipper::{ReadZipperTracked, WriteZipperTracked, ZipperAbsolutePath, ZipperCreation, ZipperHeadOwned, ZipperIteration, ZipperMoving, ZipperReadOnly, ZipperWriting}};

use crate::space::ParDataParser;

/// A path in the space, expressed in terms of the space's semantic
pub type Path = [u8];

/// Converts the semantic path into a [PathMap] bytes path
pub fn path_as_bytes(path: &Path) -> Cow<[u8]> {
    Cow::from(path)
}

/// The number of S-Expressions returned by [Space::load_sexpr]
type SExprCount     = usize;


pub trait SpaceReaderZipper<'s, 'r> :ZipperMoving + ZipperReadOnly<'s, ()> + ZipperIteration<'s, ()> + ZipperAbsolutePath + 'r {}
impl<'s, 'r, T > SpaceReaderZipper<'s, 'r> for T where T : ZipperMoving + ZipperReadOnly<'s, ()> + ZipperIteration<'s, ()> + ZipperAbsolutePath + 'r {}

/// An interface for accessing the state used by the MORK kernel
pub trait Space {
    /// An authentication token used for access to the space
    type Auth;
    /// Objects of this type encapsulate a location in the space and the rights to read from that location
    type Reader<'space> where Self: 'space;
    /// Objects of this type encapsulate a location in the space and the rights to write to that location
    type Writer<'space> where Self: 'space;
    /// An error type
    type Err;

    // ===================== Methods used by caller ===================== 

    /// Requests a new [Space::Reader] from the `Space`
    fn new_reader<'space>(&'space self, path: &Path, auth: &Self::Auth) -> Result<Self::Reader<'space>, Self::Err>;

    /// Requests a new [Space::Writer] from the `Space`
    fn new_writer<'space>(&'space self, path: &Path, auth: &Self::Auth) -> Result<Self::Writer<'space>, Self::Err>;

    // ===================== Methods used by shared impl ===================== 

    /// Gets a read zipper from a Reader
    fn read_zipper<'r, 's: 'r>(&'s self, reader: &'r mut Self::Reader<'s>) -> impl SpaceReaderZipper<'s, 'r>;

    /// Gets a write zipper from a Writer
    fn write_zipper<'w, 's: 'w>(&'s self, writer: &'w mut Self::Writer<'s>) -> impl ZipperMoving + ZipperWriting<()> + 'w;

    /// Returns a handle to the `Space`'s [bucket_map] symbol table.
    fn symbol_table(&self) -> &SharedMappingHandle;

    /// Parses and loads a buffer of S-Expressions into the `Space`
    ///
    /// Returns the number of expressions loaded into the space
    fn load_sexpr<'s>(&'s self, data: &str, dst: &mut Self::Writer<'s>) -> Result<SExprCount, Self::Err> {
        let mut dst = self.write_zipper(dst);
        dst.reset();
        let mut it = Context::new(data.as_bytes());

        let t0 = Instant::now();
        let mut i = 0;
        let mut stack = [0u8; 2048];
        let mut parser = ParDataParser::new(self.symbol_table());
        loop {
            let mut ez = ExprZipper::new(Expr{ptr: stack.as_mut_ptr()});
            match parser.sexpr(&mut it, &mut ez) {
                Ok(()) => {
                    dst.descend_to(&stack[..ez.loc]);
                    dst.set_value(());
                }
                Err(ParserError::InputFinished) => { break }
                Err(other) => { panic!("{:?}", other) }
            }
            i += 1;
            it.variables.clear();
        }
        println!("loading took {} ms", t0.elapsed().as_millis());
        Ok(i)
    }

    fn dump_as_sexpr<'s, W : std::io::Write>(&'s self, dst: &mut W, src: &mut Self::Reader<'s>) -> Result<crate::space::PathCount, String> {
        let mut rz = self.read_zipper(src);

        let t0 = Instant::now();
        let mut i = 0;
        loop {
            match rz.to_next_val() {
                None => { break }
                Some(()) => {
                    let path = rz.origin_path().unwrap();
                    let e = Expr { ptr: path.as_ptr().cast_mut() };
                    e.serialize(dst, |s| {
                        let symbol = i64::from_be_bytes(s.try_into().unwrap()).to_be_bytes();
                        let mstr = self.symbol_table().get_bytes(symbol).map(unsafe { |x| std::str::from_utf8_unchecked(x) });
                        #[cfg(debug_assertions)]
                        println!("symbol {symbol:?}, bytes {mstr:?}");
                        unsafe { std::mem::transmute(mstr.expect(format!("failed to look up {:?}", symbol).as_str())) }
                    });
                    dst.write(&[b'\n']).map_err(|x| x.to_string())?;
                    i += 1;
                }
            }
        }
        println!("dumping took {} ms", t0.elapsed().as_millis());
        Ok(i)
    }


    fn transform<'s>(&'s self, reader : &mut Self::Reader<'s>, writer : &mut Self::Writer<'s> , pattern: Expr, template: Expr) {
        use mork_bytestring::ExtractFailure;

        // todo take read zipper at static pattern prefix
        let mut rz = self.read_zipper(reader);
        // todo take write zipper at static template prefix
        let mut wz = self.write_zipper(writer);
        let mut pz = ExprZipper::new(pattern);
        // todo create feedback signal from ExprZipper to buffer size
        let mut buffer = [0u8; 512];
        let mut stack = vec![ACTION];
        // todo generate matching from dynamic postfix
        stack.extend(indiscriminate_bidirectional_matching_stack(&mut pz));
        // todo transition should gather pattern bindings
        self.transition(&mut stack, &mut rz, &mut |loc| {
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

    fn transition<'s, 'r, SRZ : SpaceReaderZipper<'s, 'r>, F:  FnMut(&mut SRZ) -> ()>(&self, stack: &mut Vec<u8>, loc: &mut SRZ, f: &mut F) {
        use mork_bytestring::{Tag, byte_item, item_byte};
        let last = stack.pop().unwrap();
        match last {
            ACTION => { f(loc) }
            ITER_AT_DEPTH => {
                let size = stack.pop().unwrap();
                if loc.descend_first_k_path(size as usize) {
                    self.transition(stack, loc, f);
                    while loc.to_next_k_path(size as usize) {
                        self.transition(stack, loc, f);
                    }
                }
                stack.push(size);
            }
            ITER_NESTED => {
                let arity = stack.pop().unwrap();
                let l = stack.len();
                for _ in 0..arity { stack.push(ITER_EXPR); }
                self.transition(stack, loc, f);
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
                            self.transition(stack, loc, f);
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
                self.transition(stack, loc, f);
                stack.pop();
                stack.pop();
            }
            ITER_VARIABLES => {
                let m = mask_and(loc.child_mask(), VARS);
                let mut it = pathmap::utils::ByteMaskIter::new(m);
    
                while let Some(b) = it.next() {
                    let buf = [b];
                    if loc.descend_to(buf) {
                        self.transition(stack, loc, f);
                    }
                    loc.ascend(1);
                }
            }
            ITER_ARITIES => {
                let m = mask_and(loc.child_mask(), ARITIES);
                let mut it = pathmap::utils::ByteMaskIter::new(m);
    
                while let Some(b) = it.next() {
                    if let Tag::Arity(a) = byte_item(b) {
                        let buf = [b];
                        if loc.descend_to(buf) {
                            let last = stack.pop().unwrap();
                            stack.push(a);
                            stack.push(last);
                            self.transition(stack, loc, f);
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
                self.transition(stack, loc, f);
                stack.pop();
    
                stack.push(ITER_SYMBOLS);
                self.transition(stack, loc, f);
                stack.pop();
    
                stack.push(ITER_NESTED);
                stack.push(ITER_ARITIES);
                self.transition(stack, loc, f);
                stack.pop();
                stack.pop();
            }
            ITER_SYMBOL => {
                let size = stack.pop().unwrap();
                let mut v = vec![];
                for _ in 0..size { v.push(stack.pop().unwrap()) }
                loc.descend_to(&[item_byte(Tag::SymbolSize(size))]);
                loc.descend_to(&v[..]);
                self.transition(stack, loc, f);
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
                self.transition(stack, loc, f);
                stack.pop();
    
                loc.descend_to(&[item_byte(Tag::SymbolSize(size))]);
                loc.descend_to(&v[..]);
                self.transition(stack, loc, f);
                loc.ascend(size as usize);
                loc.ascend(1);
                for _ in 0..size { stack.push(v.pop().unwrap()) }
                stack.push(size)
            }
            ITER_ARITY => {
                let arity = stack.pop().unwrap();
                loc.descend_to(&[item_byte(Tag::Arity(arity))]);
                self.transition(stack, loc, f);
                loc.ascend(1);
                stack.push(arity);
            }
            ITER_VAR_ARITY => {
                let arity = stack.pop().unwrap();
    
                stack.push(ITER_VARIABLES);
                self.transition(stack, loc, f);
                stack.pop();
    
                loc.descend_to(&[item_byte(Tag::Arity(arity))]);
                self.transition(stack, loc, f);
                loc.ascend(1);
                stack.push(arity);
            }
            _ => { unreachable!() }
        }
        stack.push(last);
    }


    
}

/// A default minimalist implementation of [Space]
pub struct DefaultSpace {
    map: ZipperHeadOwned<()>,
    sm: SharedMappingHandle,
}

impl DefaultSpace {
    /// Creates a new empty `DefaultSpace`
    pub fn new() -> Self {
        Self {
            map: BytesTrieMap::new().into_zipper_head([]),
            sm: SharedMapping::new(),
        }
    }
}

impl Space for DefaultSpace {
    type Auth = ();
    type Reader<'space> = ReadZipperTracked<'space, 'static, ()>;
    type Writer<'space> = WriteZipperTracked<'space, 'static, ()>;
    type Err = String;

    fn new_reader<'space>(&'space self, path: &Path, _auth: &Self::Auth) -> Result<Self::Reader<'space>, Self::Err> {
        let path = path_as_bytes(path);
        self.map.read_zipper_at_path(path).map_err(|e| e.to_string())
    }
    fn new_writer<'space>(&'space self, path: &Path, _auth: &Self::Auth) -> Result<Self::Writer<'space>, Self::Err> {
        let path = path_as_bytes(path);
        self.map.write_zipper_at_exclusive_path(path).map_err(|e| e.to_string())
    }
    fn read_zipper<'r, 's: 'r>(&'s self, reader: &'r mut Self::Reader<'s>) -> impl  ZipperMoving + ZipperReadOnly<'s, ()> + ZipperIteration<'s, ()> + ZipperAbsolutePath + 'r {
        reader
    }
    fn write_zipper<'w, 's: 'w>(&'s self, writer: &'w mut Self::Writer<'s>) -> impl ZipperMoving + ZipperWriting<()> + 'w {
        writer
    }
    fn symbol_table(&self) -> &SharedMappingHandle {
        &self.sm
    }
}



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



fn indiscriminate_bidirectional_matching_stack(ez: &mut mork_bytestring::ExprZipper) -> Vec<u8> {
    use mork_bytestring::Tag;
    
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



fn mask_and(l: [u64; 4], r: [u64; 4]) -> [u64; 4] {
    [l[0] & r[0], l[1] & r[1], l[2] & r[2], l[3] & r[3]]
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
