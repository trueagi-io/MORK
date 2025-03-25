
extern crate alloc;
use alloc::borrow::Cow;

use bucket_map::{SharedMapping, SharedMappingHandle};
use mork_frontend::bytestring_parser::{Parser, ParserError, Context};
use mork_bytestring::{Expr, ExprZipper};
use pathmap::{morphisms::Catamorphism, trie_map::BytesTrieMap, zipper::{ReadZipperTracked, WriteZipperTracked, Zipper, ZipperAbsolutePath, ZipperCreation, ZipperHeadOwned, ZipperIteration, ZipperMoving, ZipperReadOnly, ZipperWriting}};

/// The number of S-Expressions returned by [Space::load_sexpr]
pub type SExprCount     = usize;
pub type PathCount      = usize;
pub type AttributeCount = usize;
pub type NodeCount      = usize;
/// A path in the space, expressed in terms of the space's semantic
pub type Path = [u8];

/// Converts the semantic path into a [PathMap] bytes path
pub fn path_as_bytes(path: &Path) -> Cow<[u8]> {
    Cow::from(path)
}


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
    ///
    /// NOTE: The `&mut Self::Reader` argument ensures exclusivity, but the `Reader` does
    /// not conceptually have mutable state
    fn read_zipper<'r, 's: 'r>(&'s self, reader: &'r mut Self::Reader<'s>) -> impl SpaceReaderZipper<'s, 'r>;

    /// Gets a write zipper from a Writer
    ///
    /// NOTE: The `&mut Self::Writer` argument ensures exclusivity, but the `Writer` does
    /// not conceptually have mutable state
    fn write_zipper<'w, 's: 'w>(&'s self, writer: &'w mut Self::Writer<'s>) -> impl ZipperMoving + ZipperWriting<()> + 'w;

    /// Returns a handle to the `Space`'s [bucket_map] symbol table.
    fn symbol_table(&self) -> &SharedMappingHandle;

    /// Parses and loads a buffer of S-Expressions into the `Space`
    ///
    /// Returns the number of expressions loaded into the space
    fn load_sexpr<'s>(&'s self, data: &str, dst: &mut Self::Writer<'s>) -> Result<SExprCount, Self::Err> {
        let mut dst = self.write_zipper(dst);
        load_sexpr_impl(self.symbol_table(), data, &mut dst)
    }

    fn dump_as_sexpr<'s, W : std::io::Write>(&'s self, dst: &mut W, src: &mut Self::Reader<'s>) -> Result<PathCount, String> {
        let mut rz = self.read_zipper(src);
        let sm = self.symbol_table();
        dump_as_sexpr_impl(sm, dst, &mut rz)
    }

    fn load_csv<'s>(&'s self, writer : &mut Self::Writer<'s>, r: &str) -> Result<PathCount, String> {
        let sm = self.symbol_table();
        let mut wz = self.write_zipper(writer);
        load_csv_impl(sm, &mut wz, r)
    }

    fn load_json<'s>(&'s self, writer : &mut Self::Writer<'s>, r: &str) -> Result<PathCount, String> {
        let mut wz = self.write_zipper(writer);
        let sm = self.symbol_table();

        load_json_impl(sm, &mut wz, r)
    }


    fn transform<'s>(&'s self, reader : &mut Self::Reader<'s>, writer : &mut Self::Writer<'s> , pattern: Expr, template: Expr) {
        // todo take read zipper at static pattern prefix
        let mut rz = self.read_zipper(reader);
        // todo take write zipper at static template prefix
        let mut wz = self.write_zipper(writer);
        transform_impl(&mut rz, &mut wz, pattern, template);
    }

    fn transition<'s, 'r, SRZ : SpaceReaderZipper<'s, 'r>, F:  FnMut(&mut SRZ) -> ()>(&self, stack: &mut Vec<u8>, loc: &mut SRZ, f: &mut F) {
        transition_impl(stack, loc, f)
    }

    fn referential_transition<'s, 'r, SRZ : SpaceReaderZipper<'s, 'r>, F: FnMut(&mut SRZ) -> ()>(&mut self,stack: &mut Vec<u8>, loc: &mut SRZ, references: &mut Vec<(u32, u32)>, f: &mut F) {
        referential_transition_impl(stack, loc, references, f);
    }

    fn query<'s, 'r, F : FnMut(Expr) -> ()>(&'s self, reader : &'r mut Self::Reader<'s>, pattern: Expr, effect: F) {
        let mut rz = self.read_zipper(reader);
        query_impl(&mut rz, pattern, effect);
    }

    fn load_neo4j_triples<'s>(&'s mut self, writer : &mut Self::Writer<'s>, rt : &tokio::runtime::Runtime, uri: &str, user: &str, pass: &str) -> Result<PathCount, String> {
        let sm = self.symbol_table();
        let mut wz = self.write_zipper(writer);
        load_neo4j_triples_impl(sm, &mut wz, rt, uri, user, pass)
    }

    fn load_neo4j_node_properties<'s>(&'s self, writer : &mut Self::Writer<'s>, rt : &tokio::runtime::Runtime, uri: &str, user: &str, pass: &str) -> Result<(NodeCount, AttributeCount), String> {
        let sm = self.symbol_table();
        let mut wz = self.write_zipper(writer);
        load_neo4j_node_properties_impl(sm, &mut wz, rt, uri, user, pass)
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
        reader.reset();
        reader
    }
    fn write_zipper<'w, 's: 'w>(&'s self, writer: &'w mut Self::Writer<'s>) -> impl ZipperMoving + ZipperWriting<()> + 'w {
        writer.reset();
        writer
    }
    fn symbol_table(&self) -> &SharedMappingHandle {
        &self.sm
    }
}

// this module exists purely to make glob importing it easier
pub(crate) mod stack_actions {
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

    #[allow(unused)]
    pub(crate) fn label(l: u8) -> String {
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
} 
use stack_actions::*;


pub(crate) fn backup_as_dag_impl<'s, 'r, RZ, OutFilePath>(rz : &'r mut RZ, path: OutFilePath) -> Result<(), std::io::Error> 
    where 
        &'r mut RZ : ZipperReadOnly<'s, ()> +  ZipperIteration<'s, ()> + ZipperAbsolutePath,
        OutFilePath : AsRef<std::path::Path>
{
    pathmap::serialization::write_trie("neo4j triples", rz,
                                       |_v, _b| pathmap::serialization::ValueSlice::Read(&[]),
                                       path.as_ref()).map(|_| ())
}

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

pub(crate) fn transition_impl<'s, Z : ZipperIteration<'s, ()>, F:  FnMut(&mut Z) -> ()>(stack: &mut Vec<u8>, loc: &mut Z, f: &mut F) {
    use mork_bytestring::{Tag, byte_item, item_byte};
    let last = stack.pop().unwrap();
    match last {
        ACTION => { f(loc) }
        ITER_AT_DEPTH => {
            let size = stack.pop().unwrap();
            if loc.descend_first_k_path(size as usize) {
                transition_impl(stack, loc, f);
                while loc.to_next_k_path(size as usize) {
                    transition_impl(stack, loc, f);
                }
            }
            stack.push(size);
        }
        ITER_NESTED => {
            let arity = stack.pop().unwrap();
            let l = stack.len();
            for _ in 0..arity { stack.push(ITER_EXPR); }
            transition_impl(stack, loc, f);
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
                        transition_impl(stack, loc, f);
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
            transition_impl(stack, loc, f);
            stack.pop();
            stack.pop();
        }
        ITER_VARIABLES => {
            let m = mask_and(loc.child_mask(), VARS);
            let mut it = pathmap::utils::ByteMaskIter::new(m);

            while let Some(b) = it.next() {
                let buf = [b];
                if loc.descend_to(buf) {
                    transition_impl(stack, loc, f);
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
                        transition_impl(stack, loc, f);
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
            transition_impl(stack, loc, f);
            stack.pop();

            stack.push(ITER_SYMBOLS);
            transition_impl(stack, loc, f);
            stack.pop();

            stack.push(ITER_NESTED);
            stack.push(ITER_ARITIES);
            transition_impl(stack, loc, f);
            stack.pop();
            stack.pop();
        }
        ITER_SYMBOL => {
            let size = stack.pop().unwrap();
            let mut v = vec![];
            for _ in 0..size { v.push(stack.pop().unwrap()) }
            loc.descend_to(&[item_byte(Tag::SymbolSize(size))]);
            loc.descend_to(&v[..]);
            transition_impl(stack, loc, f);
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
            transition_impl(stack, loc, f);
            stack.pop();

            loc.descend_to(&[item_byte(Tag::SymbolSize(size))]);
            loc.descend_to(&v[..]);
            transition_impl(stack, loc, f);
            loc.ascend(size as usize);
            loc.ascend(1);
            for _ in 0..size { stack.push(v.pop().unwrap()) }
            stack.push(size)
        }
        ITER_ARITY => {
            let arity = stack.pop().unwrap();
            loc.descend_to(&[item_byte(Tag::Arity(arity))]);
            transition_impl(stack, loc, f);
            loc.ascend(1);
            stack.push(arity);
        }
        ITER_VAR_ARITY => {
            let arity = stack.pop().unwrap();

            stack.push(ITER_VARIABLES);
            transition_impl(stack, loc, f);
            stack.pop();

            loc.descend_to(&[item_byte(Tag::Arity(arity))]);
            transition_impl(stack, loc, f);
            loc.ascend(1);
            stack.push(arity);
        }
        _ => { unreachable!() }
    }
    stack.push(last);
}

pub(crate) fn referential_transition_impl<Z : ZipperMoving + Zipper, F: FnMut(&mut Z) -> ()>(stack: &mut Vec<u8>, loc: &mut Z, references: &mut Vec<(u32, u32)>, f: &mut F) {
    use mork_bytestring::{Tag, byte_item, item_byte};
    use pathmap::utils::ByteMaskIter;

    // println!("/stack {}", stack.iter().map(|x| label(*x)).reduce(|x, y| format!("{} {}", x, y)).unwrap_or("empty".to_string()));
    // println!("|path {:?}", serialize(loc.origin_path().unwrap()));
    // println!("|refs {:?}", references);
    // println!("\\label {}", label(*stack.last().unwrap()));
    let last = stack.pop().unwrap();
    match last {
        ACTION => { f(loc) }
        ITER_AT_DEPTH => {
            let size = stack.pop().unwrap();
            all_at_depth(loc, size as _, |loc| referential_transition_impl(stack, loc, references, f));
            stack.push(size);
        }
        ITER_NESTED => {
            let arity = stack.pop().unwrap();
            let l = stack.len();
            for _ in 0..arity { stack.push(ITER_EXPR); }
            referential_transition_impl(stack, loc, references, f);
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
                        referential_transition_impl(stack, loc, references, f);
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
            referential_transition_impl(stack, loc, references, f);
            stack.pop();
            stack.pop();
        }
        ITER_VARIABLES => {
            let m = mask_and(loc.child_mask(), VARS);
            let mut it = ByteMaskIter::new(m);

            while let Some(b) = it.next() {
                let buf = [b];
                if loc.descend_to(buf) {
                    referential_transition_impl(stack, loc, references, f);
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
                        referential_transition_impl(stack, loc, references, f);
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
            referential_transition_impl(stack, loc, references, f);
            stack.pop();

            stack.push(ITER_SYMBOLS);
            referential_transition_impl(stack, loc, references, f);
            stack.pop();

            stack.push(ITER_NESTED);
            stack.push(ITER_ARITIES);
            referential_transition_impl(stack, loc, references, f);
            stack.pop();
            stack.pop();
        }
        ITER_SYMBOL => {
            let size = stack.pop().unwrap();
            let mut v = vec![];
            for _ in 0..size { v.push(stack.pop().unwrap()) }
            if loc.descend_to_byte(item_byte(Tag::SymbolSize(size))) {
                if loc.descend_to(&v[..]) {
                    referential_transition_impl(stack, loc, references, f);
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
            referential_transition_impl(stack, loc, references, f);
            stack.pop();

            if loc.descend_to_byte(item_byte(Tag::SymbolSize(size))) {
                if loc.descend_to(&v[..]) {
                    referential_transition_impl(stack, loc, references, f);
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
                referential_transition_impl(stack, loc, references, f);
            }
            loc.ascend_byte();
            stack.push(arity);
        }
        ITER_VAR_ARITY => {
            let arity = stack.pop().unwrap();

            stack.push(ITER_VARIABLES);
            referential_transition_impl(stack, loc, references, f);
            stack.pop();

            if loc.descend_to_byte(item_byte(Tag::Arity(arity))) {
                referential_transition_impl(stack, loc, references, f);
            }
            loc.ascend_byte();
            stack.push(arity);
        }
        BEGIN_RANGE => {
            references.push((loc.path().len() as u32, 0));
            referential_transition_impl(stack, loc, references, f);
            references.pop();
        }
        FINALIZE_RANGE => {
            references.last_mut().unwrap().1 = loc.path().len() as u32;
            referential_transition_impl(stack, loc, references, f);
            references.last_mut().unwrap().1 = 0;
        }
        REFER_RANGE => {
            let index = stack.pop().unwrap();
            let (begin, end) = references[index as usize];
            let subexpr = Expr { ptr: loc.path()[begin as usize..end as usize].as_ptr().cast_mut() };

            let substack = indiscriminate_bidirectional_matching_stack(&mut ExprZipper::new(subexpr));
            let substack_len = substack.len();
            stack.extend(substack);
            referential_transition_impl(stack, loc, references, f);
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

pub(crate) fn all_at_depth<Z : ZipperMoving, F>(loc: &mut Z, level: u32, mut action: F) where F: FnMut(&mut Z) -> () {
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



pub(crate) fn transform_impl<'r, RZ, WZ>(rz : &mut RZ, wz : &mut WZ , pattern: Expr, template: Expr)
    where 
        RZ : ZipperIteration<'r, ()> + ZipperAbsolutePath,
        WZ : ZipperMoving + ZipperWriting<()>
{
    use mork_bytestring::ExtractFailure;

    // todo take read zipper at static pattern prefix
    // todo take write zipper at static template prefix
    
    let mut pz = ExprZipper::new(pattern);
    // todo create feedback signal from ExprZipper to buffer size
    let mut buffer = [0u8; 512];
    let mut stack = vec![ACTION];
    // todo generate matching from dynamic postfix
    stack.extend(indiscriminate_bidirectional_matching_stack(&mut pz));
    // todo transition should gather pattern bindings
    transition_impl(&mut stack, rz, &mut |loc| {
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

pub(crate) fn dump_as_sexpr_impl<'s, RZ, W : std::io::Write>(sm : &SharedMappingHandle, dst: &mut W, src: &mut RZ) -> Result<crate::space::PathCount, String> 
    where
    RZ : ZipperAbsolutePath + ZipperIteration<'s, ()>
{
    let mut i = 0;
    loop {
        match src.to_next_val() {
            None => { break }
            Some(()) => {
                let path = src.origin_path().unwrap();
                let e = Expr { ptr: path.as_ptr().cast_mut() };
                e.serialize(dst, |s| {
                    let symbol = i64::from_be_bytes(s.try_into().unwrap()).to_be_bytes();
                    let mstr = sm.get_bytes(symbol).map(unsafe { |x| std::str::from_utf8_unchecked(x) });
                    #[cfg(debug_assertions)]
                    println!("symbol {symbol:?}, bytes {mstr:?}");
                    unsafe { std::mem::transmute(mstr.expect(format!("failed to look up {:?}", symbol).as_str())) }
                });
                dst.write(&[b'\n']).map_err(|x| x.to_string())?;
                i += 1;
            }
        }
    }
    Ok(i)
}

pub(crate) fn load_sexpr_impl<'s, WZ, Err>(sm : &SharedMappingHandle, data: &str, dst: &mut WZ) -> Result<SExprCount, Err> 
    where
    WZ : ZipperMoving + ZipperWriting<()>
{
    let mut it = Context::new(data.as_bytes());

    let mut i = 0;
    let mut stack = [0u8; 2048];
    let mut parser = ParDataParser::new(sm);
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
    Ok(i)
}



pub(crate) fn query_impl<'r, RZ,F : FnMut(Expr) -> ()>(rz : &mut RZ, pattern: Expr, mut effect: F) 
    where
        RZ : ZipperAbsolutePath + ZipperIteration<'r, ()>
{
    let mut pz = ExprZipper::new(pattern);
    let mut stack = vec![ACTION];
    stack.extend(indiscriminate_bidirectional_matching_stack(&mut pz));
    transition_impl(&mut stack, rz, &mut |loc| {
        let e = Expr { ptr: loc.origin_path().unwrap().as_ptr().cast_mut() };
        effect(e);
    });
}




pub(crate) fn load_csv_impl<'s, WZ>(sm : &SharedMappingHandle, wz : &mut WZ, r: &str) -> Result<crate::space::PathCount, String> 
    where
        WZ : Zipper + ZipperMoving + ZipperWriting<()>
{
    wz.reset();

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

        // .insert(&stack[..total], ()); // if only we had this function...
        wz.descend_to(&stack[..total]);
        wz.set_value(());
        wz.reset();
        
        i += 1;
    }
    Ok(i)
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



pub(crate) fn load_neo4j_triples_impl<'s, WZ>(sm : &SharedMappingHandle, wz : &mut WZ, rt : &tokio::runtime::Runtime, uri: &str, user: &str, pass: &str) -> Result<PathCount, String> 
    where
        WZ : Zipper + ZipperMoving + ZipperWriting<()>
{
    use neo4rs::*;

    let graph = Graph::new(uri, user, pass).unwrap();

    let mut pdp = ParDataParser::new(sm);

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
        // .insert(ez.span(), ()); // if only we had this function...
        wz.descend_to(ez.span());
        wz.set_value(());
        wz.reset();
        
        count += 1;
    }
    Ok(count)
}




pub(crate) fn load_neo4j_node_properties_impl<'s, WZ>(sm : &SharedMappingHandle, wz : &mut WZ, rt : &tokio::runtime::Runtime, uri: &str, user: &str, pass: &str) -> Result<(NodeCount, AttributeCount), String> 
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



pub(crate) struct ParDataParser<'a> { count: u64, buf: [u8; 8], write_permit: bucket_map::WritePermit<'a> }

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