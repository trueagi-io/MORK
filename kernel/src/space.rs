use std::{fs::File, io::Write};
use mork_bytestring::{Expr, ExprZipper, item_byte, Tag};
use bucket_map::{SharedMapping, SharedMappingHandle};
use pathmap::{
    trie_map::BytesTrieMap, 
    zipper::{WriteZipperUntracked, Zipper, ZipperAbsolutePath, ZipperMoving, ZipperWriting}
};

use crate::space_temporary::{
    SIZES, ARITIES, VARS,
    mask_and,
    stack_actions::*
};
pub use crate::space_temporary::{
    PathCount,
    NodeCount,
    AttributeCount,
    SExprCount,
};
pub struct Space {
    pub(crate) btm: BytesTrieMap<()>,
    pub sm: SharedMappingHandle
}


#[macro_export]
macro_rules! expr {
    ($space:ident, $s:literal) => {{
        let mut src = parse!($s);
        let q = Expr{ ptr: src.as_mut_ptr() };
        let mut pdp = crate::space_temporary::ParDataParser::new(&$space.sm);
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
        crate::space_temporary::load_csv_impl(&self.sm, &mut self.btm.write_zipper(), r)
    }

    pub fn load_json(&mut self, r: &str) -> Result<PathCount, String> {
        crate::space_temporary::load_json_impl(&self.sm, &mut self.btm.write_zipper(), r)
    }

    pub fn load_neo4j_triples(&mut self, uri: &str, user: &str, pass: &str) -> Result<PathCount, String> {
        let rt = tokio::runtime::Builder::new_current_thread()
          .enable_io()
          .build()
          .unwrap();
        crate::space_temporary::load_neo4j_triples_impl(&self.sm, &mut self.btm.write_zipper(), &rt, uri, user, pass)
    }

    pub fn load_neo4j_node_properties(&mut self, uri: &str, user: &str, pass: &str) -> Result<(NodeCount, AttributeCount), String> {
        let rt = tokio::runtime::Builder::new_current_thread()
          .enable_io()
          .build()
          .unwrap();
        crate::space_temporary::load_neo4j_node_properties_impl(&self.sm, &mut self.btm.write_zipper(), &rt, uri, user, pass)
    }

    pub fn load_sexpr(&mut self, r: &str) -> Result<SExprCount, String> {
        crate::space_temporary::load_sexpr_impl(&self.sm, r, &mut self.btm.write_zipper())
    }

    pub fn dump_as_sexpr<W : Write>(&self, w: &mut W) -> Result<PathCount, String> {
        let mut rz = self.btm.read_zipper();
        crate::space_temporary::dump_as_sexpr_impl(&self.sm, w, &mut rz)
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

    pub fn backup_paths<OutDirPath : AsRef<std::path::Path>>(&self, path: OutDirPath) -> Result<pathmap::path_serialization::SerializationStats, std::io::Error> {
        let mut file = File::create(path).unwrap();
        pathmap::path_serialization::serialize_paths_(self.btm.read_zipper(), &mut file)
    }

    pub fn restore_paths<OutDirPath : AsRef<std::path::Path>>(&mut self, path: OutDirPath) -> Result<pathmap::path_serialization::DeserializationStats, std::io::Error> {
        let mut file = File::open(path).unwrap();
        pathmap::path_serialization::deserialize_paths(self.btm.write_zipper(), &mut file, |_, _| ())
    }

    pub fn query<F : FnMut(Expr) -> ()>(&self, pattern: Expr, effect: F) {
        let mut rz = self.btm.read_zipper();
        crate::space_temporary::query_impl(&mut rz, pattern, effect)
    }

    pub fn transform(&mut self, pattern: Expr, template: Expr) {
        // todo take read zipper at static pattern prefix
        let mut rz = self.btm.read_zipper();
        // todo take write zipper at static template prefix
        let mut wz = self.write_zipper_unchecked();
        crate::space_temporary::transform_impl(&mut rz, &mut wz, pattern, template)
    }

    // Remy : this function looked like it was WIP, so I did not add it to the Space trait yet
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

    #[doc(hidden)]
    pub fn inner_map_as_ref(&self) -> &BytesTrieMap<()> {
        &self.btm
    }

    pub fn into_map(self) -> BytesTrieMap<()> {
        self.btm
    }
}

// Remy : This looks to only be used as a helper function for transform_multi, which I was not sure was done. This will be left here for now
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

// Remy : This looks to only be used as a helper function for transform_multi, which I was not sure was done. This will be left here for now
fn referential_transition<Z : ZipperMoving + Zipper, F: FnMut(&mut Z) -> ()>(stack: &mut Vec<u8>, loc: &mut Z, references: &mut Vec<(u32, u32)>, f: &mut F) {
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
            crate::space_temporary::all_at_depth(loc, size as _, |loc| referential_transition(stack, loc, references, f));
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

            let substack = crate::space_temporary::indiscriminate_bidirectional_matching_stack(&mut ExprZipper::new(subexpr));
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
