use std::{fs::File, io::Write};
use mork_bytestring::{Expr, ExprZipper, item_byte, byte_item, Tag, ExtractFailure};
use bucket_map::{SharedMapping, SharedMappingHandle};
use pathmap::{
    trie_map::BytesTrieMap, 
    zipper::*,
    utils::*,
};
use std::ptr;

use crate::space_temporary::{
    SIZES, ARITIES, VARS,
    stack_actions::*
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


#[macro_export]
macro_rules! expr {
    ($space:ident, $s:literal) => {{
        let mut src = mork_bytestring::parse!($s);
        let q = mork_bytestring::Expr{ ptr: src.as_mut_ptr() };
        let mut pdp = $crate::ParDataParser::new(&$space.sm);
        let mut buf = [0u8; 2048];
        let p = mork_bytestring::Expr{ ptr: buf.as_mut_ptr() };
        let used = q.substitute_symbols(&mut mork_bytestring::ExprZipper::new(p), |x| pdp.tokenizer(x));
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
            let mstr = $space.sm.get_bytes(symbol).map(unsafe { |x| std::str::from_utf8_unchecked(x) });
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
        let mut pdp = $crate::space_temporary::ParDataParser::new(&$space.sm);
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

    #[cfg(feature="neo4j")]
    pub fn load_neo4j_triples(&mut self, uri: &str, user: &str, pass: &str) -> Result<PathCount, String> {
        let rt = tokio::runtime::Builder::new_current_thread()
          .enable_io()
          .build()
          .unwrap();
        crate::space_temporary::load_neo4j_triples_impl(&self.sm, &mut self.btm.write_zipper(), &rt.handle(), uri, user, pass)
    }

    #[cfg(feature="neo4j")]
    pub fn load_neo4j_node_properties(&mut self, uri: &str, user: &str, pass: &str) -> Result<(NodeCount, AttributeCount), String> {
        let rt = tokio::runtime::Builder::new_current_thread()
          .enable_io()
          .build()
          .unwrap();
        crate::space_temporary::load_neo4j_node_properties_impl(&self.sm, &mut self.btm.write_zipper(), &rt.handle(), uri, user, pass)
    }

        #[cfg(feature="neo4j")]
    pub fn load_neo4j_node_lables(&mut self, uri: &str, user: &str, pass: &str) -> Result<(NodeCount, AttributeCount), String> {
        let rt = tokio::runtime::Builder::new_current_thread()
          .enable_io()
          .build()
          .unwrap();
        crate::space_temporary::load_neo4j_node_labels_impl(&self.sm, &mut self.btm.write_zipper(), &rt.handle(), uri, user, pass)
    }

    pub fn load_sexpr(&mut self, prefix : crate::prefix::Prefix, r: &str) -> Result<SExprCount, String> {
        crate::space_temporary::load_sexpr_impl(&self.sm, r, &mut self.btm.write_zipper_at_path(prefix.path()))
    }

    pub fn dump_sexpr<W : Write>(&self, prefix : crate::prefix::Prefix, w: &mut W) -> Result<PathCount, String> {
        let mut rz = self.btm.read_zipper_at_path(prefix.path());
        crate::space_temporary::dump_as_sexpr_impl(&self.sm, w, &mut rz)
    }

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

    pub fn query<F : FnMut(Expr) -> ()>(&self, prefix: crate::prefix::Prefix,  pattern: Expr, effect: F) {
        let mut rz = self.btm.read_zipper_at_path(prefix.path());
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
        let mut arity_hack = BytesTrieMap::new();
        arity_hack.write_zipper_at_path(&[item_byte(Tag::Arity(patterns.len() as _))]).graft(&self.btm.read_zipper());
        let rz = arity_hack.read_zipper();
        let mut prz = ProductZipper::new(rz, patterns[1..].iter().map(|_| self.btm.read_zipper()));

        let mut buffer = [0u8; 512];
        let mut stack = vec![0; 4096];
        stack[0] = ACTION;

        let mut compound_vec = vec![item_byte(Tag::Arity(patterns.len() as _))];
        for pattern in patterns.iter() {
            compound_vec.extend_from_slice(unsafe { &*pattern.span() });
        }

        let compound = Expr{ ptr: compound_vec.as_mut_ptr() };
        let v = referential_bidirectional_matching_stack(&mut ExprZipper::new(compound));
        stack[1..1+v.len()].copy_from_slice(&v[..]);
        let mut btm = BytesTrieMap::new();
        let mut references: Vec<(u32, u32)> = vec![];
        let mut candidate = 0;
        referential_transition(&mut stack[v.len()], &mut prz, &mut references, &mut |loc| {
            let e = Expr { ptr: loc.origin_path().unwrap().as_ptr().cast_mut() };
            let mut oz = ExprZipper::new(Expr { ptr: buffer.as_mut_ptr() });
            // println!("{}", sexpr!(self, e));
            match e.transformData(compound, template, &mut oz) {
                Ok(()) => {
                    btm.insert(&buffer[..oz.loc], ());
                }
                Err(ExtractFailure::IntroducedVar()) | Err(ExtractFailure::RecurrentVar(_)) => {
                    todo!()
                }
                Err(other) => {
                    println!("err {:?}", other);
                }
            }
            candidate += 1;
        });
        drop(prz);
        drop(arity_hack);
        self.btm = self.btm.join(&btm);
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

// // Remy : This looks to only be used as a helper function for transform_multi, which I was not sure was done. This will be left here for now
fn referential_transition<Z : ZipperMoving + Zipper, F: FnMut(&mut Z) -> ()>(mut last: *mut u8, loc: &mut Z, references: &mut Vec<(u32, u32)>, f: &mut F) {
    #![allow(unused_unsafe)]
    unsafe {
    macro_rules! unroll {
    (ACTION $recursive:expr) => { f(loc); };
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
<<<<<<< HEAD
        let m = loc.child_mask().and(&ByteMask(SIZES));
=======
        let m = loc.child_mask().and(&pathmap::utils::ByteMask(SIZES));
>>>>>>> 4da5072 (first step to sexpr prefix.)
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
<<<<<<< HEAD
        let m = loc.child_mask().and(&ByteMask(VARS));
=======
        let m = loc.child_mask().and(&pathmap::utils::ByteMask(VARS));
>>>>>>> 4da5072 (first step to sexpr prefix.)
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
<<<<<<< HEAD
        let m = loc.child_mask().and(&ByteMask(ARITIES));
=======
        let m = loc.child_mask().and(&pathmap::utils::ByteMask(ARITIES));
>>>>>>> 4da5072 (first step to sexpr prefix.)
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
        references.push((loc.path().len() as u32, 0));
        $recursive;
        references.pop();
    };
    (FINALIZE_RANGE $recursive:expr) => {
        references.last_mut().unwrap().1 = loc.path().len() as u32;
        $recursive;
        references.last_mut().unwrap().1 = 0;
    };
    (REFER_RANGE $recursive:expr) => {
        let index = *last; last = last.offset(-1);
        let (begin, end) = references[index as usize];
        let subexpr = Expr { ptr: loc.path()[begin as usize..end as usize].as_ptr().cast_mut() };
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
                    ptr::copy_nonoverlapping(s.as_ptr(), last, s.len());
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
