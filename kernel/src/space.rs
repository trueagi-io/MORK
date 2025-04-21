use std::{fs::File, io::Write};
use mork_bytestring::Expr;
use bucket_map::{SharedMapping, SharedMappingHandle};
use pathmap::{
    trie_map::BytesTrieMap, 
    zipper::*,
};

use crate::{dump_as_sexpr_impl, load_sexpr_impl, space_temporary};
pub use crate::space_temporary::{
    PathCount,
    NodeCount,
    AttributeCount,
    SExprCount,
    Either,
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
        let table = $space.sym_table();
        let mut pdp = $crate::ParDataParser::new(&table);
        let mut buf = [0u8; 2048];
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
            let table = $space.sym_table();
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

    /// Remy :I want to really discourage the use of this method, it needs to be exposed if we want to use the debugging macros `expr` and `sexpr` without giving access directly to the field
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

    pub fn load_csv(&mut self, r: &str, pattern: Expr, template: Expr) -> Result<usize, String> {
        crate::space_temporary::load_csv_impl(self, &self.sm.clone(), |s, p| Result::<_,Either<_,()>>::Ok(s.write_zipper_at_unchecked(p)), r, pattern, template).map_err(|e| format!("{:?}",e))
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

    pub fn load_sexpr(&mut self, r: &str, pattern: Expr, template: Expr) -> Result<SExprCount, String> {
        load_sexpr_impl(self, &self.sm, |s, p| Result::<_,Either<_,()>>::Ok(s.write_zipper_at_unchecked(p)), r, pattern, template).map_err(|e| format!("{:?}", e))
    }

    pub fn dump_sexpr<W : Write>(&self, pattern: Expr, template: Expr, w: &mut W) -> Result<usize, String> {
        let mut c = self.btm.clone();
        let z = c.zipper_head();
        dump_as_sexpr_impl(&z, &self.sm, pattern, template, w, |_|Result::<_,()>::Ok(())).map_err(|e| format!("{:?}", e))
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


    pub fn query_multi<T, F : FnMut(&[Expr], Expr) -> Result<(), T>>(&self, patterns: &[Expr], effect: F) -> Result<(), T> {
        // this is ugly and the zipper head branch should not merge this, but we need to conserve behavior
        let mut clone = self.btm.clone();
        let zh = clone.zipper_head();
        let x = crate::space_temporary::query_multi_impl(&zh,patterns, effect);
        match x {
            Ok(_)                                         => Ok(()),
            Err(space_temporary::Either::Left(_conflict)) => Ok(()),
            Err(space_temporary::Either::Right(t))        => Err(t),
        }
    }

    pub fn transform_multi_multi(&mut self, patterns: &[Expr], templates: &[Expr]) {
        // this is ugly and the zipper head branch should not merge this, but we need to conserve behavior
        let _ = crate::space_temporary::transform_multi_multi_impl(&self.btm.zipper_head(),patterns, templates, |_|Result::<_,()>::Ok(()), |_|Ok(()));
    }

    pub fn transform_multi(&mut self, patterns: &[Expr], template: Expr) {
        self.transform_multi_multi(patterns, &[template])
    }

    pub fn transform(&mut self, pattern: Expr, template: Expr) {
        self.transform_multi_multi(&[pattern], &[template])
    }

    pub fn query<F : FnMut(&[Expr], Expr) -> ()>(&self, pattern: Expr, mut effect: F) {
        let _ = self.query_multi(&[pattern], |refs, e| { effect(refs, e); Ok::<(), ()>(()) } ).unwrap();
    }
}
