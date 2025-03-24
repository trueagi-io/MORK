use std::marker::PhantomData;

use pathmap::{self, trie_map::BytesTrieMap, zipper, TrieValue};
use bucket_map::SharedMappingHandle;


pub struct Space<Machine, Semantics, >{ machine : Machine, semanitic : Semantics }

struct MeTTa<V> {
    symbols    : SharedMappingHandle,
    value_type : PhantomData<*const V>,
}
impl<V> core::clone::Clone for MeTTa<V> {
    fn clone(&self) -> Self {
        Self { symbols: self.symbols.clone(), value_type: self.value_type }
    }
}

impl<V> Semantic for MeTTa<V> { type Value = V;}
impl<V> Semantic for &MeTTa<V> { type Value = V;}

trait Semantic : Sized + Clone {
    type Value;

    fn empty_space(self)->Space<BytesTrieMap<Self::Value>, Self> where Self::Value : TrieValue { Space { machine: BytesTrieMap::new(), semanitic: self } }
}


impl<V : TrieValue, S : Semantic<Value = V>> Space<BytesTrieMap<V>, S> {
    fn read_zipper(&self)-> Space<pathmap::zipper::ReadZipperUntracked<V>, &S> 
        { Space { machine: self.machine.read_zipper(), semanitic: &self.semanitic } }
}
impl<'a, V  : TrieValue, RZ : pathmap::zipper::ZipperMoving,S  : Semantic<Value =  V>> 
  Space<RZ, S>
{
    fn descend_to(&mut self, path : &[u8])->bool{ self.machine.descend_to(path)}
}





// fn ex() {
//     let x : BytesTrieMap<()> = BytesTrieMap::new();
//     let rw =  x.read_zipper();
// }




impl Space<BytesTrieMap<()>, MeTTa<()>> {
    pub fn load_sexpr(&mut self, r: &str) -> Result<crate::space::SExprCount, String> {
        use mork_frontend::bytestring_parser::Parser;
        let mut it = mork_frontend::bytestring_parser::Context::new(r.as_bytes());
    
        let mut i = 0;
        let mut stack = [0u8; 2048];
        let mut parser = crate::space::ParDataParser::new(&self.semanitic.symbols);
        loop {
            let mut ez = mork_bytestring::ExprZipper::new(mork_bytestring::Expr{ptr: stack.as_mut_ptr()});
            match parser.sexpr(&mut it, &mut ez) {
                Ok(()) => { self.machine.insert(&stack[..ez.loc], ()); }
                Err(mork_frontend::bytestring_parser::ParserError::InputFinished) => { break }
                Err(other) => { panic!("{:?}", other) }
            }
            i += 1;
            it.variables.clear();
        }
        Ok(i)
    }
}