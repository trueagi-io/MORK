use log::trace;
use pathmap::zipper::{PolyZipper, PrefixZipper, ReadZipperTracked, ReadZipperUntracked, Zipper, ZipperAbsolutePath, ZipperIteration, ZipperMoving};
use mork_expr::{item_byte, serialize, Expr, Tag};

pub trait Source {
    fn new(e: Expr) -> Self;
    fn request(&self) -> impl Iterator<Item=&'static [u8]>;
    fn source<'a, 'k, It : Iterator<Item=ReadZipperUntracked<'a, 'k, ()>>>(&self, it: It) -> AFactor<'a, ()> where 'k : 'a;
}

struct PosSource {
    e: Expr
}
impl Source for PosSource {

    fn new(e: Expr) -> Self {
        PosSource{ e }
    }

    fn request(&self) -> impl Iterator<Item=&'static [u8]> {
        std::iter::once([].as_slice())
    }

    fn source<'a, 'k, It: Iterator<Item=ReadZipperUntracked<'a, 'k, ()>>>(&self, mut it: It) -> AFactor<'a, ()> where 'k : 'a {
        static prefix: [u8; 3] = [item_byte(Tag::Arity(2)), item_byte(Tag::SymbolSize(1)), b'+'];
        let rz = it.next().unwrap();
        let rz = PrefixZipper::new(&prefix[..], rz);
        AFactor::PosSource(rz)
    }
}

pub enum ASource { PosSource(PosSource) }

#[derive(PolyZipper)]
pub enum AFactor<'trie, V: Clone + Send + Sync + Unpin = ()> {
    PosSource(PrefixZipper<'trie, ReadZipperUntracked<'trie, 'trie, V>>),
}

impl Source for ASource {
    fn new(e: Expr) -> Self {
        if unsafe { *e.ptr == item_byte(Tag::Arity(2)) && *e.ptr.offset(1) == item_byte(Tag::SymbolSize(1)) && *e.ptr.offset(2) == b'+' } {
            ASource::PosSource(PosSource::new(e))
        } else {
            unreachable!()
        }
    }

    fn request(&self) -> impl Iterator<Item=&'static [u8]> {
        match self { ASource::PosSource(s) => { s.request() } }
    }

    fn source<'a, 'k, It: Iterator<Item=ReadZipperUntracked<'a, 'k, ()>>>(&self, it: It) -> AFactor<'a, ()> where 'k : 'a {
        match self { ASource::PosSource(s) => { s.source(it) } }
    }
}
