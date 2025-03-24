
extern crate alloc;
use alloc::borrow::Cow;
use std::time::Instant;

use bucket_map::{SharedMapping, SharedMappingHandle};
use mork_frontend::bytestring_parser::{Parser, ParserError, Context};
use mork_bytestring::{Expr, ExprZipper};
use pathmap::{trie_map::BytesTrieMap, zipper::{ReadZipperTracked, WriteZipperTracked, ZipperCreation, ZipperHeadOwned, ZipperMoving, ZipperReadOnly, ZipperWriting}};

use crate::space::ParDataParser;

/// A path in the space, expressed in terms of the space's semantic
pub type Path = [u8];

/// Converts the semantic path into a [PathMap] bytes path
pub fn path_as_bytes(path: &Path) -> Cow<[u8]> {
    Cow::from(path)
}

/// The number of S-Expressions returned by [Space::load_sexpr]
type SExprCount     = usize;

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
    fn read_zipper<'r, 's>(&self, reader: &'r mut Self::Reader<'s>) -> impl ZipperMoving + ZipperReadOnly<'s, ()> + 'r;

    /// Gets a write zipper from a Writer
    fn write_zipper<'w, 's>(&self, writer: &'w mut Self::Writer<'s>) -> impl ZipperMoving + ZipperWriting<()> + 'w;

    /// Returns a handle to the `Space`'s [bucket_map] symbol table.
    fn symbol_table(&self) -> &SharedMappingHandle;

    /// Parses and loads a buffer of S-Expressions into the `Space`
    ///
    /// Returns the number of expressions loaded into the space
    fn load_sexpr(&mut self, data: &str, dst: &mut Self::Writer<'_>) -> Result<SExprCount, Self::Err> {
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
    fn read_zipper<'r, 's>(&self, reader: &'r mut Self::Reader<'s>) -> impl ZipperMoving + ZipperReadOnly<'s, ()> + 'r {
        reader
    }
    fn write_zipper<'w, 's>(&self, writer: &'w mut Self::Writer<'s>) -> impl ZipperMoving + ZipperWriting<()> + 'w {
        writer
    }
    fn symbol_table(&self) -> &SharedMappingHandle {
        &self.sm
    }
}
