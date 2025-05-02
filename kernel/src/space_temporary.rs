
extern crate alloc;
use alloc::borrow::Cow;

use bucket_map::{SharedMapping, SharedMappingHandle};
use mork_frontend::bytestring_parser::{Parser, ParserError, Context};
use mork_bytestring::{Expr, ExprZipper};
use pathmap::{trie_map::BytesTrieMap, zipper::*};


use crate::space::{
    dump_as_sexpr_impl,
    load_csv_impl,
    load_json_impl,
    load_neo4j_node_labels_impl,
    load_neo4j_node_properties_impl,
    load_neo4j_triples_impl,
    load_sexpr_impl,
    transform_multi_multi_impl,
    ParDataParser
};

/// The number of S-Expressions returned by [Space::load_sexpr]
pub type SExprCount     = usize;
pub type PathCount      = usize;
pub type AttributeCount = usize;
pub type NodeCount      = usize;
pub type OwnedExpr      = Vec<u8>;
/// A path in the space, expressed in terms of the space's semantic
pub type Path = [u8];

/// Converts the semantic path into a [PathMap] bytes path
pub fn path_as_bytes(path: &Path) -> Cow<[u8]> {
    Cow::from(path)
}

// One should not depend on the string representation of debug as per standard lib. this gives us the room to make these types better later.
#[allow(unused)]
#[derive(Debug)]
pub struct DumpSExprError(String);
#[allow(unused)]
#[derive(Debug)]
pub struct ParseError(String);
#[cfg(feature="neo4j")]
#[allow(unused)]
#[derive(Debug)]
pub struct LoadNeo4JTriplesError(String);
#[cfg(feature="neo4j")]
#[allow(unused)]
#[derive(Debug)]
pub struct LoadNeo4JNodePropertiesError(String);
#[cfg(feature="neo4j")]
#[allow(unused)]
#[derive(Debug)]
pub struct LoadNeo4JNodeLabelsError(String);



pub trait SpaceReaderZipper<'s, 'r> :ZipperMoving + ZipperReadOnlyValues<'s, ()> + ZipperReadOnlySubtries<'s, ()> + ZipperIteration<'s, ()> + ZipperAbsolutePath + 'r {}
impl<'s, 'r, T > SpaceReaderZipper<'s, 'r> for T where T : ZipperMoving + ZipperReadOnlyValues<'s, ()> + ZipperReadOnlySubtries<'s, ()> + ZipperIteration<'s, ()> + ZipperAbsolutePath + 'r {}

/// An interface for accessing the state used by the MORK kernel
pub trait Space {
    /// An authentication token used for access to the space
    type Auth;
    /// Objects of this type encapsulate a location in the space and the rights to read from that location
    type Reader<'space> where Self: 'space;
    /// Objects of this type encapsulate a location in the space and the rights to write to that location
    type Writer<'space> where Self: 'space;
    /// An error type for when a new reader or writer cannot be authenticated.
    type PermissionErr;

    // ===================== Methods used by caller ===================== 

    /// Requests a new [Space::Reader] from the `Space`
    fn new_reader<'space>(&'space self, path: &Path, auth: &Self::Auth) -> Result<Self::Reader<'space>, Self::PermissionErr>;

    /// Requests a new [Space::Writer] from the `Space`
    fn new_writer<'space>(&'space self, path: &Path, auth: &Self::Auth) -> Result<Self::Writer<'space>, Self::PermissionErr>;

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
    fn write_zipper<'w, 's: 'w>(&'s self, writer: &'w mut Self::Writer<'s>) -> impl ZipperMoving + ZipperWriting<()> /* + ZipperAbsolutePath */ + 'w;

    /// Returns a handle to the `Space`'s [bucket_map] symbol table.
    fn symbol_table(&self) -> &SharedMappingHandle;

    /// Parses and loads a buffer of S-Expressions into the `Space`
    ///
    /// Returns the number of expressions loaded into the space
    fn load_sexpr<'s>(
        &'s self,
        src_data        : &str,
        pattern         : Expr,
        template        : Expr,
        template_writer : &mut Self::Writer<'s>,
    ) -> Result<PathCount, ParseError> {
        load_sexpr_impl(
            &self.symbol_table(),
            src_data,
            pattern,
            template,
            self.write_zipper(template_writer)
        ).map_err(|e|ParseError(format!("{e:?}")))
    }


    fn sexpr_to_expr(&self, sexpr :  &str) -> Result<OwnedExpr, ParseError> {
        sexpr_to_path(self.symbol_table(), sexpr)
    }


    fn dump_as_sexpr<'s, W : std::io::Write>(
        &'s self,
        writer   : &mut W,
        (prefix_reader, pattern)  : (&mut Self::Reader<'s>, Expr),
        template : Expr,
    )  -> Result<PathCount, DumpSExprError> {
        dump_as_sexpr_impl(self.symbol_table(), pattern, self.read_zipper(prefix_reader), template, writer, 
        || "IO Write Error")
        .map_err(|e| DumpSExprError( e.to_string() ))
    }

    fn load_csv<'s>(
        &'s self,
        src_data        : &str,
        pattern         : Expr,
        template        : Expr,
        template_writer : &mut Self::Writer<'s>,
    ) -> Result<PathCount, ParseError> {
        load_csv_impl(
            &self.symbol_table(), 
            src_data,
            pattern,
            template,
            self.write_zipper(template_writer)
        ).map_err(|_| ParseError("UnexpectedParseError".to_string()))
    }

    fn load_json_old<'s>(&'s self, src_data: &str, dst: &mut Self::Writer<'s>) -> Result<PathCount, ParseError> {
        let mut wz = self.write_zipper(dst);
        let sm = self.symbol_table();
        load_json_impl(sm, &mut wz, src_data).map_err(ParseError)
    }

    fn transform_multi_multi<'s>(
        &'s self,
        patterns : &[Expr],
        pattern_readers : &'s mut[Self::Reader<'s>],
        template : &[Expr],
        template_writer : &mut [Self::Writer<'s>],

    ) {
        let readers = pattern_readers.iter_mut().map(|r| self.read_zipper(r)).collect::<Vec<_>>();
        let template_prefixes: Vec<_> = template.iter().map(|e| unsafe { e.prefix().unwrap_or_else(|_| e.span()).as_ref().unwrap() }).collect();
        let mut template_wzs: Vec<_> = template_writer.iter_mut().map(|p| self.write_zipper(p)).collect();

        transform_multi_multi_impl(patterns, &readers, template, &template_prefixes, &mut template_wzs);
    }

    #[cfg(feature="neo4j")]
    fn load_neo4j_triples<'s>(&'s self, writer : &mut Self::Writer<'s>, rt : &tokio::runtime::Handle, uri: &str, user: &str, pass: &str) -> Result<PathCount, LoadNeo4JTriplesError> {
        let sm = self.symbol_table();
        let mut wz = self.write_zipper(writer);
        load_neo4j_triples_impl(sm, &mut wz, rt, uri, user, pass).map_err(LoadNeo4JTriplesError)
    }

    #[cfg(feature="neo4j")]
    fn load_neo4j_node_properties<'s>(&'s self, writer : &mut Self::Writer<'s>, rt : &tokio::runtime::Handle, uri: &str, user: &str, pass: &str) -> Result<(NodeCount, AttributeCount), LoadNeo4JNodePropertiesError> {
        let sm = self.symbol_table();
        let mut wz = self.write_zipper(writer);
        load_neo4j_node_properties_impl(sm, &mut wz, rt, uri, user, pass).map_err(LoadNeo4JNodePropertiesError)
    }

    #[cfg(feature="neo4j")]
    fn load_neo4j_node_labels<'s>(&'s self, writer : &mut Self::Writer<'s>, rt : &tokio::runtime::Handle, uri: &str, user: &str, pass: &str) -> Result<(NodeCount, AttributeCount), LoadNeo4JNodeLabelsError> {
        let sm = self.symbol_table();
        let mut wz = self.write_zipper(writer);
        load_neo4j_node_labels_impl(sm, &mut wz, rt, uri, user, pass).map_err(LoadNeo4JNodeLabelsError)
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
    type PermissionErr = String;

    fn new_reader<'space>(&'space self, path: &Path, _auth: &Self::Auth) -> Result<Self::Reader<'space>, Self::PermissionErr> {
        let path = path_as_bytes(path);
        self.map.read_zipper_at_path(path).map_err(|e| e.to_string())
    }
    fn new_writer<'space>(&'space self, path: &Path, _auth: &Self::Auth) -> Result<Self::Writer<'space>, Self::PermissionErr> {
        let path = path_as_bytes(path);
        self.map.write_zipper_at_exclusive_path(path).map_err(|e| e.to_string())
    }
    fn read_zipper<'r, 's: 'r>(&'s self, reader: &'r mut Self::Reader<'s>) -> impl  ZipperMoving + ZipperReadOnlyValues<'s, ()> + ZipperReadOnlySubtries<'s, ()> + ZipperIteration<'s, ()> + ZipperAbsolutePath + 'r {
        reader.reset();
        reader
    }
    fn write_zipper<'w, 's: 'w>(&'s self, writer: &'w mut Self::Writer<'s>) -> impl ZipperMoving + ZipperWriting<()> /* + ZipperAbsolutePath */ + 'w {
        writer.reset();
        writer
    }
    fn symbol_table(&self) -> &SharedMappingHandle {
        &self.sm
    }
}

pub(crate) fn sexpr_to_path(sm : &SharedMappingHandle, data: &str) -> Result<OwnedExpr, ParseError> {
    let mut it = Context::new(data.as_bytes());
    let mut stack = [0u8; 2048];
    let mut parser = ParDataParser::new(sm);
    let mut result = None;
    loop {
        let mut ez = ExprZipper::new(Expr{ptr: stack.as_mut_ptr()});
        match parser.sexpr(&mut it, &mut ez) {
            Ok(()) => {
                if result.is_some() {
                    return Err(ParseError(format!("Found multiple S-Expressions in: {data}")))
                }
                result = Some(stack[..ez.loc].to_vec());
            }
            Err(ParserError::InputFinished) => { break }
            Err(other) => { return Err(ParseError(format!("Internal Parse error: {other:?}"))) }
        }
        it.variables.clear();
    }

    result.ok_or_else(|| ParseError(format!("Failed to parse S-Expression: {data}")))
}

