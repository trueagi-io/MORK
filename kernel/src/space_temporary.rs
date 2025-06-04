
extern crate alloc;
use std::io::{BufRead, Read};

use alloc::borrow::Cow;

use bucket_map::{SharedMapping, SharedMappingHandle};
use mork_frontend::bytestring_parser::{ParseContext, Parser, ParserError, ParserErrorType};
use mork_bytestring::{Expr, OwnedExpr, ExprZipper};
use pathmap::{trie_map::BytesTrieMap, morphisms::Catamorphism, zipper::*};


use crate::space::{
    self, dump_as_sexpr_impl, load_csv_impl, load_json_impl, load_neo4j_node_labels_impl, load_neo4j_node_properties_impl, load_neo4j_triples_impl, load_sexpr_impl, transform_multi_multi_impl, token_bfs_impl, ParDataParser
};

/// The number of S-Expressions returned by [Space::load_sexpr]
pub type SExprCount     = usize;
pub type PathCount      = usize;
pub type AttributeCount = usize;
pub type NodeCount      = usize;

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

pub trait SpaceReaderZipper<'s> : ZipperMoving + ZipperReadOnlyValues<'s, ()> + ZipperReadOnlyIteration<'s, ()> + ZipperReadOnlySubtries<'s, ()> + ZipperIteration + Catamorphism<()> + ZipperAbsolutePath + ZipperPathBuffer + ZipperForking<()> {}
impl<'s, T> SpaceReaderZipper<'s> for T where T : ZipperMoving + ZipperReadOnlyValues<'s, ()> + ZipperReadOnlyIteration<'s, ()> + ZipperReadOnlySubtries<'s, ()> + ZipperIteration + Catamorphism<()> + ZipperAbsolutePath + ZipperPathBuffer + ZipperForking<()> {}

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
    fn new_reader<'space>(&'space self, path: &[u8], auth: &Self::Auth) -> Result<Self::Reader<'space>, Self::PermissionErr>;

    /// Requests a new [Space::Writer] from the `Space`
    fn new_writer<'space>(&'space self, path: &[u8], auth: &Self::Auth) -> Result<Self::Writer<'space>, Self::PermissionErr>;

    // ===================== Methods used by shared impl ===================== 

    /// Gets a read zipper from a Reader
    ///
    /// NOTE: The `&mut Self::Reader` argument ensures exclusivity, but the `Reader` does
    /// not conceptually have mutable state
    fn read_zipper<'r, 's: 'r>(&'s self, reader: &'r mut Self::Reader<'s>) -> impl SpaceReaderZipper<'s>;

    /// Gets a write zipper from a Writer
    ///
    /// NOTE: The `&mut Self::Writer` argument ensures exclusivity, but the `Writer` does
    /// not conceptually have mutable state
    fn write_zipper<'w, 's: 'w>(&'s self, writer: &'w mut Self::Writer<'s>) -> impl ZipperMoving + ZipperWriting<()> + ZipperForking<()> + /* ZipperAbsolutePath +  */'w;

    /// Returns a handle to the `Space`'s [bucket_map] symbol table.
    fn symbol_table(&self) -> &SharedMappingHandle;

    /// Parses and loads a buffer of S-Expressions into the `Space`
    ///
    /// Returns the number of expressions loaded into the space
    fn load_sexpr<'s, SrcStream: Read + BufRead>(
        &'s self,
        src_data        : SrcStream,
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

    fn load_csv<'s, SrcStream: BufRead>(
        &'s self,
        src_data        : SrcStream,
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

    /// Explore a limited number of paths below a focus position
    ///
    /// `focus_token` represents a location within `pattern` and thus accessible from `pattern_reader`.  Externally,
    /// it is an opaque token.  Internally, it is simply a relative PathMap path, althoug the format may change in
    /// the future.
    ///
    /// Usage:
    /// 1. Start exploration from the `pattern` by passing `&[]` as `focus_token`.
    /// 2. This will return a vector of, at most, 256 disjoint result sets.  Each result set is represented by a
    ///  pair of `(focus_token, sample_expr)`. The `sample_expr` represents one expression from within the set,
    ///  although the chosen expression is arbitrary and can't be relied upon.
    /// 3. The `focus_token` can be used to recursively continue exploration by calling the method again using
    ///  the same `pattern` and `pattern_reader`, but with the new `focus_token`.  Subsequent results are now relative
    ///  to the prior result set.
    /// 4. A zero-length result vector means the `sample_expr` that was paired with the `focus_token` is a singleton
    ///  within its result set.  A zero-length result vector when `focus_token == &[]` means the subspace is empty
    ///
    fn token_bfs<'s>(&'s self, focus_token: &[u8], pattern: Expr, pattern_reader: &mut Self::Reader<'s>) -> Vec<(Vec<u8>, OwnedExpr)> {
        token_bfs_impl(
            focus_token,
            pattern,
            self.read_zipper(pattern_reader)
        )
    }

    fn transform_multi_multi<'s>(
        &'s self,
        patterns : &[Expr],
        pattern_readers : &mut[Self::Reader<'s>],
        template : &[Expr],
        template_writer : &mut [Self::Writer<'s>],
    ) -> (usize, bool) {
        core::debug_assert_eq!(patterns.len(), pattern_readers.len());
        core::debug_assert_eq!(template.len(), template_writer.len());

        // until dangling paths are fixed, the aquisition order matters, writers first, then readers

        // FIRST THE WRITERS
        let template_prefixes: Vec<_> = template.iter().map(|e| unsafe { e.prefix().unwrap_or_else(|_| e.span()).as_ref().unwrap() }).collect();
        let mut template_wzs: Vec<_> = template_writer.iter_mut().map(|p| self.write_zipper(p)).collect();

        // SECOND THE READERS
        let readers = pattern_readers.iter_mut().map(|r| self.read_zipper(r)).collect::<Vec<_>>();

        transform_multi_multi_impl(patterns, &readers, template, &template_prefixes, &mut template_wzs)
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

pub(crate) fn sexpr_to_path(sm : &SharedMappingHandle, data: &str) -> Result<OwnedExpr, ParseError> {
    let mut it = ParseContext::new(data.as_bytes());
    let mut stack = [0u8; 2048];
    let mut parser = ParDataParser::new(sm);
    let mut result = None;
    loop {
        let mut ez = ExprZipper::new(Expr{ptr: stack.as_mut_ptr()});
        match parser.sexpr_(&mut it, &mut ez) {
            Ok(()) => {
                if result.is_some() {
                    return Err(ParseError(format!("Found multiple S-Expressions in: {data}")))
                }
                result = Some(stack[..ez.loc].into());
            }
            Err(err) => {
                if err.error_type == ParserErrorType::InputFinished {
                    break
                } else {
                    return Err(ParseError(format!("{err:?}")))
                }
            }
        }
    }

    result.ok_or_else(|| ParseError(format!("Failed to parse S-Expression: {data}")))
}

