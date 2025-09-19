
extern crate alloc;
use std::io::{BufRead, Read};
use std::ptr::slice_from_raw_parts;
use log::*;

use bucket_map::SharedMappingHandle;
use mork_frontend::{bytestring_parser::{ParseContext, Parser, ParserErrorType}};
use mork_bytestring::{Expr, ExprTrait, OwnedExpr, ExprZipper};
use pathmap::{PathMap, morphisms::Catamorphism, zipper::*};

use crate::multi_zipper::MultiZipper;
use crate::space::{
    ExecError, dump_as_sexpr_impl, load_csv_impl, load_json_impl, load_sexpr_impl, transform_multi_multi_impl, metta_calculus_impl, token_bfs_impl, ParDataParser
};

#[cfg(feature="neo4j")]
use crate::space::{
    load_neo4j_node_labels_impl, load_neo4j_node_properties_impl, load_neo4j_triples_impl
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

pub trait GetPathmap<'trie> {
    fn get_pathmap(&self) -> Option<&ReadZipperUntracked<'trie, 'trie, ()>>;
}

pub trait SpaceReaderZipper<'s> : ZipperMoving + ZipperReadOnlyConditionalValues<'s, ()> + ZipperReadOnlyConditionalIteration<'s, ()> + ZipperIteration + Catamorphism<()> + ZipperAbsolutePath + ZipperPathBuffer + ZipperForking<()> + GetPathmap<'s> {}
impl<'s, T> SpaceReaderZipper<'s> for T where T : ZipperMoving + ZipperReadOnlyConditionalValues<'s, ()> + ZipperReadOnlyConditionalIteration<'s, ()> + ZipperIteration + Catamorphism<()> + ZipperAbsolutePath + ZipperPathBuffer + ZipperForking<()> + GetPathmap<'s> {}

pub trait SpaceWriterZipper : ZipperMoving + ZipperWriting<()> + ZipperForking<()> + ZipperAbsolutePath {}
impl<T> SpaceWriterZipper for T where T : ZipperMoving + ZipperWriting<()> + ZipperForking<()> + ZipperAbsolutePath {}

/// Implemented on a type that can be returned by a failure to acquire a permission
pub trait PathPermissionErr: core::fmt::Debug {
    /// Returns the path to which access was forbidden
    fn path(&self) -> &[u8];
}

/// Implemented on an object that assigns permissions for a [Space]
///
/// A given `PermissionArb` object must never be capable of assigning conflicting permissions
/// with another `PermissionArb` object.
pub trait PermissionArb<'space, S: Space> {
    /// Requests a new [Space::Reader] from the `Space`
    fn new_reader(&self, path: &[u8], auth: &S::Auth) -> Result<S::Reader<'space>, S::PermissionErr>;

    /// Requests a new [Space::Writer] from the `Space`
    fn new_writer(&self, path: &[u8], auth: &S::Auth) -> Result<S::Writer<'space>, S::PermissionErr>;
}

/// An interface for accessing the state used by the MORK kernel
pub trait Space: Sized {
    /// An authentication token used for access to the space
    type Auth;
    /// Objects of this type encapsulate a location in the space and the rights to read from that location
    type Reader<'space> where Self: 'space;
    /// Objects of this type encapsulate a location in the space and the rights to write to that location
    type Writer<'space> where Self: 'space;
    /// An object from which reader and writer permissions may be acquired within the space
    type PermissionHead<'space>: PermissionArb<'space, Self> where Self: 'space;
    /// An error type for when a new reader or writer cannot be authenticated.
    type PermissionErr: PathPermissionErr;

    // ===================== Methods intended for use from outside the space ===================== 

    /// Atomically request multiple permissions.  Ensures no other requests for permissions will be
    /// granted while the supplied closure is running.
    ///
    /// If a single requested permission cannot be fulfilled, the enture request should fail
    fn new_multiple<'space, F: FnOnce(&Self::PermissionHead<'space>)->Result<(), Self::PermissionErr>>(&'space self, f: F) -> Result<(), Self::PermissionErr>;

    /// Requests a new [Space::Reader] from the `Space`
    fn new_reader<'space>(&'space self, path: &[u8], auth: &Self::Auth) -> Result<Self::Reader<'space>, Self::PermissionErr> {
        let mut reader = None;
        self.new_multiple(|perm_head| {
            reader = Some(perm_head.new_reader(path, auth)?);
            Ok(())
        })?;
        Ok(reader.unwrap())
    }

    /// Requests a new [Space::Writer] from the `Space`
    fn new_writer<'space>(&'space self, path: &[u8], auth: &Self::Auth) -> Result<Self::Writer<'space>, Self::PermissionErr> {
        let mut writer = None;
        self.new_multiple(|perm_head| {
            writer = Some(perm_head.new_writer(path, auth)?);
            Ok(())
        })?;
        Ok(writer.unwrap())
    }

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
    fn write_zipper<'w, 's: 'w>(&'s self, writer: &'w mut Self::Writer<'s>) -> impl SpaceWriterZipper + 'w;

    /// Removes the WriteZipper from the ZipperHead
    fn cleanup_write_zipper(&self, wz: impl SpaceWriterZipper);

    /// Attempts to acquire a new writer at `path`, but retries in a loop instead of failing immediately
    fn new_writer_retry<'space>(&'space self, path: &[u8], attempts: usize, auth: &Self::Auth) -> Result<Self::Writer<'space>, Self::PermissionErr> {
        let mut attempts = attempts.max(1);
        let mut err = None;
        while attempts > 0 {
            match self.new_writer(path, auth) {
                Ok(writer) => return Ok(writer),
                Err(e) => { 
                    std::thread::sleep(core::time::Duration::from_micros(500));
                    err = Some(e);
                } 
            };
            attempts -= 1;
        }
        Err(err.unwrap())
    }

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

    fn sexpr_to_expr(&self, sexpr:  &str) -> Result<OwnedExpr, ParseError> {
        sexpr_to_path(self.symbol_table(), sexpr)
    }

    fn dump_as_sexpr<'s, W : std::io::Write>(
        &'s self,
        writer   : &mut W,
        (prefix_reader, pattern)  : (&mut Self::Reader<'s>, Expr),
        template : Expr,
        max_write: usize
    )  -> Result<PathCount, DumpSExprError> {
        let s = "IoWriteError";
        let mut error = false;
        let c = dump_as_sexpr_impl(self.symbol_table(), pattern, self.read_zipper(prefix_reader), template, writer,
                           || unsafe { std::ptr::write_volatile(&mut error, true); }, max_write);
        if error { Err(DumpSExprError(s.to_string())) } else { Ok(c) }
    }

    fn load_csv<'s, SrcStream: BufRead>(
        &'s self,
        src_data        : SrcStream,
        pattern         : Expr,
        template        : Expr,
        template_writer : &mut Self::Writer<'s>,
        separator       : u8,
        include_line_nums: bool
    ) -> Result<PathCount, ParseError> {
        load_csv_impl(
            &self.symbol_table(), 
            src_data,
            pattern,
            template,
            self.write_zipper(template_writer),
            separator,
            include_line_nums,
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

    /// Acquires the minimum set of permissions needed to perform a transform by applying the necessary
    /// subsumption logic
    ///
    /// The return value is: `(read_map, template_prefixes, writers)`
    ///
    /// * read_map: PathMap<()>
    ///    A PathMap in which all readers can be acquired
    ///
    /// * template_prefixes: Vec<(usize, usize)>
    ///    A vec of `(incremental_path_start, writer_idx)`, corresponding to the `templates` where:
    ///     - `incremental_path_start`: The index in the full template path for the start of the part of the path
    ///        that is not subsumed by the writer's root path.
    ///     - `writer_idx`: The index into `writers` for the write permssion to use for this expr
    ///
    /// * writers: Vec<Self::Writer<'s>>
    ///    A vector of [Space::Writer] permission objects
    ///
    fn acquire_transform_permissions<'s, E: ExprTrait>(
        &'s self,
        patterns            : &[E],
        templates           : &[E],
        auth                : &Self::Auth,
    ) -> Result<(PathMap<()>, Vec<(usize, usize)>, Vec<Self::Writer<'s>>), ExecError<Self>> {
        let make_prefix = |e:&Expr|  unsafe { e.prefix().unwrap_or_else(|_| e.span()).as_ref().unwrap() };

        // ************************************************************************
        // Writer subsumption logic (No permissions acquired yet)
        // ************************************************************************

        //Make a vec of template paths, sorted from shortest to longest
        // `(path, template_idx, writer_slot_idx)`
        let mut template_path_table: Vec<(&[u8], usize, usize)> = templates.iter().enumerate().map(|(i, template)|{
            let path = make_prefix(&template.borrow());
            (path, i, 0)
        }).collect();
        template_path_table.sort_by(|a, b| a.0.len().cmp(&b.0.len()));

        //Find the set of least-common-denominator template prefixes
        let mut writer_slots: Vec<&[u8]> = Vec::with_capacity(templates.len());
        for (path, _template_idx, writer_slot_idx) in template_path_table.iter_mut() {
            let mut subsumed = false;
            for (slot_idx, slot_path) in writer_slots.iter().enumerate() {
                let overlap = pathmap::utils::find_prefix_overlap(path, slot_path);
                if overlap == slot_path.len() {
                    *writer_slot_idx = slot_idx;
                    subsumed = true;
                    break
                }
            }
            if !subsumed {
                *writer_slot_idx = writer_slots.len();
                writer_slots.push(path);
            }
        }

        //Untangle the prefixes into the `template_prefixes` format from [TransformPermissions::template_prefixes]
        let mut template_prefixes = vec![(0, 0); templates.len()];
        for (_, template_idx, writer_slot_idx) in template_path_table {
            let incremental_path_start = writer_slots[writer_slot_idx].len();
            template_prefixes[template_idx] = (incremental_path_start, writer_slot_idx);
        }

        // ************************************************************************
        // Permission Acquisition
        // ************************************************************************

        let mut read_map = PathMap::new();
        let mut writers = Vec::with_capacity(writer_slots.len());
        self.new_multiple(|perm_head| {

            //Make the "ReadMap" by copying each pattern from the space
            for pat in patterns {
                let path = make_prefix(&pat.borrow());

                let mut reader = perm_head.new_reader(path, auth)?;
                let rz = self.read_zipper(&mut reader);
                let rz_head = rz.get_pathmap()
                    .expect("trying to graft with ACTree");
                    // .ok_or_else(|| ExecError::OtherFmtErr("".to_string()))?;
                let mut wz = read_map.write_zipper_at_path(path);
                wz.graft(rz_head);
            }

            //Acquire writers at each slot, knowing we any conflicts are with external clients
            for path in writer_slots {
                let writer = perm_head.new_writer(path, auth)?;
                writers.push(writer);
            }

            Ok(())
        }).map_err(|perm_err| ExecError::perm_err(self, perm_err))?;

        trace!(target: "transform", "templates {:?}", templates);
        trace!(target: "transform", "prefixes {:?}", template_prefixes);

        Ok(( read_map, template_prefixes, writers ))
    }

    fn transform_multi_multi<'s, E: ExprTrait>(
        &'s self,
        patterns : &[E],
        read_map: &PathMap<()>,
        templates : &[E],
        template_prefixes : &[(usize, usize)],
        writers : &mut [Self::Writer<'s>],
    ) -> (usize, bool) {
        let make_prefix = |e:&Expr|  unsafe { e.prefix().unwrap_or_else(|_| e.span()).as_ref().unwrap() };

        let pattern_rzs: Vec<_> = patterns.iter().map(|pat| {
            let path = make_prefix(&pat.borrow());
            read_map.read_zipper_at_borrowed_path(path)
        }).collect();

        let mut template_wzs: Vec<_> = writers.iter_mut().map(|writer| self.write_zipper(writer)).collect();

        let result = transform_multi_multi_impl(patterns, pattern_rzs, templates, template_prefixes, &mut template_wzs);

        for wz in template_wzs {
            self.cleanup_write_zipper(wz);
        }
        result
    }

    /// Executes a MeTTa thread
    ///
    /// GOAT, TODO.  This also needs to take a callback that is called each trip through the loop, in order to
    ///  facilitate logging of sub-commands in the server
    fn metta_calculus<'s>(&'s self,
        thread_id_sexpr_str: &str,
        step_cnt: usize,
        auth: &Self::Auth
    ) -> Result<(), ExecError<Self>>
    {
        metta_calculus_impl(self, thread_id_sexpr_str, 2000, step_cnt, auth)
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
    let mut stack = Vec::with_capacity(1 << 32);
    let mut parser = ParDataParser::new(sm);
    let mut result = None;
    loop {
        let mut ez = ExprZipper::new(Expr{ptr: stack.as_mut_ptr()});
        match parser.sexpr_(&mut it, &mut ez) {
            Ok(()) => {
                if result.is_some() {
                    return Err(ParseError(format!("Found multiple S-Expressions in: {data}")))
                }
                result = Some(unsafe { slice_from_raw_parts(stack.as_ptr(), ez.loc).as_ref().unwrap() }.into());
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

