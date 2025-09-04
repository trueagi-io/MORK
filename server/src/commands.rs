use core::pin::Pin;
use std::collections::BTreeMap;
use std::future::Future;
use std::mem::MaybeUninit;
use std::path::Path;
use std::io::{BufRead, BufReader, Read, Write};
use std::any::Any;
use std::path::PathBuf;
use std::ptr::slice_from_raw_parts;
use std::sync::Arc;
use std::usize;

use gxhash::gxhash64;
use mork::{OwnedExpr, ExprTrait};
use mork::{Space, space::serialize_sexpr_into};
use pathmap::zipper::{ZipperIteration, ZipperMoving, ZipperWriting, ZipperReadOnlyConditionalIteration, ZipperReadOnlyConditionalValues, ZipperAbsolutePath};
use tokio::fs::File;
use tokio::io::{BufWriter, AsyncWriteExt};

use bytes::BytesMut;
use hyper::{Request, StatusCode};
use hyper::body::{Incoming as IncomingBody, Bytes, Frame};
use http_body_util::BodyExt;
use tokio::sync::mpsc;
use tokio_stream::{StreamExt, wrappers::ReceiverStream};
use futures_util::Stream;
use url::Url;
use mork_bytestring::{Expr, ExprZipper};
use super::{BoxedErr, MorkService, WorkThreadHandle};
use super::status_map::{StatusRecord, FetchError, ParseError};
use super::resource_store::ResourceHandle;
use super::server_space::*;
use super::status_map::*;

pub type BoxStream = Pin<Box<dyn Stream<Item = Result<Frame<Bytes>, hyper::Error>> + Send + Sync + 'static>>;

pub enum WorkResult {
    Immediate(Bytes), // previous behavior
    Streamed(BoxStream),  // support for streaming responses
}

impl WorkResult {
    pub fn is_immediate(&self) -> bool {
        match self {
            WorkResult::Immediate(_) => true,
            WorkResult::Streamed(_) => false,
        }
    }

    pub fn is_streamed(&self) -> bool {
        match self {
            WorkResult::Immediate(_) => false,
            WorkResult::Streamed(_) => true,
        }
    }

    pub fn get_bytes(&self) -> Option<Bytes> {
        match self {
            WorkResult::Immediate(b) => Some(b.clone()),
            WorkResult::Streamed(_) => None,
        }
    }
}

impl From<&str> for WorkResult {
    fn from(b: &str) -> WorkResult {
        WorkResult::Immediate(Bytes::copy_from_slice(b.as_bytes()))
    }
}

impl From<String> for WorkResult {
    fn from(b: String) -> WorkResult {
        WorkResult::Immediate(Bytes::copy_from_slice(b.as_bytes()))
    }
}

// ===***===***===***===***===***===***===***===***===***===***===***===***===***===***===***
// busywait
// ===***===***===***===***===***===***===***===***===***===***===***===***===***===***===***

/// Tie up a worker for `millis` ms.  Used to test server behavior under conditions resembling
/// heavy load
pub struct BusywaitCmd;

impl CommandDefinition for BusywaitCmd {
    const NAME: &'static str = "busywait";
    const CONST_CMD: &'static Self = &Self;
    const CONSUME_WORKER: bool = true;
    fn args() -> &'static [ArgDef] {
        &[ArgDef{
            arg_type: ArgType::UInt,
            name: "millis",
            desc: "The number of milliseconds to tie up the worker",
            required: true
        }]
    }
    fn properties() -> &'static [PropDef] {
        &[PropDef {
            arg_type: ArgType::Expr,
            name: "expr1",
            desc: "An expression to lock for the duration of the busy-wait",
            required: false
        },
        PropDef {
            arg_type: ArgType::Flag,
            name: "writer1",
            desc: "Holds write permission over expr1 if set, otherwise takes a read permission",
            required: false
        }]
    }
    async fn work(ctx: MorkService, cmd: Command, thread: Option<WorkThreadHandle>, _req: Request<IncomingBody>) -> Result<WorkResult, CommandError> {

        let expr1 = cmd.properties[0].as_ref().map(|prop| prop.as_expr_bytes());
        let writer1 = cmd.properties[1].is_some();

        let expr1 = match expr1 {
            Some(expr) => {
                let prefix = derive_prefix_from_expr_slice(expr).till_constant_to_till_last_constant();
                if writer1 {
                    Some(Box::new(ctx.0.space.new_writer_async(prefix, &()).await?) as Box<dyn Any + Send + Sync>)
                } else {
                    Some(Box::new(ctx.0.space.new_reader_async(prefix, &()).await?) as Box<dyn Any + Send + Sync>)
                }
            },
            None => None
        };

        thread.unwrap().dispatch_blocking_task(cmd, move |cmd| {
            let millis = cmd.args[0].as_u64();
            std::thread::sleep(std::time::Duration::from_millis(millis));
            drop(expr1);
            Ok(())
        }).await;
        Ok("ACK. Waiting".into())
    }
}

// ===***===***===***===***===***===***===***===***===***===***===***===***===***===***===***
// clear
// ===***===***===***===***===***===***===***===***===***===***===***===***===***===***===***

/// Clears all data at the specified path
pub struct ClearCmd;

impl CommandDefinition for ClearCmd {
    const NAME: &'static str = "clear";
    const CONST_CMD: &'static Self = &Self;
    const CONSUME_WORKER: bool = false;
    fn args() -> &'static [ArgDef] {
        &[ArgDef{
            arg_type: ArgType::Expr,
            name: "expr",
            desc: "The expression defining a subspace from which to clear.  The path is relative to the first variable in the expression, e.g. `(test (data $v) _)`",
            required: true
        }]
    }
    fn properties() -> &'static [PropDef] {
        &[]
    }
    async fn work(ctx: MorkService, cmd: Command, _thread: Option<WorkThreadHandle>, _req: Request<IncomingBody>) -> Result<WorkResult, CommandError> {
        let expr = cmd.args[0].as_expr_bytes();
        let prefix = derive_prefix_from_expr_slice(&expr).till_constant_to_till_last_constant();
        let mut writer = ctx.0.space.new_writer_async(prefix, &()).await?;

        let mut wz = ctx.0.space.write_zipper(&mut writer);
        wz.remove_branches();
        wz.remove_val();
        '_journal_event : {
            test_journal_append(b"CLEAR",format!("{:?}", prefix).as_bytes());
            // JOURNAL.append_event(Clear(prefix))

            // explictly drop wz only after Journal event complete
            drop(wz)
        }
        Ok("ACK. Cleared".into())
    }
}

// ===***===***===***===***===***===***===***===***===***===***===***===***===***===***===***
// copy
// ===***===***===***===***===***===***===***===***===***===***===***===***===***===***===***

/// Copys (by reference) the contents of `source` to `dest`.  This is PathMap::graft
pub struct CopyCmd;

impl CommandDefinition for CopyCmd {
    const NAME: &'static str = "copy";
    const CONST_CMD: &'static Self = &Self;
    const CONSUME_WORKER: bool = false;
    fn args() -> &'static [ArgDef] {
        &[ArgDef{
            arg_type: ArgType::Expr,
            name: "src_expr",
            desc: "The expression defining a subspacespace from which to copy.  The path is relative to the first variable in the expression, e.g. `(test (data $v) _)`",
            required: true
        },
        ArgDef{
            arg_type: ArgType::Expr,
            name: "dst_expr",
            desc: "The expression defining a destination subspacespace into which to copy.  The path is relative to the first variable in the expression, e.g. `(test (data $v) _)`",
            required: true
        }]
    }
    fn properties() -> &'static [PropDef] {
        &[]
    }
    async fn work(ctx: MorkService, cmd: Command, _thread: Option<WorkThreadHandle>, _req: Request<IncomingBody>) -> Result<WorkResult, CommandError> {
        let src_expr = cmd.args[0].as_expr_bytes();
        let src_prefix = derive_prefix_from_expr_slice(&src_expr).till_constant_to_till_last_constant();
        let mut reader = ctx.0.space.new_reader_async(src_prefix, &()).await?;

        let dst_expr = cmd.args[1].as_expr_bytes();
        let dst_prefix = derive_prefix_from_expr_slice(&dst_expr).till_constant_to_till_last_constant();
        let mut writer = ctx.0.space.new_writer_async(dst_prefix, &()).await?;

        let rz = ctx.0.space.read_zipper(&mut reader);
        let mut wz = ctx.0.space.write_zipper(&mut writer);
        wz.graft(&rz);


        '_journal_event : {
            test_journal_append(b"COPY", &format!("src({:?}) -> dst({:?})", src_expr, dst_expr).as_bytes());
            // JOURNAL.append_event(Copy( (src_expr, dst_expr)) ) // maybe Sexpr?

            // explictly drop (wz,rz) only after Journal event complete
            drop((wz,rz))
        }

        Ok("ACK. Copied".into())
    }
}

// ===***===***===***===***===***===***===***===***===***===***===***===***===***===***===***
// count
// ===***===***===***===***===***===***===***===***===***===***===***===***===***===***===***

/// Returns a count of values below the specified path.
pub struct CountCmd;

impl CommandDefinition for CountCmd {
    const NAME: &'static str = "count";
    const CONST_CMD: &'static Self = &Self;
    const CONSUME_WORKER: bool = true;
    fn args() -> &'static [ArgDef] {
        &[ArgDef{
            arg_type: ArgType::Expr,
            name: "expr",
            desc: "The expression in the map at which to count the values.  The path is relative to the first variable in the expression, e.g. `(test (data $v) _)`",
            required: true
        }]
    }
    fn properties() -> &'static [PropDef] {
        &[]
    }
    async fn work(ctx: MorkService, cmd: Command, thread: Option<WorkThreadHandle>, _req: Request<IncomingBody>) -> Result<WorkResult, CommandError> {
        let expr = cmd.args[0].as_expr_bytes();
        let prefix = derive_prefix_from_expr_slice(&expr).till_constant_to_till_last_constant();
        let reader = ctx.0.space.new_reader_async(prefix, &()).await?;

        tokio::task::spawn(async move {
            match do_count(&ctx, thread.unwrap(), &cmd, reader).await {
                Ok(()) => {},
                Err(err) => {
                    println!("Internal Error occurred during count: {err:?}"); //GOAT Log this error
                }
            }
            async { () }
        });
        Ok("ACK. Starting Count".into())
    }
}

async fn do_count(ctx: &MorkService, thread: WorkThreadHandle, _cmd: &Command, mut reader: ReadPermission) -> Result<(), CommandError> {

    let ctx_clone = ctx.clone();
    tokio::task::spawn_blocking(move || -> Result<(), CommandError> {
        let rz = ctx_clone.0.space.read_zipper(&mut reader);
        let count = rz.val_count();
        drop(rz);

        ctx_clone.0.space.set_user_status(reader.path(), StatusRecord::CountResult(count.into()))?;
        Ok(())
    }).await??;

    thread.finalize().await;
    println!("Count command successful"); //GOAT Log this!
    Ok(())
}

// ===***===***===***===***===***===***===***===***===***===***===***===***===***===***===***
// explore
// ===***===***===***===***===***===***===***===***===***===***===***===***===***===***===***

/// Explore a limited number of paths below a focus position, within an expression's subspace
///
/// `focus_token` represents a location within `pattern` and thus accessible from `pattern_reader`.  It should
/// be treated as opaque bytes.
///
/// Usage:
/// 1. Start exploration from the `expr` by passing an empty `focus_token` (use a trailing '/').
/// 2. This will return at most 256 pairs.  Each pair represents a disjoint set of values in the subspace at or
///  below the position defined by the `focus_token` that was passed in.  Each pair includes:
///  `(focus_token, sample_expr)`. The `sample_expr` represents one arbitrarily chosen expression from within
///  the set.
/// 3. The pair's `focus_token` can be used to recursively continue exploration by calling the method again using
///  the same `pattern` and `pattern_reader`, but with the new `focus_token`.  Subsequent results are now relative
///  to the prior result set.
/// 4. A "()" response means the `sample_expr` that was paired with the prior call's `focus_token` is a singleton
///  within its result set.  A "()" response when `focus_token` is empty means the expression's subspace is empty
pub struct ExploreCmd;

impl CommandDefinition for ExploreCmd {
    const NAME: &'static str = "explore";
    const CONST_CMD: &'static Self = &Self;
    const CONSUME_WORKER: bool = true;
    fn args() -> &'static [ArgDef] {
        &[ArgDef{
            arg_type: ArgType::Expr,
            name: "expr",
            desc: "The expression within the space, from which to begin traversal",
            required: true
        },
        ArgDef{
            arg_type: ArgType::Path,
            name: "focus_token",
            desc: "An encoded representation of a subset of the subspace matched by the expression.  Pass a zero-length string to begin exploration",
            required: true
        }]
    }
    fn properties() -> &'static [PropDef] { &[] }
    async fn work(ctx: MorkService, cmd: Command, thread: Option<WorkThreadHandle>, _req: Request<IncomingBody>) -> Result<WorkResult, CommandError> {

        let expr = cmd.args[0].as_expr_bytes().to_vec();
        let prefix = derive_prefix_from_expr_slice(&expr).till_constant_to_till_last_constant();
        let reader = ctx.0.space.new_reader_async(prefix, &()).await?;

        let out = tokio::task::spawn_blocking(move || -> Result<WorkResult, CommandError> {
            do_bfs(&ctx, cmd, reader, expr)
        }).await??;

        thread.unwrap().finalize().await;
        println!("Explore command successful"); // TODO log this!

        Ok(out)
    }
}

fn do_bfs(ctx: &MorkService, cmd: Command, mut reader: ReadPermission, mut expr: Vec<u8>) -> Result<WorkResult, CommandError> {

    let focus_token = cmd.args[1].as_path();
    let result_paths = ctx.0.space.token_bfs(focus_token, mork_bytestring::Expr { ptr: expr.as_mut_ptr() }, &mut reader);

    let mut buffer = Vec::with_capacity(4096);
    let mut writer = std::io::BufWriter::new(&mut buffer);
    let mut expr_buffer = Vec::with_capacity(4096);

    let mut first = true;
    writer.write(b"[")?;
    for (new_tok, expr) in result_paths {
        if first {
            first = false
        } else {
            writer.write(b",\n")?;
        }

        writer.write(b"{\"token\": [")?;

        let mut inner_first = true;
        for &byte in new_tok.iter() {
            if inner_first {
                inner_first = false
            } else {
                writer.write(b", ")?;
            }
            writer.write(format!("{}", byte as u16).as_bytes())?;
        }

        writer.write(b"], \"expr\": ")?;

        serialize_sexpr_into(expr.borrow().ptr, &mut expr_buffer, ctx.0.space.symbol_table())
            .map_err(|e|CommandError::internal(format!("failed to serialize to MeTTa S-Expressions: {e:?}")))?;
        writer.write(serde_json::to_string(std::str::from_utf8(&expr_buffer[..])?)?.as_bytes())?;
        expr_buffer.clear();

        writer.write(b"}")?;
    }
    writer.write(b"]")?;

    writer.flush()?;
    drop(writer);

    Ok(WorkResult::Immediate(hyper::body::Bytes::from(buffer)))
}

// ===***===***===***===***===***===***===***===***===***===***===***===***===***===***===***
// export
// ===***===***===***===***===***===***===***===***===***===***===***===***===***===***===***

/// deserialize a map, serve as a file to the client. 
pub struct ExportCmd;

impl CommandDefinition for ExportCmd {
    const NAME: &'static str = "export";
    const CONST_CMD: &'static Self = &Self;
    const CONSUME_WORKER: bool = true;
    fn args() -> &'static [ArgDef] {
        &[ArgDef{
            arg_type: ArgType::String,
            name: "pattern",
            desc: "The pattern to specify the expressions to export from the space",
            required: true
        },
        ArgDef{
            arg_type: ArgType::String,
            name: "template",
            desc: "The template to specify the form of the expressions in the exported data",
            required: true
        }]
    }
    fn properties() -> &'static [PropDef] {
        &[PropDef {
            arg_type: ArgType::String,
            name: "format",
            desc: "The format to export, default is metta S-Expressions",
            required: false
        },
        PropDef {
            arg_type: ArgType::String,
            name: "uri",
            desc: "A file url to export to.  If this property is provided then the returned body won't contain any result data",
            required: false
        },
        PropDef {
            arg_type: ArgType::UInt,
            name: "max_write",
            desc: "Max number of expressions to export",
            required: false
        }]
    }
    async fn work(ctx: MorkService, cmd: Command, thread: Option<WorkThreadHandle>, _req: Request<IncomingBody>) -> Result<WorkResult, CommandError> {

        let (pattern, template) = pattern_template_from_sexpr_pair(&ctx.0.space, cmd.args[0].as_str(), cmd.args[1].as_str())
            .map_err(|e| CommandError::external(StatusCode::BAD_REQUEST, format!("{e:?}")))?;

        let pat_reader = ctx.0.space.new_reader_async(&derive_prefix_from_expr_slice(pattern.as_bytes()).till_constant_to_till_last_constant(), &()).await?;

        let format = cmd.properties[0].as_ref().map(|fmt_arg| fmt_arg.as_str()).unwrap_or("metta");
        let format = DataFormat::from_str(format).ok_or_else(|| CommandError::external(StatusCode::BAD_REQUEST, format!("Unrecognized format: {format}")))?;

        //Unpack the "uri" argument into a file path, if one was provided
        let file_path = match cmd.properties[1].as_ref() {
            Some(file_uri) => {
                #[cfg(feature="local_files")]
                {
                    let url = Url::parse(file_uri.as_str())?;

                    if url.scheme() != "file" {
                        return Err(CommandError::external(StatusCode::BAD_REQUEST, format!("Export command only supports `file` URLs in `uri` property")))
                    }
                    match url.to_file_path() {
                        Ok(file_path) => Some(file_path),
                        Err(e) => {
                            return Err(CommandError::external(StatusCode::BAD_REQUEST, format!("Failed to parse URL as a file path: {e:?}")))
                        }
                    }
                }
                #[cfg(not(feature="local_files"))]
                {
                    println!("Illegal attempt to export to local file using url: {file_uri:?}"); //GOAT, log this!!
                    return Err(CommandError::external(StatusCode::BAD_REQUEST, format!("File URLs aren't supported because the MORK server was compiled without `local_files` support")))
                }
            },
            None => None
        };

        let max_write = cmd.properties[2].as_ref().map(|x| x.as_u64() as usize).unwrap_or(usize::MAX);
        
        let out = tokio::task::spawn_blocking(move || -> Result<WorkResult, CommandError> {
            do_export(&ctx, (pat_reader, pattern), template, format, file_path, max_write)
        }).await??;

        thread.unwrap().finalize().await;
        println!("Export command successful"); // TODO log this!

        Ok(out)
    }
}

/// Do the actual serialization
fn do_export(ctx: &MorkService, (reader, pattern): (ReadPermission, OwnedExpr), template: OwnedExpr, format: DataFormat, file_path: Option<PathBuf>, max_write: usize) -> Result<WorkResult, CommandError> {
    let buffer = match &file_path {
        Some(file_path) => {
            // The rendered output will go to a file
            let file = std::fs::File::create(&file_path)?;
            let mut writer = std::io::BufWriter::new(file);
            dump_as_format(ctx, &mut writer, (reader, pattern), template, format, max_write)?;
            writer.flush()?;
            drop(writer);
            format!("Output written to file: {file_path:?}").into_bytes()
        },
        None => {
            // The rendered output will be returned directly
            let mut buffer = Vec::with_capacity(4096);
            let mut writer = std::io::BufWriter::new(&mut buffer);
            dump_as_format(ctx, &mut writer, (reader, pattern), template, format, max_write)?;
            writer.flush()?;
            drop(writer);
            buffer
        }
    };

    Ok(WorkResult::Immediate(hyper::body::Bytes::from(buffer)))
}

fn dump_as_format<W: Write>(ctx: &MorkService, writer: &mut std::io::BufWriter<W>, (mut reader, pattern): (ReadPermission, OwnedExpr), template: OwnedExpr, format: DataFormat, max_write: usize) -> Result<(), CommandError> {
    match format {
        DataFormat::Metta => {
            ctx.0.space.dump_as_sexpr(writer, (&mut reader, pattern.borrow()), template.borrow(), max_write).map_err(|e| CommandError::internal(format!("failed to serialize to MeTTa S-Expressions: {e:?}")))?;
        },
        DataFormat::Csv |
        DataFormat::Json => {
            writer.write(b"Export Error: Unimplemented Export Format")?;
        },
        DataFormat::Raw => {
            let mut rz = ctx.0.space.read_zipper(&mut reader);
            while rz.to_next_val() {
                writeln!(writer, "{:?}", rz.path()).map_err(|e| CommandError::internal(format!("Error occurred writing raw paths: {e:?}")))?;
            }
        }
        // #[cfg(not(feature="interning"))]
        DataFormat::Paths => {
            // println!("serializing...");
            thread_local!{
                static BUF: std::cell::UnsafeCell<[u8; 4096]> = std::cell::UnsafeCell::new([0; 4096]);
            }
            BUF.with(|b| {
                let mut rz = ctx.0.space.read_zipper(&mut reader);
                let wn = rz.witness();

                pathmap::path_serialization::for_each_path_serialize(writer, ||  {
                    while let Some(()) = rz.to_next_get_val_with_witness(&wn) {
                        let p = rz.origin_path();
                        let mut oz = ExprZipper::new(Expr{ ptr: unsafe { (*b.get()).as_mut_ptr() } });
                        // println!("dump transforming {:?} with {:?} => {:?}", Expr{ ptr: p.as_ptr() as *mut u8 }, pattern.borrow(), template.borrow());
                        match (Expr{ ptr: p.as_ptr() as *mut u8 }.transformData(pattern.borrow(), template.borrow(), &mut oz)) {
                            Ok(()) => unsafe {
                                // println!("success {:?}", Expr{ ptr: (*b.get()).as_mut_ptr() });
                                return Ok(Some(slice_from_raw_parts((*b.get()).as_ptr(), oz.loc).as_ref().unwrap()))
                            }
                            Err(_e) => {
                                // println!("failure");
                                continue
                            }
                        }
                    }
                    Ok(None)
                }
            )
            }).map_err(|e| CommandError::internal(format!("Error occurred writing raw paths: {e:?}")))?;
        }
    };
    Ok(())
}

// ===***===***===***===***===***===***===***===***===***===***===***===***===***===***===***
// import
// ===***===***===***===***===***===***===***===***===***===***===***===***===***===***===***

/// Fetch a remotely-hosted file, parse it, and load it into the map
pub struct ImportCmd;

impl CommandDefinition for ImportCmd {
    const NAME: &'static str = "import";
    const CONST_CMD: &'static Self = &Self;
    const CONSUME_WORKER: bool = true;
    fn args() -> &'static [ArgDef] {
        &[ArgDef{
            arg_type: ArgType::String,
            name: "pattern",
            desc: "The pattern to specify the expression to import from the data",
            required: true
        },
        ArgDef{
            arg_type: ArgType::String,
            name: "template",
            desc: "The template to specify the form of the expressions in the space",
            required: true
        }]
    }
    fn properties() -> &'static [PropDef] {
        &[PropDef{
            arg_type: ArgType::String,
            name: "uri",
            desc: "The URI from which to fetch the file, only http and https schemes are currently supported",
            required: true
        }]
    }
    async fn work(ctx: MorkService, cmd: Command, thread: Option<WorkThreadHandle>, _req: Request<IncomingBody>) -> Result<WorkResult, CommandError> {
        //Make sure we can get a place to download the file to, and we don't have an existing download in-progress
        let file_uri = cmd.properties[0].as_ref().unwrap().as_str();
        let file_handle = ctx.0.resource_store.new_resource(file_uri, cmd.cmd_id).await?;

        let (pattern, template) = pattern_template_from_sexpr_pair(&ctx.0.space, cmd.args[0].as_str(), cmd.args[1].as_str())
            .map_err(|e| CommandError::external(StatusCode::BAD_REQUEST, format!("{e:?}")))?;

        let writer = ctx.0.space.new_writer_async(derive_prefix_from_expr_slice(template.as_bytes()).till_constant_to_full(), &()).await?;

        tokio::task::spawn(async move {
            match do_import(&ctx, thread.unwrap(), &cmd, pattern, template, writer, file_handle).await {
                Ok(()) => {},
                Err(err) => {
                    println!("Internal Error occurred during import: {err:?}"); //GOAT Log this error
                }
            }
            async { () }
        });
        Ok("ACK. Starting Import".into())
    }
}

async fn do_import(ctx: &MorkService, thread: WorkThreadHandle, cmd: &Command, pattern: OwnedExpr, template: OwnedExpr, mut writer: WritePermission, mut file_resource: ResourceHandle) -> Result<(), CommandError> {
    let file_uri = cmd.properties[0].as_ref().unwrap().as_str();
    let url = Url::parse(file_uri)?;

    let space_prefix = derive_prefix_from_expr_slice(template.as_bytes()).till_constant_to_till_last_constant().to_owned();

    let file_path = if url.scheme() == "file" {

        // If a `file://` url was provided, then see if we can resolve it to a path and that the path exists
        //========================
        #[cfg(feature="local_files")]
        {
            let file_path = match url.to_file_path() {
                Ok(file_path) => file_path,
                Err(e) => {
                    let fetch_err = FetchError::new(StatusCode::BAD_REQUEST, format!("Failed to parse URL as a file path: {e:?}"));
                    return ctx.0.space.set_user_status(space_prefix, StatusRecord::FetchError(fetch_err))
                }
            };
            if !file_path.is_file() {
                let fetch_err = FetchError::new(StatusCode::BAD_REQUEST, format!("Failed to open file at path: {file_path:?}"));
                return ctx.0.space.set_user_status(space_prefix, StatusRecord::FetchError(fetch_err))
            }
            file_path
        }
        #[cfg(not(feature="local_files"))]
        {
            println!("Illegal attempt to import local file using url: {file_uri}"); //GOAT, log this!!
            let fetch_err = FetchError::new(StatusCode::BAD_REQUEST, format!("File URLs aren't supported because the MORK server was compiled without `local_files` support"));
            return ctx.0.space.set_user_status(space_prefix, StatusRecord::FetchError(fetch_err))
        }
    } else {

        // Otherwise fetch the url from a remote server
        //========================
        let mut response = match ctx.0.http_client.get(&*file_uri).send().await {
            Ok(response) => {
                if !response.status().is_success() {
                    //User-facing error
                    println!("Import Failed. unable to fetch remote resource: {}", response.status()); //GOAT, log this failure to fetch remote resource
                    let fetch_err = FetchError::new(response.status(), format!("Failed to load remote resource: {}", response.status()));
                    return ctx.0.space.set_user_status(space_prefix, StatusRecord::FetchError(fetch_err))
                }
                response
            },
            Err(e) => {
                let fetch_err = FetchError::new(StatusCode::INTERNAL_SERVER_ERROR, format!("Error occurred fetching remote resource: {e:?}"));
                return ctx.0.space.set_user_status(space_prefix, StatusRecord::FetchError(fetch_err))
            }
        };

        let mut file_writer = BufWriter::new(File::create(file_resource.path()?).await?);

        //GOAT!!!  We need to communicate back to the user if the download craps out in the middle
        while let Some(chunk) = response.chunk().await? {
            file_writer.write(&*chunk).await?;
        }
        file_writer.flush().await?;

        println!("Successful download from '{}', file saved to '{:?}'", file_uri, file_resource.path()?); //GOAT Log this sucessful completion
        file_resource.path()?.to_owned()
    };

    // Do the Parsing
    //========================
    let file_type = match detect_file_type(&file_path, file_uri) {
        Ok(file_type) => file_type,
        Err(err) => {
            //User-facing error
            println!("Import Failed. Unrecognized file type: {err:?}"); //GOAT, log this failure
            let parse_err = ParseError::new(format!("Failed to recognize file format: {err:?}"));
            return ctx.0.space.set_user_status(space_prefix, StatusRecord::ParseError(parse_err))
        }
    };

    let ctx_clone = ctx.clone();
    match tokio::task::spawn_blocking(move || {
        let file_handle = std::fs::File::open(&file_path)?;
        let file_stream = BufReader::new(file_handle);

        let pre_journal = format!("file({:?}) pattern({:?}) template({:?})", file_path, pattern.as_bytes(), template.as_bytes());

        do_parse(&ctx_clone.0.space, file_stream, pattern, template, &mut writer, file_type)?;

        '_journal_event : {
            test_journal_append(b"IMPORT", pre_journal.as_bytes());
            // JOURNAL.append_event(Import( (file, pattern, template)) ) // pattern : Sexpr, template : Sexpr
        
            // explictly drop `writer` only after Journal event complete
            drop(writer)
        }
        Result::<(),CommandError>::Ok(())
    
    }).await.map_err(CommandError::internal)? {
        Ok(()) => {},
        Err(err) => {
            //User-facing error
            println!("Import Failed. Parse error: {err:?}"); //GOAT, log this failure
            let parse_err = ParseError::new(format!("Failed to parse file: {err:?}"));
            return ctx.0.space.set_user_status(space_prefix, StatusRecord::ParseError(parse_err))
        }
    };

    //Finalize the resource
    let timestamp = 987654321; //GOAT, use the real timestamp from this command.
    file_resource.finalize(timestamp).await?;

    thread.finalize().await;
    println!("Import command successful"); //GOAT Log this!
    Ok(())
}

enum DataFormat {
    Metta, Json, Csv, Raw,
    #[cfg(not(feature="interning"))]
    Paths,
}

impl DataFormat {
    pub fn from_str(fmt_name: &str) -> Option<DataFormat> {
        let name_string = fmt_name.to_lowercase();
        // println!("gotten format {name_string}");
        match name_string.as_str() {
            "metta" => Some(DataFormat::Metta),
            "json" => Some(DataFormat::Json),
            "csv" => Some(DataFormat::Csv),
            "raw" => Some(DataFormat::Raw),
            // #[cfg(not(feature="interning"))]
            "paths" => Some(DataFormat::Paths),
            _ => { None }
        }
    }
}

/// Detects the type of file based on its name and/or contents
fn detect_file_type(_file_path: &Path, uri: &str) -> Result<DataFormat, CommandError> {
    let file_extension_err = || { CommandError::internal(format!("Unrecognized extension on file in url: {:?}", uri)) };

    let start_char = uri.len()-6.min(uri.len());
    let extension_start = uri[start_char..].rfind('.').ok_or_else(file_extension_err)? + start_char + 1;
    let extension = &uri[extension_start..];

    DataFormat::from_str(extension).ok_or_else(|| file_extension_err())
}

fn do_parse<SrcStream: Read + BufRead>(space: &ServerSpace, src: SrcStream, pattern: OwnedExpr, template: OwnedExpr, writer: &mut WritePermission, file_type: DataFormat) -> Result<(), CommandError> {
    let pattern_expr = pattern.borrow();
    let template_expr = template.borrow();
    match file_type {
        DataFormat::Metta => {
            let count = space.load_sexpr(src, pattern_expr, template_expr, writer).map_err(|e| CommandError::external(StatusCode::BAD_REQUEST, format!("{e:?}")))?;
            println!("Loaded {count} atoms from MeTTa S-Expr");
        },
        DataFormat::Json => {
            unimplemented!();//GOAT
            // let count = space.load_json_old(std::str::from_utf8(src_buf)?, dst).map_err(|e| CommandError::external(StatusCode::BAD_REQUEST, format!("{e:?}")))?;
            // println!("Loaded {count} atoms from JSON");
        },
        DataFormat::Csv => {
            let count = space.load_csv(src, pattern_expr, template_expr, writer, b',', true).map_err(|e| CommandError::external(StatusCode::BAD_REQUEST, format!("{e:?}")))?;
            println!("Loaded {count} atoms from CSV");
        },
        DataFormat::Raw => {
            return Err(CommandError::external(StatusCode::BAD_REQUEST, format!("Unimplemnted Import from raw format")))
        }
        // #[cfg(not(feature="interning"))] // use at own risk with interning
        DataFormat::Paths => {
            let bl = writer.path().len();
            let mut wz = space.write_zipper(writer);
            thread_local!{
                static BUF: std::cell::UnsafeCell<[u8; 4096]> = std::cell::UnsafeCell::new([0; 4096]);
            }
            let pathmap::path_serialization::DeserializationStats { path_count, .. } = BUF.with(|b| {
                // println!("for each deserialized...");
                pathmap::path_serialization::for_each_deserialized_path(src, |_k, p| {
                    let mut oz = ExprZipper::new(Expr{ ptr: unsafe { (*b.get()).as_mut_ptr() } });
                    // println!("transforming {:?} with {:?} => {:?}", Expr{ ptr: p.as_ptr() as *mut u8 }, pattern.borrow(), template.borrow());
                    match (Expr{ ptr: p.as_ptr() as *mut u8 }.transformData(pattern.borrow(), template.borrow(), &mut oz)) {
                        Ok(()) => unsafe {
                            wz.move_to_path(slice_from_raw_parts((*b.get()).as_ptr().offset(bl as _), oz.loc).as_ref().unwrap());
                            wz.set_val(());
                        }
                        Err(_e) => {}
                    }
                    std::io::Result::Ok(())
                })
            }).map_err(|e| CommandError::external(StatusCode::BAD_REQUEST, format!("{e:?}")))?;
            println!("Loaded {path_count} paths from `.paths` file");
        }
    }
    Ok(())
}

#[cfg(feature="neo4j")]
mod neo4j_commands {
    use crate::commands::*;

    /// makes initializing arrays easier
    const ZEROED : ArgDef = ArgDef{ arg_type: ArgType::String, name: "", desc: "", required: false}; 
    #[allow(unused)]
    #[repr(usize)]
    enum LoadNeo4jArg {
        OutputPath,
        Neo4jUri,
        Neo4jUser,
        // TODO! can we make this more secure?
        Neo4jPassword,
        /// this needs to remain the last variant
        _Len,
    }

    macro_rules! load_neo4j {
        (struct $COMMAND:ident; const NAME = $NAME:literal; fn $METHOD:ident) => {
            pub struct $COMMAND;
            impl CommandDefinition for $COMMAND {
                const NAME: &'static str = $NAME;
                const CONST_CMD: &'static Self = &Self;
                const CONSUME_WORKER: bool = true;
                fn args() -> &'static [ArgDef] {
                    & const {
                        use LoadNeo4jArg as Arg;
                        let mut args = [ZEROED; Arg::_Len as usize];

                        args[Arg::OutputPath as usize] = 
                            ArgDef{
                                arg_type : ArgType::Path,
                                name     : "output_path",
                                desc     : "the path where the loaded data will be stored",
                                required : true
                            };

                        args[Arg::Neo4jUri as usize] = 
                            ArgDef{
                                arg_type : ArgType::String,
                                name     : "neo4j_uri",
                                desc     : "the uri to the Neo4j instance",
                                required : true
                            };

                        args[Arg::Neo4jUser as usize] = 
                            ArgDef{
                                arg_type : ArgType::String,
                                name     : "neo4j_user",
                                desc     : "the username for accessing the Neo4j instance",
                                required : true
                            };

                        args[Arg::Neo4jUser as usize] = 
                            ArgDef{
                                arg_type : ArgType::String,
                                name     : "neo4j_password",
                                desc     : "the password for accessing the Neo4j instance",
                                required : true
                            };

                        args
                    }
                }
                fn properties() -> &'static [PropDef] {
                    &[]
                }
                async fn work(ctx: MorkService, cmd: Command, thread: Option<WorkThreadHandle>, _req: Request<IncomingBody>) -> Result<WorkResult, CommandError> {
                    let mut output = ctx.0.space.new_writer_async(cmd.args[LoadNeo4jArg::OutputPath as usize].as_path(), &()).await?;

                    let thread = thread.unwrap();
                    thread.dispatch_blocking_task(cmd, move |cmd| {
                        ctx.0.space.$METHOD(
                            &mut output,
                            &tokio::runtime::Handle::current(),
                            cmd.args[LoadNeo4jArg::Neo4jUri as usize].as_str(),
                            cmd.args[LoadNeo4jArg::Neo4jUser as usize].as_str(),
                            cmd.args[LoadNeo4jArg::Neo4jPassword as usize].as_str(),
                        ).map(|_|{}).map_err(|e| {
                            let e_ : Box<dyn std::error::Error + Send + Sync + 'static> = Box::new( std::io::Error::other(format!("{e:?}")));
                            e_
                        })
                    }).await;

                    Ok(WorkResult::Immediate(Bytes::from("Load Neo4j Triples query sent")))
                }
            }
        };
    }

    // ===***===***===***===***===***===***===***===***===***===***===***===***===***===***===***
    // load_neo4j_triples
    // ===***===***===***===***===***===***===***===***===***===***===***===***===***===***===***
    load_neo4j!{struct LoadNeo4jTriplesCmd; const NAME = "load_neo4j_triples"; fn load_neo4j_triples}

    // ===***===***===***===***===***===***===***===***===***===***===***===***===***===***===***
    // load_neo4j_node_properties
    // ===***===***===***===***===***===***===***===***===***===***===***===***===***===***===***
    load_neo4j!{struct LoadNeo4jNodePropertiesCmd; const NAME = "load_neo4j_node_properties"; fn load_neo4j_node_properties}

    // ===***===***===***===***===***===***===***===***===***===***===***===***===***===***===***
    // load_neo4j_node_labels
    // ===***===***===***===***===***===***===***===***===***===***===***===***===***===***===***
    load_neo4j!{struct LoadNeo4jNodeLabelsCmd; const NAME = "load_neo4j_node_labels"; fn load_neo4j_node_labels}

}
#[cfg(feature="neo4j")]
#[allow(unused)]
pub use neo4j_commands::*;

// ===***===***===***===***===***===***===***===***===***===***===***===***===***===***===***
// metta_thread
// ===***===***===***===***===***===***===***===***===***===***===***===***===***===***===***

/// Runs a MeTTa thread at a location
pub struct MettaThreadCmd;

impl CommandDefinition for MettaThreadCmd {
    const NAME: &'static str = "metta_thread";
    const CONST_CMD: &'static Self = &Self;
    const CONSUME_WORKER: bool = true;
    fn args() -> &'static [ArgDef] { &[] }
    fn properties() -> &'static [PropDef] {
        &[
            PropDef {
                arg_type: ArgType::String,
                //GOAT: I don't think it makes any sense to call this a "location" at this point.  It's really a unique thread_id.
                // And once we make it auto-generated, I don't think it makes any sense for it to be a parameter at all
                //
                //GOAT: we probably want to use `ctx.0.workers.job_counter()` instead of `ctx.0.request_counter`, because request_counter
                // increments for every request including status requests, while `job_counter` only increments for actual work operations.
                name: "location",
                desc: "If this parameter is present the thread id will not be generated by the runtime, but will instead try to run with the one supplied.\
                      \nThe location of the execution of a metta thread. The location must be a ground (no variable bindings or references).\
                      \nThe thread will run and consume expressions of the form (exec (<loc> <priority>) (, <..patterns>) (, <..templates>)) until there are none left.\
                      \nIt is an error to spawn a thread at the same location or to execute an exec expression where the patterns and templates are not in (, <..args>) form",
                required: false
            }
        ]
    }
    async fn work(ctx: MorkService, cmd: Command, _thread: Option<WorkThreadHandle>, _req: Request<IncomingBody>) -> Result<WorkResult, CommandError> {
        let thread = _thread.unwrap();

        let bad_request = |s : &str| Err(CommandError::external(StatusCode::BAD_REQUEST, s));

        // //////////////////////////////////////////////////////////////////////////////////////
        // Get a unique identifier or grounded sub-expression for this MeTTa thread
        // //////////////////////////////////////////////////////////////////////////////////////

        let thread_id_sexpr_string = match &cmd.properties[0] {
            Some(prop) => prop.as_str().to_owned(),
            None       => {
                return Err(CommandError::external(StatusCode::NOT_IMPLEMENTED,
                    "Thread ID substitution is work in progress,\
                    \nuntil it is fully implemented use a hardcoded constant , for example \"task_name\", for the <location> as a convention,\
                    \nand use the command property `location` with that constant specified (`.../?location=task_name`)."
                ));
                #[allow(unreachable_code /* hopefully we will have this in the near future removed*/)]
                cmd.cmd_id.to_string()
            },
        };
        let Ok(expr) = ctx.0.space.sexpr_to_expr(&thread_id_sexpr_string) else { return bad_request("malformed location sexpr") };

        let location = expr.borrow();
        if !location.is_ground() { return Err(CommandError::external(StatusCode::BAD_REQUEST, "Location was not a ground expression."));};

        // //////////////
        // BUILD TASK //
        // ////////////

        let spec = ctx.0.space.metta_calculus_machine_spec(&thread_id_sexpr_string, &(), 500)?;

        thread.dispatch_blocking_task(cmd, move |_| {

            use mork::space::metta_calculus::{LookupCases, };
            let mut machine          = None;
            let mut start_controller = spec.init(&ctx.0.space, &(), &mut machine);

            'process_execs : loop {
                let pre_transform = match start_controller.exec_lookup_explicit() {
                    LookupCases::Done                      => { return Ok(())},
                    LookupCases::Success(lookup_sucess)    => lookup_sucess,
                    LookupCases::NonReactiveExec(loop_start) |
                    LookupCases::ExecsRemaining(loop_start) => {
                                                                start_controller = loop_start;
                                                                continue 'process_execs;
                                                              },
                };

                // close the loop
                start_controller = pre_transform.transform_or_defer(|machine|{
                    
                    /* journal transform in critical section */
                    #[cfg(debug_assertions)]'_journal:{

                        let current_exec = machine.current_exec().unwrap();
                        let s = format!("current_exec({:?})", current_exec);

                        test_journal_append(b"METTA_THREAD", s.as_bytes());
                    }

                    
                
                });
            };
        }).await;

        // TODO! location needs to be pulled out with space!  GOAT: Please explain what you mean by this.
        Ok(
            WorkResult::Immediate(
                Bytes::from(format!("Thread `{thread_id_sexpr_string}` was dispatched.")))
        )
    }
}


// ===***===***===***===***===***===***===***===***===***===***===***===***===***===***===***
// status
// ===***===***===***===***===***===***===***===***===***===***===***===***===***===***===***

/// Returns the status associated with a path in the trie
pub struct StatusCmd;

impl CommandDefinition for StatusCmd {
    const NAME: &'static str = "status";
    const CONST_CMD: &'static Self = &Self;
    const CONSUME_WORKER: bool = false;
    fn args() -> &'static [ArgDef] {
        &[ArgDef{
            arg_type: ArgType::Expr,
            name: "expr",
            desc: "The expression on which to return the status.  The path is relative to the first variable in the expression, e.g. `(test (data $v) _)`",
            required: true
        }]
    }
    fn properties() -> &'static [PropDef] {
        &[]
    }
    async fn work(ctx: MorkService, cmd: Command, _thread: Option<WorkThreadHandle>, _req: Request<IncomingBody>) -> Result<WorkResult, CommandError> {
        let expr = cmd.args[0].as_expr_bytes();
        let prefix = derive_prefix_from_expr_slice(&expr).till_constant_to_till_last_constant();

        let status = ctx.0.space.get_status(&prefix);
        let json_string = serde_json::to_string(&status)?;
        Ok(json_string.into())
    }
}

// ===***===***===***===***===***===***===***===***===***===***===***===***===***===***===***
// status_stream
// ===***===***===***===***===***===***===***===***===***===***===***===***===***===***===***

/// Opens a Server-Side-Events stream, to monitor an expression / path for status updates
pub struct StatusStreamCmd;

impl CommandDefinition for StatusStreamCmd {
    const NAME: &'static str = "status_stream";
    const CONST_CMD: &'static Self = &Self;
    const CONSUME_WORKER: bool = false;

    fn args() -> &'static [ArgDef] {
        &[ArgDef{
            arg_type: ArgType::Expr,
            name: "expr",
            desc: "The expression on which to return the status.  The path is relative to the first variable in the expression, e.g. `(test (data $v) _)`",
            required: true
        }]
    }
    fn properties() -> &'static [PropDef] {
        &[]
    }
    async fn work(
        ctx: MorkService,
        cmd: Command,
        _thread: Option<WorkThreadHandle>, _req: Request<IncomingBody>
    ) -> Result<WorkResult, CommandError> {

        let expr = cmd.args[0].as_expr_bytes();
        let prefix = derive_prefix_from_expr_slice(expr).till_constant_to_till_last_constant();

        //Make a channel to send status updates to the client
        let (tx, rx) = mpsc::channel::<StatusRecord>(100);

        //Send the current status right away.  It'll be buffered because we haven't composed the reply yet
        let status = ctx.0.space.get_status(&prefix);
        let _ = tx.send(status).await;

        //Put the sender in the StatusMap, so we can send updates to the stream
        ctx.0.space.status_map.add_stream(prefix, cmd.cmd_id, tx);

        //Finally, Make a StatusStream from the channel, so we can return it to the client, and clean up the
        // StatusMap if the client closes the stream
        let stream = ReceiverStream::new(rx).map(|quote| {
            let data = serde_json::to_string(&quote).unwrap();
            let event = format!("data: {}\n\n", data);
            Ok(Frame::data(Bytes::from(event)))
        });
        let stream = StatusStream::new(ctx.0.space.status_map.clone(), prefix.to_vec(), cmd.cmd_id, stream);

        Ok(WorkResult::Streamed(Box::pin(stream)))
    }
}

/// Wraps a stream, so the stream will be removed from the server's status_streams map when the client closes the connection
pub(crate) struct StatusStream<S> {
    inner: S,
    stream_id: u64,
    status_map: StatusMap,
    path: Vec<u8>,
}

impl<S> Drop for StatusStream<S> {
    fn drop(&mut self) {
        //When this is called, it tells us that the client has closed the channel, so remove the sender from the map
        self.status_map.remove_stream(&self.path, self.stream_id);
    }
}

impl<S> StatusStream<S> {
    pub(crate) fn new(status_map: StatusMap, path: Vec<u8>, stream_id: u64, inner: S) -> Self {
        StatusStream { path, status_map, stream_id, inner }
    }
}

impl<S: Stream + Unpin> Stream for StatusStream<S> where S::Item : core::fmt::Debug {
    type Item = S::Item;

    fn poll_next(mut self: Pin<&mut Self>, cx: &mut std::task::Context<'_>) -> std::task::Poll<Option<Self::Item>> {
        Pin::new(&mut self.inner).poll_next(cx)
    }
}

// ===***===***===***===***===***===***===***===***===***===***===***===***===***===***===***
// stop
// ===***===***===***===***===***===***===***===***===***===***===***===***===***===***===***

/// Initiate server shutdown, immedaitely stop accepting new connections
pub struct StopCmd;

impl CommandDefinition for StopCmd {
    const NAME: &'static str = "stop";
    const CONST_CMD: &'static Self = &Self;
    const CONSUME_WORKER: bool = false;
    fn args() -> &'static [ArgDef] {
        &[]
    }
    fn properties() -> &'static [PropDef] {
        &[
            PropDef {
                arg_type: ArgType::Flag,
                name: "wait_for_idle",
                desc: "A flag instructing the server to wait for an idle state before initiating shutdown",
                required: false
            }
        ]
    }
    async fn work(ctx: MorkService, cmd: Command, _thread: Option<WorkThreadHandle>, _req: Request<IncomingBody>) -> Result<WorkResult, CommandError> {
        const IDLE_TIME_MS: u128 = 1000; //The server must be idle for 1s before shutdown will begin from a `wait_for_idle` request
        let wait_for_idle = cmd.properties[0].is_some();

        if wait_for_idle {
            tokio::task::spawn(async move {
                //This loop runs until the server has gone `IDLE_TIME_MS` without taking any new work
                let mut last_busy_time = std::time::Instant::now();
                let mut last_request_count = ctx.0.request_counter.load(std::sync::atomic::Ordering::Relaxed);
                loop {
                    ctx.0.workers.wait_for_worker_completion().await;
                    let cur_request_count = ctx.0.request_counter.load(std::sync::atomic::Ordering::Relaxed);
                    if last_request_count != cur_request_count {
                        last_busy_time = std::time::Instant::now();
                        last_request_count = cur_request_count;
                    }
                    if std::time::Instant::now().duration_since(last_busy_time).as_millis() > IDLE_TIME_MS {
                        break
                    }
                    tokio::time::sleep(std::time::Duration::from_millis(5)).await;
                }
                ctx.0.stop_cmd.notify_waiters();
            });
            println!("Processed `stop?wait_for_idle` request"); //GOAT log this
            Ok("ACK. Shutdown will occur when server activity stops".into())
        } else {
            ctx.0.stop_cmd.notify_waiters();
            println!("Processed `stop` request"); //GOAT log this
            Ok("ACK. Initiating Shutdown.  Connections will not longer be accepted".into())
        }
    }
}

// ===***===***===***===***===***===***===***===***===***===***===***===***===***===***===***
// transform
// ===***===***===***===***===***===***===***===***===***===***===***===***===***===***===***

/// expects the post body to be of this form of sexpr
/// ```ignore
/// (transform
///   (, (pattern0 ...)
///      (pattern1 ...)
///      ...
///   )
///   (, (template0 ...)
///      (template1 ...)
///      ...
///   )
/// )
/// ```

pub struct TransformCmd;

impl CommandDefinition for TransformCmd {
    const NAME: &'static str = "transform";
    const CONST_CMD: &'static Self = &Self;
    const CONSUME_WORKER: bool = true;
    fn args() -> &'static [ArgDef] {
        &[]
    }
    fn properties() -> &'static [PropDef] {
        &[]
    }
    async fn work(ctx: MorkService, cmd: Command, thread: Option<WorkThreadHandle>, mut _req: Request<IncomingBody>) -> Result<WorkResult, CommandError> {
        let work_thread = thread.unwrap();

        let post_bytes = get_all_post_frame_bytes(&mut _req).await?;
        let src = core::str::from_utf8(&post_bytes).map_err(|e| CommandError::external(StatusCode::BAD_REQUEST, format!("{e:?}")))?;

        let (patterns, templates) = pattern_template_args(&ctx.0.space, src)
            .map_err(|e| CommandError::external(StatusCode::BAD_REQUEST, format!("{e:?}")))?;

        let (read_map, template_prefixes, mut writers) = ctx.0.space.acquire_transform_permissions(&patterns, &templates, &(), ||{})?;

        '_journal_event : {
            test_journal_append(b"TRANSFORM", format!("{:?}", post_bytes).as_bytes());
            // JOURNAL.append_event(Transform(Post_bytes))

            // explictly drop wz only after Journal event complete
        }

        work_thread.dispatch_blocking_task(cmd, move |_c| {

            ctx.0.space.transform_multi_multi(&patterns, &read_map, &templates, &template_prefixes, &mut writers);
            Ok(())
        }).await;

        Ok(WorkResult::Immediate(Bytes::from("ACK. TranformMultiMulti dispatched")))
    }
}

#[cfg(test)]
#[test]
fn transform_multi_multi_basic_arg_check() {
    let space = ServerSpace::new();

    let input ="\
               \n(transform\
               \n  (, (pattern0 a)\
               \n     (pattern1 b)\
               \n     (pattern1 b d e $f)\
               \n  )\
               \n  (, (template0 c)\
               \n     (template1 d)\
               \n  )\
               \n)\
               \n\
    ";

    let (out_paterns, out_templates) = pattern_template_args(&space, input).unwrap();

    println!("PATERNS   : {out_paterns:?}\
            \nTEMPLATES : {out_templates:?}")
}


#[derive(Debug)]
enum TransformMultiMultiError {
    ExpectedTransformSym,
    ExpectedPatternList,
    ExpectedTemplateList,
    ExpectedArity3AsFirstByte,
    ParseError
}

/// Parse a (pattern, template) pair as paths
fn pattern_template_from_sexpr_pair(space : &ServerSpace, pattern: &str, template: &str) -> Result<(OwnedExpr, OwnedExpr), TransformMultiMultiError> {
    let formatted = format!(
        "(transform (, {}) (, {}) )",
        pattern, 
        template,
    );
    let (mut patterns, mut templates) = pattern_template_args(&space, &formatted)?;
    // Ok((patterns.pop().unwrap(), templates.pop().unwrap()))
    Ok((patterns.pop().unwrap_or(OwnedExpr::empty()), templates.pop().unwrap_or(OwnedExpr::empty())))
}

/// Parses the args in the POST body of a transform command request into a Vec of patterns and a Vec of templates
fn pattern_template_args(space: &ServerSpace, input: &str)->Result<(Vec<OwnedExpr>, Vec<OwnedExpr>), TransformMultiMultiError> {
    use mork_bytestring::Tag;

    let expr = space.sexpr_to_expr(input).map_err(|_| TransformMultiMultiError::ParseError)?;
    let mut expr_z = mork_bytestring::ExprZipper::new(expr.borrow());

    let Ok(Tag::Arity(3)) = expr_z.item() else { return  Err(TransformMultiMultiError::ExpectedArity3AsFirstByte);};

    expr_z.next_child();
    if unsafe {expr_z.subexpr().span().as_ref() != mork::expr!(space, "transform").span().as_ref()} {
        return Err(TransformMultiMultiError::ExpectedTransformSym)
    }

    expr_z.next_child();
    let paterns = expr_z.subexpr();
    let Ok(out_paterns) = comma_list_expr(&space, paterns) else { return Err(TransformMultiMultiError::ExpectedPatternList); };

    expr_z.next_child();
    let templates = expr_z.subexpr();
    let Ok(out_templates) = comma_list_expr(&space, templates) else { return Err(TransformMultiMultiError::ExpectedTemplateList); };

    Ok((out_paterns, out_templates))
}

fn comma_list_expr(space : &ServerSpace, expr : mork_bytestring::Expr) -> Result<Vec<OwnedExpr>, &'static str> {

    let mut out = Vec::new();
    let mut z = mork_bytestring::ExprZipper::new(expr);
    match z.item() {
        Ok(mork_bytestring::Tag::Arity(arity)) => {
            if !z.next_child() { return Err("Malformed expr") };

            if unsafe {z.subexpr().span().as_ref() != mork::expr!(space, ",").span().as_ref()} {
                return Err("expected `,` symbol");
            }
            for _ in 0..arity-1 {
                z.next_child();
                let sub = z.subexpr();
                out.push(OwnedExpr::from(unsafe { &*sub.span() }))
            }
            Ok(out)
        }
        _ => Err(dbg!("expected arity byte"))
    }
}

// ===***===***===***===***===***===***===***===***===***===***===***===***===***===***===***
// upload
// ===***===***===***===***===***===***===***===***===***===***===***===***===***===***===***

/// Upload data directly to the map via a post request
pub struct UploadCmd;

impl CommandDefinition for UploadCmd {
    const NAME: &'static str = "upload";
    const CONST_CMD: &'static Self = &Self;
    const CONSUME_WORKER: bool = true;
    fn args() -> &'static [ArgDef] {
        &[ArgDef{
            arg_type: ArgType::String,
            name: "pattern",
            desc: "The pattern to specify the expression to import from the data",
            required: true
        },
        ArgDef{
            arg_type: ArgType::String,
            name: "template",
            desc: "The template to specify the form of the expressions in the space",
            required: true
        }]
    }
    fn properties() -> &'static [PropDef] {
        &[
            PropDef {
                arg_type: ArgType::String,
                name: "format",
                desc: "The format to expect, default is metta S-Expressions",
                required: false
            }
        ]
    }
    async fn work(ctx: MorkService, cmd: Command, thread: Option<WorkThreadHandle>, mut req: Request<IncomingBody>) -> Result<WorkResult, CommandError> {
        let format = cmd.properties[0].as_ref().map(|fmt_arg| fmt_arg.as_str()).unwrap_or("metta");
        let format = DataFormat::from_str(format).ok_or_else(|| CommandError::external(StatusCode::BAD_REQUEST, format!("Unrecognized format: {format}")))?;

        let (pattern, template) = pattern_template_from_sexpr_pair(&ctx.0.space, cmd.args[0].as_str(), cmd.args[1].as_str())
            .map_err(|e| CommandError::external(StatusCode::BAD_REQUEST, format!("{e:?}")))?;

        let mut writer = ctx.0.space.new_writer(derive_prefix_from_expr_slice(template.as_bytes()).till_constant_to_full(), &())?;

        //Read all the data from the post request

        // Do the Parsing
        //========================
        let ctx_clone   = ctx.clone();
        let src_buf     = get_all_post_frame_bytes(&mut req).await?;
        let data_format = format;
        match tokio::task::spawn_blocking(move || {
            let (sexpr_pattern, sexpr_template) = (cmd.args[0].as_str(), cmd.args[1].as_str());
            
            do_parse(&ctx_clone.0.space, &src_buf[..], pattern, template, &mut writer, data_format)?;
            '_journal_event : {
                // this is only to reduce the degenerate behavior
                const DEGENERACY_LIMIT : usize = u128::BITS as usize; 
                if src_buf.len() > DEGENERACY_LIMIT {
                    // Hash
                    let hash =  gxhash::gxhash128(&src_buf[..], 0);


                }
                let test_journal_s = format!("pattern({:?}) template({:?}) src_buf({:?})", sexpr_pattern, sexpr_template, core::str::from_utf8(&src_buf[..]));
                test_journal_append(b"UPLOAD", test_journal_s.as_bytes());
                // JOURNAL.append_event(Upload(Pattern, template, src_buf))
                            
                // explictly drop writer only after Journal event complete
                drop(writer)
            }
            Result::<(),CommandError>::Ok(())
        }).await.map_err(CommandError::internal)? {
            Ok(()) => {},
            Err(err) => {
                //User-facing error
                println!("Upload Failed. Parse error: {err:?}"); //GOAT, log this failure
                return Err(CommandError::external(StatusCode::BAD_REQUEST, format!("Failed to parse uploaded data: {err:?}")))
            }
        };

        thread.unwrap().finalize().await;
        Ok("ACK. Upload Successful".into())
    }
}

/// Read all the data from the post request
async fn get_all_post_frame_bytes(req : &mut Request<IncomingBody>) -> Result<Bytes, CommandError> {
    let mut post_data_buf = BytesMut::with_capacity(4096);
    while let Some(chunk) = req.frame().await {
        match chunk {
            Ok(frame) => {
                if let Some(data) = frame.data_ref() {
                    post_data_buf.extend_from_slice(data);
                }
            }
            Err(err) => {
                return Err(CommandError::external(StatusCode::BAD_REQUEST, format!("Error reading POST data: {err}")))
            }
        }
    }
    Ok(post_data_buf.freeze())
}

// ===***===***===***===***===***===***===***===***===***===***===***===***===***===***===***
// Command mechanism implementation
// ===***===***===***===***===***===***===***===***===***===***===***===***===***===***===***

/// The definition of an argument to a command
pub struct ArgDef {
    pub arg_type: ArgType,
    pub name: &'static str,
    pub desc: &'static str,
    pub required: bool
}

/// The definition of a property associated with a command
pub type PropDef = ArgDef;

/// Defines the behavior of a command the server can execute
pub trait CommandDefinition where Self: 'static + Send + Sync {
    /// Name of the command
    const NAME: &'static str;

    /// Glue to get a constant reference to the Self singleton
    const CONST_CMD: &'static Self;

    /// Whether or not this command requires a free worker be available in order to proceed
    const CONSUME_WORKER: bool;

    /// Arguments, `(arg_type, arg_name, arg_description)`
    fn args() -> &'static [ArgDef];

    /// Additional named properties associated with the command, (key, )
    fn properties() -> &'static [PropDef];

    /// Method to perform the execution.  If anything CPU-intensive is done in this method,
    /// it should call `dispatch_blocking_task` for that work
    fn work(ctx: MorkService, cmd: Command, thread: Option<WorkThreadHandle>, req: Request<IncomingBody>) -> impl Future<Output=Result<WorkResult, CommandError>> + Sync + Send;
}

/// Object-safe wrapper over CommandDefinition
pub trait CmdDefObject: 'static + Send + Sync {
    fn name(&self) -> &'static str;
    fn consume_worker(&self) -> bool;
    // fn args(&self) -> &'static [ArgDef];
    // fn properties(&self) -> &'static [PropDef];
    fn work(&self, ctx: MorkService, cmd: Command, thread: Option<WorkThreadHandle>, req: Request<IncomingBody>) -> Pin<Box<dyn Future<Output=Result<WorkResult, CommandError>> + Sync + Send>>;
}

impl<CmdDef> CmdDefObject for CmdDef where CmdDef: 'static + Send + Sync + CommandDefinition {
    fn name(&self) -> &'static str {
        Self::NAME
    }
    fn consume_worker(&self) -> bool {
        Self::CONSUME_WORKER
    }
    // fn args(&self) -> &'static [ArgDef] {
    //     Self::args()
    // }
    // fn properties(&self) -> &'static [PropDef] {
    //     Self::properties()
    // }
    fn work(&self, ctx: MorkService, cmd: Command, thread: Option<WorkThreadHandle>, req: Request<IncomingBody>) -> Pin<Box<dyn Future<Output=Result<WorkResult, CommandError>> + Sync + Send>> {
        Box::pin(Self::work(ctx, cmd, thread, req))
    }
}

/// An invocation of a command, that can be (or has been) executed by the server
#[derive(Clone)]
pub struct Command {
    pub def: &'static dyn CmdDefObject,
    pub args: Vec<ArgVal>,
    pub properties: Vec<Option<ArgVal>>,
    pub cmd_id: u64,
}

/// An error type from a command that can be logged and returned to a client
#[derive(Debug)]
pub enum CommandError {
    /// An internal server error that is not the result of a client action
    Internal(BoxedErr),
    /// An error originating from an action done by the client
    External(ExternalError)
}

#[derive(Clone, Debug)]
pub struct ExternalError {
    pub(crate) user_message: Option<String>,
    pub(crate) log_message: String,
    pub(crate) status_code: StatusCode,
}

impl ExternalError {
    pub fn new<M: Into<String>>(status_code: StatusCode, log_message: M) -> Self {
        Self { status_code, log_message: log_message.into(), user_message: None, }
    }
}

impl CommandError {
    pub fn internal<Desc: Into<Box<dyn core::error::Error + Send + Sync>>>(desc: Desc) -> Self {
        Self::Internal(desc.into())
    }
    pub fn external<M: Into<String>>(status_code: StatusCode, log_message: M) -> Self {
        Self::External(ExternalError{ status_code, log_message: log_message.into(), user_message: None })
    }
    pub fn from_status_record<M: Into<String>>(status_record: StatusRecord, log_message: M) -> Self {
        match status_record {
            StatusRecord::PathClear => unreachable!(),
            StatusRecord::CountResult(_) => unreachable!(),
            StatusRecord::PathReadOnly => Self::external(StatusCode::FORBIDDEN, log_message),
            StatusRecord::PathReadOnlyTemporary => Self::external(StatusCode::CONFLICT, log_message),
            StatusRecord::PathForbidden => Self::external(StatusCode::FORBIDDEN, log_message),
            StatusRecord::PathForbiddenTemporary => Self::external(StatusCode::CONFLICT, log_message),
            StatusRecord::FetchError(err) => Self::external(err.status_code, err.log_message),
            StatusRecord::ParseError(err) => Self::external(StatusCode::UNSUPPORTED_MEDIA_TYPE, err.log_message),
            StatusRecord::ExecError(err) =>Self::external(StatusCode::BAD_REQUEST, err),
        }
    }
}

impl<E: core::error::Error + Send + Sync + 'static> From<E> for CommandError {
    fn from(err: E) -> Self {
        Self::Internal(Box::new(err))
    }
}

#[derive(Clone, Copy, Debug)]
pub enum ArgType {
    Expr, Flag, Int, UInt, Path, String
}

#[derive(Clone, Debug, Default)]
pub enum ArgVal {
    #[default]
    None,
    Flag,
    Int(i64),
    UInt(u64),
    Expr(OwnedExpr),
    Path(Vec<u8>),
    String(String),
}

impl ArgVal {
    pub fn as_u64(&self) -> u64 {
        match self {
            Self::UInt(v) => *v,
            _ => unreachable!()
        }
    }
    pub fn as_i64(&self) -> i64 {
        match self {
            Self::Int(v) => *v,
            _ => unreachable!()
        }
    }
    pub fn as_path(&self) -> &[u8] {
        match self {
            Self::Path(path) => &*path,
            _ => unreachable!()
        }
    }
    pub fn as_str(&self) -> &str {
        match self {
            Self::String(string) => &*string,
            _ => unreachable!()
        }
    }
    pub fn as_expr_bytes(&self) -> &[u8] {
        match self {
            Self::Expr(expr) => expr.as_bytes(),
            _ => unreachable!()
        }
    }
}


type ExprPrefixSlice<'a> = &'a [u8];
#[derive(Clone, Copy, Debug)]
enum DerivedPrefix<'a> {
    TillVar(ExprPrefixSlice<'a>),
    TillConst{ full : ExprPrefixSlice<'a>, till_last_constant : ExprPrefixSlice<'a>},
}
impl<'a> DerivedPrefix<'a> {
    /// the [`Self::TillConstant`] variant will be collapsed to the `full` field, and the [`Self::TillVar`] variant to it's inner value
    fn till_constant_to_full(self)-> ExprPrefixSlice<'a> {
        match self {
            DerivedPrefix::TillVar(items) => items,
            DerivedPrefix::TillConst { full, .. } => full,
        }
    }
    #[allow(unused)]
    /// the [`Self::TillConstant`] variant will be collapsed to the `till_last_constant` field, and the [`Self::TillVar`] variant to it's inner value
    fn till_constant_to_till_last_constant(self) -> ExprPrefixSlice<'a> {
        match self {
            DerivedPrefix::TillVar(items) => items,
            DerivedPrefix::TillConst { till_last_constant, .. } => till_last_constant,
        }
    }
}

// wrapper for [`mork_bytestring::Expr::prefix`] to make the interface more straight-forward
fn derive_prefix_from_expr_slice(expr_slice : &[u8]) -> DerivedPrefix<'_>{
    unsafe {
      match (mork_bytestring::Expr{
          ptr : expr_slice.as_ptr() as *mut _
      })
      .prefix()
      {
        Ok(pre) => DerivedPrefix::TillVar(&*pre),
        Err(till_last) => DerivedPrefix::TillConst {
            full               : expr_slice, 
            till_last_constant : &*till_last,
        },
      }
    }
}

#[cfg(test)]
#[test]
fn prefix_assertions() {
    let space = ServerSpace::new();

    macro_rules! prefix_to_var { ($EXPR:ident :expr ; $PREFIX:ident : prefix ; $SEXPR:literal) => {
        let se      = $SEXPR;
        let $EXPR   = space.sexpr_to_expr(se).unwrap();
        let $PREFIX = derive_prefix_from_expr_slice(& $EXPR.as_bytes());
    }; }

    prefix_to_var!(e1 : expr ; pe1 : prefix ; "a");
    core::assert_eq!{e1, pe1.till_constant_to_full()};

    prefix_to_var!(e2 : expr; pe2 : prefix; "$a");
    core::assert_ne!{e2, pe2.till_constant_to_full()};
    core::assert_eq!(pe2.till_constant_to_full(), pe1.till_constant_to_till_last_constant());

    // ----

    prefix_to_var!(e3 : expr; pe3 : prefix; "(a)");
    core::assert_eq!{e3, pe3.till_constant_to_full()};

    prefix_to_var!(e4 : expr; pe4 : prefix; "($a)");
    core::assert_ne!{e4, pe4.till_constant_to_full()};
    core::assert_eq!(pe4.till_constant_to_full(), pe3.till_constant_to_till_last_constant());

    // ----

    prefix_to_var!(e5 : expr; pe5 : prefix; "(a b)");
    core::assert_eq!{e5, pe5.till_constant_to_full()};

    prefix_to_var!(e6 : expr; pe6 : prefix; "(a $b)");
    core::assert_ne!{e6, pe6.till_constant_to_full()};
    core::assert_eq!{pe6.till_constant_to_full(), pe5.till_constant_to_till_last_constant()};

    // ----

    prefix_to_var!(e7 : expr; pe7 : prefix; "($a b)");
    core::assert_ne!{e7, pe7.till_constant_to_full()};
    core::assert_ne!{pe7.till_constant_to_full(), pe6.till_constant_to_full()};

    prefix_to_var!(e8 : expr; pe8 : prefix; "($a (b c))");
    core::assert_ne!{e8, pe8.till_constant_to_full()};
    core::assert_eq!{pe8.till_constant_to_full(), pe7.till_constant_to_full()};

    prefix_to_var!(e9 : expr; pe9 : prefix; "($a $b)");
    core::assert_ne!{e9, pe9.till_constant_to_full()};
    core::assert_eq!{pe9.till_constant_to_full(), pe7.till_constant_to_full()};

    // ----

    prefix_to_var!(e10 : expr; pe10 : prefix; "($a ($b c))");
    core::assert_ne!{e10, pe10.till_constant_to_full()};
    core::assert_eq!{pe10.till_constant_to_full(), pe7.till_constant_to_full()};

    prefix_to_var!(e11 : expr; pe11 : prefix; "($a ($b $c))");
    core::assert_ne!{e11, pe11.till_constant_to_full()};
    core::assert_eq!{pe11.till_constant_to_full(), pe7.till_constant_to_full()};
}



// const CACHE_ELEMENT_LIMIT : usize = 4096;
// type CacheOrder    = u64;
// type ChacheHash     = u64;
// type CacheVal       = (ChacheHash, Arc<[u8]>);
// type CacheStrBuffer = Vec<u8>;
// struct ArgsStrCache {
//     order      : CacheOrder,
//     next_evict : usize,
//     hashes     : [ChacheHash     ; CACHE_ELEMENT_LIMIT],
//     strs       : [CacheStrBuffer ; CACHE_ELEMENT_LIMIT],
//     index      : BTreeMap<ChacheHash, usize>
// }
// enum HashCollision { Yes, No, }
// impl ArgsStrCache {
//     const fn init_cache() -> Self {
//         let mut str_ = MaybeUninit::<[CacheStrBuffer; CACHE_ELEMENT_LIMIT]>::zeroed();
//         let mut i = CACHE_ELEMENT_LIMIT;
//         loop {
//             if i == 0 { break; }
//             i -=1;
//             unsafe {core::ptr::write(&mut (*str_.as_mut_ptr())[i], CacheStrBuffer::new())};
//         }
//         ArgsStrCache {
//             order      : 0,
//             next_evict : 0,
//             hashes     : [   0; CACHE_ELEMENT_LIMIT],
//             strs       : unsafe {str_.assume_init()},
//             index      : BTreeMap::new(),
//         }
//     }
//     fn check_in_cache(&mut self, s : &[u8]) -> (HashCollision, ChacheHash, CacheOrder) {
//         extern crate alloc;
//         let hash = gxhash64(s, 0);


//         match self.index.entry(hash) {
//             alloc::collections::btree_map::Entry::Vacant(v) => {
//                 let order       = self.order;
//                 let next_evict  = self.next_evict;
                
//                 self.hashes[next_evict] = hash;
//                 self.strs[next_evict].clear();

//                 self.order      += 1;
//                 self.next_evict = (self.order % CACHE_ELEMENT_LIMIT as u64) as usize ;
                
//             },
//             alloc::collections::btree_map::Entry::Occupied(o) => {

//             },
//         }



//     }
// }


fn test_journal_append(header : &[u8], s : &[u8]) {
    const TEST_JOURNAL : &str = "test_journal.txt";
    let mut f_opts = std::fs::File::options();
    f_opts.append(true);
    f_opts.create(true);

    static WAIT : std::sync::Mutex<()> = std::sync::Mutex::new(());

    let e = WAIT.lock().unwrap();
    
    let path = std::path::PathBuf::from(std::env::var("CARGO_WORKSPACE_DIR").unwrap()).join("server").join("test_journal").join(TEST_JOURNAL);
    // let path = std::dbg!(std::path::PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap()).join(TEST_JOURNAL));
    
    let mut file = f_opts.open(path).unwrap();
    file.write(header);
    file.write(b":");
    file.write(s);
    file.write(b"\n");

    drop(e)    
}

