
use core::pin::Pin;
use std::future::Future;
use std::path::Path;
use std::io::{BufRead, BufReader, Read, Write};
use std::any::Any;
use std::path::PathBuf;

use mork::OwnedExpr;
use mork::{Space, space::serialize_sexpr_into};
use pathmap::trie_map::BytesTrieMap;
use pathmap::zipper::{ZipperForking, ZipperIteration, ZipperMoving, ZipperWriting};
use mork_bytestring::Tag;
use tokio::fs::File;
use tokio::io::{BufWriter, AsyncWriteExt};

use bytes::BytesMut;
use hyper::{Request, StatusCode};
use hyper::body::{Incoming as IncomingBody, Bytes};
use http_body_util::BodyExt;
use url::Url;

use super::{BoxedErr, MorkService, WorkThreadHandle};
use super::status_map::{StatusRecord, FetchError, ParseError};
use super::resource_store::ResourceHandle;
use super::server_space::*;
use super::status_map::*;

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
    async fn work(ctx: MorkService, cmd: Command, thread: Option<WorkThreadHandle>, _req: Request<IncomingBody>) -> Result<Bytes, CommandError> {

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
    async fn work(ctx: MorkService, cmd: Command, _thread: Option<WorkThreadHandle>, _req: Request<IncomingBody>) -> Result<Bytes, CommandError> {
        let expr = cmd.args[0].as_expr_bytes();
        let prefix = derive_prefix_from_expr_slice(&expr).till_constant_to_till_last_constant();
        let mut writer = ctx.0.space.new_writer_async(prefix, &()).await?;

        let mut wz = ctx.0.space.write_zipper(&mut writer);
        wz.remove_branches();
        wz.remove_value();
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
    async fn work(ctx: MorkService, cmd: Command, _thread: Option<WorkThreadHandle>, _req: Request<IncomingBody>) -> Result<Bytes, CommandError> {
        let src_expr = cmd.args[0].as_expr_bytes();
        let src_prefix = derive_prefix_from_expr_slice(&src_expr).till_constant_to_till_last_constant();
        let mut reader = ctx.0.space.new_reader_async(src_prefix, &()).await?;

        let dst_expr = cmd.args[1].as_expr_bytes();
        let dst_prefix = derive_prefix_from_expr_slice(&dst_expr).till_constant_to_till_last_constant();
        let mut writer = ctx.0.space.new_writer_async(dst_prefix, &()).await?;

        let rz = ctx.0.space.read_zipper(&mut reader);
        let mut wz = ctx.0.space.write_zipper(&mut writer);
        wz.graft(&rz);
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
    async fn work(ctx: MorkService, cmd: Command, thread: Option<WorkThreadHandle>, _req: Request<IncomingBody>) -> Result<Bytes, CommandError> {
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
    async fn work(ctx: MorkService, cmd: Command, thread: Option<WorkThreadHandle>, _req: Request<IncomingBody>) -> Result<Bytes, CommandError> {

        let expr = cmd.args[0].as_expr_bytes().to_vec();
        let prefix = derive_prefix_from_expr_slice(&expr).till_constant_to_till_last_constant();
        let reader = ctx.0.space.new_reader_async(prefix, &()).await?;

        let out = tokio::task::spawn_blocking(move || -> Result<Bytes, CommandError> {
            do_bfs(&ctx, cmd, reader, expr)
        }).await??;

        thread.unwrap().finalize().await;
        println!("Explore command successful"); // TODO log this!

        Ok(out)
    }
}

fn do_bfs(ctx: &MorkService, cmd: Command, mut reader: ReadPermission, mut expr: Vec<u8>) -> Result<Bytes, CommandError> {

    let focus_token = cmd.args[1].as_path();
    let result_paths = ctx.0.space.token_bfs(focus_token, mork_bytestring::Expr { ptr: expr.as_mut_ptr() }, &mut reader);

    let mut buffer = Vec::with_capacity(4096);
    let mut writer = std::io::BufWriter::new(&mut buffer);

    let mut first = true;
    writer.write(b"(")?;
    for (new_tok, expr) in result_paths {
        if first {
            first = false
        } else {
            writer.write(b", ")?;
        }

        writer.write(b"(\"")?;
        writer.write(&new_tok[..])?;
        writer.write(b"\", ")?;

        serialize_sexpr_into(expr.borrow().ptr, &mut writer, ctx.0.space.symbol_table())
            .map_err(|e|CommandError::internal(format!("failed to serialize to MeTTa S-Expressions: {e:?}")))?;

        writer.write(b")")?;
    }
    writer.write(b")")?;

    writer.flush()?;
    drop(writer);

    Ok(hyper::body::Bytes::from(buffer))
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
        }]
    }
    async fn work(ctx: MorkService, cmd: Command, thread: Option<WorkThreadHandle>, _req: Request<IncomingBody>) -> Result<Bytes, CommandError> {

        let (pattern, template) = pattern_template_from_sexpr_pair(&ctx.0.space, cmd.args[0].as_str(), cmd.args[1].as_str())
            .map_err(|e| CommandError::external(StatusCode::BAD_REQUEST, format!("{e:?}")))?;

        let pat_reader = ctx.0.space.new_reader_async(&derive_prefix_from_expr_slice(&pattern).till_constant_to_till_last_constant(), &()).await?;

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

        let out = tokio::task::spawn_blocking(move || -> Result<Bytes, CommandError> {
            do_export(&ctx, (pat_reader, pattern), template, format, file_path)
        }).await??;

        thread.unwrap().finalize().await;
        println!("Export command successful"); // TODO log this!

        Ok(out)
    }
}

/// Do the actual serialization
fn do_export(ctx: &MorkService, (reader, pattern): (ReadPermission, Vec<u8>), template: Vec<u8>, format: DataFormat, file_path: Option<PathBuf>) -> Result<Bytes, CommandError> {
    let buffer = match &file_path {
        Some(file_path) => {
            // The rendered output will go to a file
            let file = std::fs::File::create(&file_path)?;
            let mut writer = std::io::BufWriter::new(file);
            dump_as_format(ctx, &mut writer, (reader, pattern), template, format)?;
            writer.flush()?;
            drop(writer);
            format!("Output written to file: {file_path:?}").into_bytes()
        },
        None => {
            // The rendered output will be returned directly
            let mut buffer = Vec::with_capacity(4096);
            let mut writer = std::io::BufWriter::new(&mut buffer);
            dump_as_format(ctx, &mut writer, (reader, pattern), template, format)?;
            writer.flush()?;
            drop(writer);
            buffer
        }
    };

    Ok(hyper::body::Bytes::from(buffer))
}

fn dump_as_format<W: Write>(ctx: &MorkService, writer: &mut std::io::BufWriter<W>, (mut reader, mut pattern): (ReadPermission, Vec<u8>), mut template: Vec<u8>, format: DataFormat) -> Result<(), CommandError> {
    match format {
        DataFormat::Metta => {
            ctx.0.space.dump_as_sexpr(writer, (&mut reader, mork_bytestring::Expr { ptr: pattern.as_mut_ptr() }), mork_bytestring::Expr { ptr: template.as_mut_ptr() }).map_err(|e| CommandError::internal(format!("failed to serialize to MeTTa S-Expressions: {e:?}")))?;
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
    async fn work(ctx: MorkService, cmd: Command, thread: Option<WorkThreadHandle>, _req: Request<IncomingBody>) -> Result<Bytes, CommandError> {
        //Make sure we can get a place to download the file to, and we don't have an existing download in-progress
        let file_uri = cmd.properties[0].as_ref().unwrap().as_str();
        let file_handle = ctx.0.resource_store.new_resource(file_uri, cmd.cmd_id).await?;

        let (pattern, template) = pattern_template_from_sexpr_pair(&ctx.0.space, cmd.args[0].as_str(), cmd.args[1].as_str())
        .map_err(|e| CommandError::external(StatusCode::BAD_REQUEST, format!("{e:?}")))?;

        let writer = ctx.0.space.new_writer_async(derive_prefix_from_expr_slice(&template).till_constant_to_full(), &()).await?;

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

async fn do_import(ctx: &MorkService, thread: WorkThreadHandle, cmd: &Command, pattern: Vec<u8>, template: Vec<u8>, mut writer: WritePermission, mut file_resource: ResourceHandle) -> Result<(), CommandError> {
    let file_uri = cmd.properties[0].as_ref().unwrap().as_str();
    let url = Url::parse(file_uri)?;

    let space_prefix = derive_prefix_from_expr_slice(&template).till_constant_to_till_last_constant().to_owned();

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
        let mut response = ctx.0.http_client.get(&*file_uri).send().await?;
        if !response.status().is_success() {
            //User-facing error
            println!("Import Failed. unable to fetch remote resource: {}", response.status()); //GOAT, log this failure to fetch remote resource
            let fetch_err = FetchError::new(response.status(), format!("Failed to load remote resource: {}", response.status()));
            return ctx.0.space.set_user_status(space_prefix, StatusRecord::FetchError(fetch_err))
        }

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

        do_parse(&ctx_clone.0.space, file_stream, pattern, template, &mut writer, file_type)
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
}

impl DataFormat {
    pub fn from_str(fmt_name: &str) -> Option<DataFormat> {
        let name_string = fmt_name.to_lowercase();
        match name_string.as_str() {
            "metta" => Some(DataFormat::Metta),
            "json" => Some(DataFormat::Json),
            "csv" => Some(DataFormat::Csv),
            "raw" => Some(DataFormat::Raw),
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

fn do_parse<SrcStream: Read + BufRead>(space: &ServerSpace, src: SrcStream, mut pattern: Vec<u8>, mut template: Vec<u8>, writer: &mut WritePermission, file_type: DataFormat) -> Result<(), CommandError> {
    let pattern_expr = mork_bytestring::Expr { ptr: pattern.as_mut_ptr() };
    let template_expr = mork_bytestring::Expr { ptr: template.as_mut_ptr() };
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
            let count = space.load_csv(src, pattern_expr, template_expr, writer).map_err(|e| CommandError::external(StatusCode::BAD_REQUEST, format!("{e:?}")))?;
            println!("Loaded {count} atoms from CSV");
        },
        DataFormat::Raw => {
            return Err(CommandError::external(StatusCode::BAD_REQUEST, format!("Unimplemnted Import from raw format")))
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
                async fn work(ctx: MorkService, cmd: Command, thread: Option<WorkThreadHandle>, _req: Request<IncomingBody>) -> Result<Bytes, CommandError> {
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
                            let e_ : Box<(dyn std::error::Error + Send + Sync + 'static)> = Box::new( std::io::Error::other(format!("{e:?}")));
                            e_
                        })
                    }).await;

                    Ok(Bytes::from("Load Neo4j Triples query sent"))
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
    fn args() -> &'static [ArgDef] {
        &[
            // // substitution related code (for reference when it gets implemented)
                // ArgDef{
                //     arg_type: ArgType::String,
                //     name: "initial_exec",
                //     desc: "The initial_exec must be of the form\
                //           \nwhere initial_exec is `(exec ($location <priority>) (, <..patterns>) (, <..templates>))`\
                //           \n<priority> must be a ground term.\
                //           \nThe $location will be substituted with a ground term based on the location property argument of the metta_thread_command.\
                //           ",
                //     required: true
                // }
        ]
    }
    fn properties() -> &'static [PropDef] {
        &[
            PropDef {
                arg_type: ArgType::String,
                name: "location",
                desc: "If this parameter is present the thread id will not be generated by the runtime, but will instead try to run with the one supplied.\
                      \nThe location of the execution of a metta thread. The location must be a ground (no variable bindings or references).\
                      \nThe thread will run and consume expressions of the form (exec (<loc> <priority>) (, <..patterns>) (, <..templates>)) until there are none left.\
                      \nIt is an error to spawn a thread at the same location or to execute an exec expression where the patterns and templates are not in (, <..args>) form\n
                      \nThe final status of the execution can be queried at (exec <location>)",
                required: false
            }
        ]
    }
    async fn work(ctx: MorkService, cmd: Command, _thread: Option<WorkThreadHandle>, _req: Request<IncomingBody>) -> Result<Bytes, CommandError> {
        let thread = _thread.unwrap();

        let bad_request = |s : &str| Err(CommandError::external(StatusCode::BAD_REQUEST, s));

        // // substitution related code (for reference when it gets implemented)
            // let initial_sexpr = cmd.args[0].as_str().to_owned();
            // let Ok(initial_expr) = ctx.0.space.sexpr_to_expr(&initial_sexpr) else { return bad_request("malformed priority sexpr") };
            // let initial_expr_raw = initial_expr.borrow();
            // Validate shape of initial
            // '_validate_initial : {
            //     let malformed_exec = || Err(CommandError::external(StatusCode::BAD_REQUEST, "malformed initial_exec, expected `(exec ($location <priority>) (, <..patterns>) (, <..templates>))`"));
            //     let mut initial_ez = mork_bytestring::ExprZipper::new(initial_expr_raw);
            //     let Ok(mork_bytestring::Tag::Arity(4)) = initial_ez.item() else { return malformed_exec(); };
            //     initial_ez.next();
            //     // exec
            //     if unsafe { initial_ez.subexpr().span().as_ref().unwrap() } !=  unsafe { mork::expr!(ctx.0.space, "exec").span().as_ref().unwrap() } { return malformed_exec();};
            //     initial_ez.next();

            //     // ($loc <priority>)
            //     let Ok(mork_bytestring::Tag::Arity(2)) = initial_ez.item() else { return malformed_exec(); };
            //     '_loc_priority : {
            //         let mut sub = mork_bytestring::ExprZipper::new(initial_ez.subexpr());
            //         sub.next();
            //         let Ok(Tag::NewVar) = sub.item() else { return malformed_exec(); };
            //         sub.next();
            //         if !sub.subexpr().is_ground() { return malformed_exec(); }
            //     }
            //     initial_ez.next_child();

            //     if let Err(e) = check_pattern_template(&ctx.0.space, &mut initial_ez) {
            //         match e {
            //             mork::space::ExecSyntaxError::ExpectedArity4(_)             => unreachable!("Already checked"),
            //             mork::space::ExecSyntaxError::ExpectedCommaListPatterns(_)  => return bad_request("the initial_exec pattern list was not syntactically correct; expected `(exec ($location <priority>) (, <..patterns>) (, <..templates>))`"),
            //             mork::space::ExecSyntaxError::ExpectedCommaListTemplates(_) => return bad_request("the initial_exec template list was not syntactically correct; expected `(exec ($location <priority>) (, <..patterns>) (, <..templates>))`"),
            //             mork::space::ExecSyntaxError::ExpectedGroundPriority(_)     => return bad_request("the initial_exec priority was not ground; expected `(exec ($location <priority>) (, <..patterns>) (, <..templates>))`"),
            //         };
            //     };
            // }

        let location_sexpr = match &cmd.properties[0] {
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

        let Ok(expr) = ctx.0.space.sexpr_to_expr(&location_sexpr) else { return bad_request("malformed location sexpr") };

        // //////////
        // GUARDS //
        // ////////
        let location = expr.borrow();
        if !location.is_ground() { return Err(CommandError::external(StatusCode::BAD_REQUEST, "Location was not a ground expression."));};

        // the uniqueness of this status_loc guarantees that this MeTTa-thread is the only consumer of the current thread
        let status_location_sexpr = format!("(exec {})", location_sexpr);
        let status_location = <_>::sexpr_to_expr(&ctx.0.space, &status_location_sexpr).unwrap();

        let Ok(status_writer) = (&ctx.0.space).new_writer(status_location.as_bytes(), &()) else { return  Err(CommandError::external(StatusCode::CONFLICT, "Thread is already running at that loacation.")); };

        // //////////////
        // BUILD TASK //
        // ////////////

        // // substitution related code (for reference when it gets implemented)
            // // insert initial
            // let mut substitution_buffer = vec![0u8;4096];
            // let mut oz = mork_bytestring::ExprZipper::new(mork_bytestring::Expr{ptr : substitution_buffer.as_mut_ptr()});
            // initial_expr_raw
            // .substitute_one_de_bruijn(
            //     0, 
            //     expr.borrow(), 
            //     &mut oz
            // );

            // let mut attempts_left = 1000;
            // loop {
            //     if attempts_left == 0 {
            //         return Err(CommandError::external(StatusCode::CONFLICT, "Location was under heavy contention, could not insert initial_exec"));
            //     }
            //     attempts_left -=1;
            //     let span = unsafe { &*mork_bytestring::Expr{ptr:substitution_buffer.as_mut_ptr()}.span() };
            //     if let Ok(mut w) = ctx.0.space.new_writer_async(span, &()).await {
            //         ctx.0.space.write_zipper(&mut w).set_value(());
            //         break;
            //     }
            // }
            // // TODO! JOURNAL INSERTION of INITIAL_EXEC

        // (exec (<location> $priority) $patterns $templates)
        let prefix_e_vec =  ctx.0.space.sexpr_to_expr(&format!("(exec ({} $) $ $)", location_sexpr)).unwrap();

        let task = async move|server_space : &ServerSpace, status_writer | {

            // ////////////////
            // BUILD BUFFER //
            // //////////////

            #[cfg(debug_assertions)]
            let mut loops_left = 500;

            let prefix = unsafe { prefix_e_vec.borrow().prefix().unwrap().as_ref().unwrap() };
            let mut retry = false;
            // the invariant is that buffer should always be reset with at least the prefix
            let mut buffer = Vec::from(prefix);

            // ///////////
            // PROCESS //
            // /////////

            const DBG_PRINTLN : bool = true;

            if DBG_PRINTLN { println!("\tPREFIX :{:?}", prefix) }


            let status_result : Result<(), mork::space::ExecSyntaxError> = 'process_execs : loop {
                #[cfg(debug_assertions)] if DBG_PRINTLN {println!("\tPROCESS")};

                #[cfg(debug_assertions)]
                { 
                    if loops_left == 0 { println!("TEST TOO LONG"); return } loops_left -= 1
                }
                debug_assert!(buffer.len() >= prefix.len());
                debug_assert_eq!(&buffer[..prefix.len()], prefix);

                let mut exec_permission = 'get_writer : loop { 
                    match server_space.new_writer(&prefix, &()) {
                        Ok(writer) => break 'get_writer writer,
                        Err(_) => { 
                            tokio::time::sleep(core::time::Duration::from_millis(1)).await;
                            continue 'get_writer;
                        } 
                    };
                };

                let mut exec_wz = server_space.write_zipper(&mut exec_permission);
                let mut rz = exec_wz.fork_read_zipper();
                rz.descend_to(&buffer[prefix.len()..]);


                if !rz.to_next_val() { 
                    if retry {
                        // ////////////////////
                        // LOOP TO BEGINING //
                        // //////////////////
                        #[cfg(debug_assertions)] if DBG_PRINTLN {println!("\tLOOP TO BEGINING")};
                        buffer.truncate(prefix.len());
                        tokio::time::sleep(core::time::Duration::from_millis(1)).await; 
                        continue 'process_execs;
                    }

                    // /////////////////////////////////////
                    // SUCCESSFUL CONSUMING OF ALL EXECS //
                    // ///////////////////////////////////
                    #[cfg(debug_assertions)] if DBG_PRINTLN { println!("\tSUCCESSFUL CONSUMING OF ALL EXECS")};
                    break 'process_execs Ok(())
                }
                // remember expr
                buffer.truncate(prefix.len());
                buffer.extend_from_slice(rz.path());
                drop(rz);

                if DBG_PRINTLN { println!("\tBUFFER :{:?}", buffer) }

                // remove expr in case of success
                exec_wz.descend_to(&buffer[prefix.len()..]);
                exec_wz.remove_value();
                drop(exec_wz);
                drop(exec_permission);


                let exec_expr = mork_bytestring::Expr{ ptr: buffer.as_mut_ptr() };
                let (patterns, templates) = match localized_with_priority_exec_match(server_space, exec_expr) {
                    Ok(ok) => ok,
                    Err(exec_syntax_error) => break 'process_execs Err(exec_syntax_error),
                }.collect_inner();

                let Ok((mut readers, mut writers)) = mork::space::aquire_interpret_localized_permissions(server_space, &patterns, &templates) else {
                    // /////////
                    // RETRY //
                    // ///////
                    #[cfg(debug_assertions)] if DBG_PRINTLN {println!("\tRETRY")};

                    // undo the removal on failure and retry
                    let mut exec_permission = 'get_writer : loop { 
                        match server_space.new_writer(&prefix, &()) {
                            Ok(writer) => break 'get_writer writer,
                            Err(_) => { 
                                tokio::time::sleep(core::time::Duration::from_millis(1)).await;
                                continue 'get_writer;
                            } 
                        };
                    };
                    let mut exec_wz = server_space.write_zipper(&mut exec_permission);
                    exec_wz.descend_to(&buffer[prefix.len()..]);
                    exec_wz.set_value(());

                    retry = true;
                    tokio::time::sleep(core::time::Duration::from_millis(1)).await; 
                    continue 'process_execs;
                };

                // ////////////////////////////
                // ALL PERMISSIONS ACQUIRED //
                // //////////////////////////
                let mut union_in_map = BytesTrieMap::new();
                union_in_map.insert(&buffer, ()); // this should allows reading "self" exec
                debug_assert!(union_in_map.contains_path(&buffer));

                #[cfg(debug_assertions)] if DBG_PRINTLN {println!("\tALL PERMISSIONS ACQUIRED | WRITER_COUNT : {} | READER_COUNT : {}", writers.len(), readers.len())};
                let res = server_space.transform_multi_multi(&patterns, &mut readers[..], &templates, &mut writers[..], union_in_map);
                #[cfg(debug_assertions)] if DBG_PRINTLN {println!("RES : {:?}", res)};
                retry = false;
                buffer.truncate(prefix.len());
            };


            if let Err(syntax_error) = status_result {
                    let _ = server_space.set_user_status(status_location.as_bytes(), match syntax_error {
                        mork::space::ExecSyntaxError::ExpectedArity4(e)             => unreachable!("`.to_next_val()` likely has a logic bug, the prefix should protect against this; offending expr : `{}`", e),
                        mork::space::ExecSyntaxError::ExpectedCommaListPatterns(e)  => StatusRecord::ExecSyntaxError(format!("the exec pattern list was not syntactically correct; offending expr : `{}`", e)),
                        mork::space::ExecSyntaxError::ExpectedCommaListTemplates(e) => StatusRecord::ExecSyntaxError(format!("the exec template list was not syntactically correct; offending expr : `{}`", e)),
                        mork::space::ExecSyntaxError::ExpectedGroundPriority(e)     => StatusRecord::ExecSyntaxError(format!("the exec priority was not ground; offending expr : {}", e)),});
            };

            // Free MeTTa Thread location explicty after everything is done.
            drop(status_writer);
        };

        thread.dispatch_blocking_task(cmd, move |_| {
            let handle = tokio::runtime::Handle::current();
            handle.block_on( task(&ctx.0.space, status_writer) );
            Ok(())
        }).await;

        // TODO! location needs to be pulled out with space!
        Ok(Bytes::from(format!("Thread at location `{}` was dispatched. Errors will be found at the status location of `{status_location_sexpr}`", location_sexpr)))
    }
}

/// this function should only be called on values of the form `(exec (<loc> <priority>) [, ..patterns) (, ..templates))`
/// it only checks the exec and <loc> in debug as asserts
fn localized_with_priority_exec_match(s : &(impl Space + ?Sized), exec_e : mork_bytestring::Expr)->Result<mork::space::PatternsTemplatesExprs, mork::space::ExecSyntaxError> {
    use mork_bytestring::{ExprZipper, Tag};
    use mork::{space::ExecSyntaxError, expr};
    let mut exec_ez = ExprZipper::new(exec_e);
    if exec_ez.item() != Ok(Tag::Arity(4)) {
        return Err(ExecSyntaxError::ExpectedArity4(mork_bytestring::serialize(unsafe { exec_e.span().as_ref().unwrap() })));
    }
    assert!(exec_ez.next());

    // exec
    core::debug_assert_eq!{
        unsafe { exec_ez.subexpr().span().as_ref().unwrap() },
        unsafe { expr!(s, "exec").span().as_ref().unwrap() }
    };
    assert!(exec_ez.next());

    // (<loc> <priority>)
    core::debug_assert!( exec_ez.subexpr().is_ground() );
    '_loc_priority_sub_expr : {
        let mut sub_ez = ExprZipper::new(exec_ez.subexpr());
        // (_ _)
        core::debug_assert_eq!(sub_ez.item(), Ok(Tag::Arity(2)));
        assert!(sub_ez.next());
        // <loc> debug asserted above
        assert!(sub_ez.next_child());
        // <priority>
        if !sub_ez.subexpr().is_ground() {
            return Err(ExecSyntaxError::ExpectedGroundPriority(mork_bytestring::serialize(unsafe { exec_e.span().as_ref().unwrap() })));
        }
    }
    assert!(exec_ez.next_child());

    check_pattern_template(s, &mut exec_ez)

}

/// this code expects that the zipper is NOT at the root of an S-Expr (but that the `.root`` is), rather that it is at the position that would have a pattern list, followed by a template list.
fn check_pattern_template(s : &(impl Space + ?Sized), ez : &mut mork_bytestring::ExprZipper) -> Result<mork::space::PatternsTemplatesExprs, mork::space::ExecSyntaxError> {
    use mork_bytestring::{ExprZipper, Tag};
    use mork::{space::ExecSyntaxError, expr};

    let comma_list_check = |e| {
        let mut ez = ExprZipper::new(e);
        let Ok(Tag::Arity(_)) = ez.item() else { return Err(()); };
        ez.next();

        let comma = unsafe { expr!(s, ",").span().as_ref().unwrap() };
        if unsafe { ez.subexpr().span().as_ref().unwrap() } != comma {
            return Err(());
        } else { Ok(()) }
    };

    // (, ..$patterns)
    let srcs = ez.subexpr();
    comma_list_check(srcs).map_err(|_|ExecSyntaxError::ExpectedCommaListPatterns(mork_bytestring::serialize(unsafe { ez.root.span().as_ref().unwrap() })))?;
    assert!(ez.next_child());

    // (, ..$templates)
    let dsts = ez.subexpr();
    comma_list_check(srcs).map_err(|_|ExecSyntaxError::ExpectedCommaListTemplates(mork_bytestring::serialize(unsafe { ez.root.span().as_ref().unwrap() })))?;

    Ok(mork::space::PatternsTemplatesExprs::new(srcs, dsts))
}



// ===***===***===***===***===***===***===***===***===***===***===***===***===***===***===***
// metta_thread_suspend
// ===***===***===***===***===***===***===***===***===***===***===***===***===***===***===***

/// Extracts a executing thread from the execution space to a location to be suspended
pub struct MettaThreadSuspendCmd;

impl CommandDefinition for MettaThreadSuspendCmd {
    const NAME: &'static str = "metta_thread_suspend";
    const CONST_CMD: &'static Self = &Self;
    const CONSUME_WORKER: bool = false;
    fn args() -> &'static [ArgDef] {
        &[
            ArgDef{
                arg_type: ArgType::String,
                name: "thread loaction",
                desc: "The thread location to stop execution",
                required: true
            },
            ArgDef{
                arg_type: ArgType::String,
                name: "suspend loaction",
                desc: "The location execs at the thread location will be suspended in the form ($suspend_loc (exec $thread_loc $patterns $templates))",
                required: true
            }
        ]

    }
    fn properties() -> &'static [PropDef] {
        &[]
    }
    async fn work(ctx: MorkService, cmd: Command, _thread: Option<WorkThreadHandle>, _req: Request<IncomingBody>) -> Result<Bytes, CommandError> {
        let exec_loc_sexpr = cmd.args[0].as_str().to_owned();
        let Ok(exec_loc_expr)  = ctx.0.space.sexpr_to_expr(&exec_loc_sexpr)  else { return Err(CommandError::external(StatusCode::BAD_REQUEST, format!("Invalid Sexpr for exec location : {:?}", exec_loc_sexpr))); };
        if !exec_loc_expr.borrow().is_ground() {
            return Err(CommandError::external(StatusCode::BAD_REQUEST, format!("Exec location must be ground : {}", exec_loc_sexpr)));
        }

        let suspend_loc_sexpr = cmd.args[1].as_str().to_owned();
        let Ok(suspend_loc_expr)  = ctx.0.space.sexpr_to_expr(&suspend_loc_sexpr) else { return Err(CommandError::external(StatusCode::BAD_REQUEST, format!("Invalid Sexpr for suspend location : {:?}", exec_loc_sexpr))); };
        if !suspend_loc_expr.borrow().is_ground() {
            return Err(CommandError::external(StatusCode::BAD_REQUEST, format!("Freeze location must be ground : {}", exec_loc_sexpr)));
        }


        let suspend_prefix_sexpr = format!("({} $x)", suspend_loc_sexpr);
        let suspend_prefix_expr  = ctx.0.space.sexpr_to_expr(&suspend_prefix_sexpr).unwrap();
        let suspend_prefix =  derive_prefix_from_expr_slice(suspend_prefix_expr.as_bytes()).till_constant_to_full();

        let Ok(mut suspend_writer) = ctx.0.space.new_writer_async(suspend_prefix, &()).await else {
            return Err(CommandError::external(StatusCode::CONFLICT, format!("Conflict at suspend location : {}", suspend_prefix_sexpr)));
        };


        let status_loc_sexpr = format!("(exec {})", exec_loc_sexpr);
        let status_loc_expr = ctx.0.space.sexpr_to_expr(&status_loc_sexpr).unwrap();

        let mut suspend_wz = ctx.0.space.write_zipper(&mut suspend_writer);
        suspend_wz.remove_branches();


        let exec_prefix_sexpr = format!("(exec ({} $) $ $)", exec_loc_sexpr);
        let exec_prefix_expr  = ctx.0.space.sexpr_to_expr(&exec_prefix_sexpr).unwrap();
        let exec_prefix       =  derive_prefix_from_expr_slice(exec_prefix_expr.as_bytes()).till_constant_to_full();
        let mut exec_loc_writer = loop {
            if let Ok(exec_writer) = ctx.0.space.new_writer(exec_prefix, &()) {
                break exec_writer;
            };
        };

        // if this fails, we have successfully blocked the thread
        if let Ok(_status) = ctx.0.space.new_reader(status_loc_expr.as_bytes(), &()) {
            return Err(CommandError::external(StatusCode::GONE, format!("The thread has already stopped, suspend location has been cleared : {}", suspend_prefix_sexpr)));
        };

        let mut exec_wz = ctx.0.space.write_zipper(&mut exec_loc_writer);
        let Some(pats_templates) = exec_wz.take_map() else {
            return Err(CommandError::external(StatusCode::GONE, format!("The thread has already been exhausted, suspend location has been cleared : {}", suspend_prefix_sexpr)));
        };

        suspend_wz.descend_to(exec_prefix_expr.as_bytes());
        suspend_wz.graft_map(pats_templates);

        Ok(Bytes::from(format!("Ack. Thread {} cleared, now frozen at `({} (exec ({} $priorities) $patterns $templates))`", exec_loc_sexpr, suspend_loc_sexpr, exec_loc_sexpr)))
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
    async fn work(ctx: MorkService, cmd: Command, _thread: Option<WorkThreadHandle>, _req: Request<IncomingBody>) -> Result<Bytes, CommandError> {
        let expr = cmd.args[0].as_expr_bytes();
        let prefix = derive_prefix_from_expr_slice(&expr).till_constant_to_till_last_constant();

        let status = ctx.0.space.get_status(&prefix);
        let json_string = serde_json::to_string(&status)?;
        Ok(json_string.into())
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
    async fn work(ctx: MorkService, cmd: Command, _thread: Option<WorkThreadHandle>, _req: Request<IncomingBody>) -> Result<Bytes, CommandError> {
        const IDLE_TIME_MS: u128 = 1000; //The server must be idle for 1s before shutdown will begin from a `wait_for_idle` request
        let wait_for_idle = cmd.properties[0].is_some();

        if wait_for_idle {
            tokio::task::spawn(async move {
                //This loop runs until the server has gone `IDLE_TIME_MS` without taking any new work
                let mut last_busy_time = std::time::Instant::now();
                let mut last_job_count = ctx.0.workers.job_counter();
                loop {
                    ctx.0.workers.wait_for_worker_completion().await;
                    let cur_job_count = ctx.0.workers.job_counter();
                    if last_job_count != cur_job_count {
                        last_busy_time = std::time::Instant::now();
                        last_job_count = cur_job_count;
                    }
                    if std::time::Instant::now().duration_since(last_busy_time).as_millis() > IDLE_TIME_MS {
                        break
                    }
                    std::thread::sleep(std::time::Duration::from_millis(5));
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


pub struct TransformCmd;

#[repr(usize)]
enum TransformArg {
    // FromSpacePath,
    Pattern,
    // ToSpacePath,
    Template,
    // keep this the last variant
    _Len
}

impl CommandDefinition for TransformCmd {
    const NAME: &'static str = "transform";
    const CONST_CMD: &'static Self = &Self;
    const CONSUME_WORKER: bool = true;
    fn args() -> &'static [ArgDef] {
        & const {
            const ZEROED : ArgDef = ArgDef{ arg_type: ArgType::String, name: "", desc: "", required: false}; 
            let mut args = [ZEROED; TransformArg::_Len as usize];
            use TransformArg as Arg;
            args[Arg::Pattern as usize] = 
                ArgDef{
                    arg_type: ArgType::String,
                    name: "pattern",
                    desc: "The pattern that the `from_space` expressions must conform to.",
                    required: true
                };
            args[Arg::Template as usize] = 
                ArgDef{
                    arg_type: ArgType::String,
                    name: "template",
                    desc: "The template that the `to_space` expressions will be derived from.",
                    required: true
                };
            args
        }
    }
    fn properties() -> &'static [PropDef] {
        &[]
    }
    async fn work(ctx: MorkService, cmd: Command, thread: Option<WorkThreadHandle>, _req: Request<IncomingBody>) -> Result<Bytes, CommandError> {

        // this is incorrect, pattern and template need to be parsed together!

        let transform_arg = 
            &format!(
                "(transform (, {}) (, {}))",
                cmd.args[TransformArg::Pattern as usize].as_str(),
                cmd.args[TransformArg::Template as usize].as_str(),
            );

        let transform_args = prep_transform_multi_multi(&ctx.0.space, &transform_arg).await?;

        let work_thread = thread.unwrap();
        work_thread.dispatch_blocking_task(cmd, move |_c| {

            transform_args.dispatch_transform(&ctx);
            Ok(())
        }).await;

        Ok(Bytes::from("ACK. Tranform dispatched"))
    }
}

// ===***===***===***===***===***===***===***===***===***===***===***===***===***===***===***
// transform_multi_multi
// ===***===***===***===***===***===***===***===***===***===***===***===***===***===***===***

/// expects the post body to be of this form os sexpr
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

pub struct TransformMultiMultiCmd;

impl CommandDefinition for TransformMultiMultiCmd {
    const NAME: &'static str = "transform_multi_multi";
    const CONST_CMD: &'static Self = &Self;
    const CONSUME_WORKER: bool = true;
    fn args() -> &'static [ArgDef] {
        &[]
    }
    fn properties() -> &'static [PropDef] {
        &[]
    }
    async fn work(ctx: MorkService, cmd: Command, thread: Option<WorkThreadHandle>, mut _req: Request<IncomingBody>) -> Result<Bytes, CommandError> {
        let work_thread = thread.unwrap();

        let post_bytes = get_all_post_frame_bytes(&mut _req).await?;
        let src  = core::str::from_utf8(&post_bytes).map_err(|e| CommandError::external(StatusCode::BAD_REQUEST, format!("{e:?}")))?;

        let transform_args = prep_transform_multi_multi(&ctx.0.space, src).await?;

        work_thread.dispatch_blocking_task(cmd, move |_c| {
            transform_args.dispatch_transform(&ctx);
            Ok(())
        }).await;


        Ok(Bytes::from("ACK. TranformMultiMulti dispatched"))
    }
}

struct PatternTemplateArgs {
    patterns  : Vec<Vec<u8>>,
    readers   : Vec<ReadPermission>,
    templates : Vec<Vec<u8>>,
    writers   : Vec<WritePermission>
}
impl PatternTemplateArgs {
    fn dispatch_transform(self, ctx : &MorkService) {
        let PatternTemplateArgs { patterns, mut readers, templates, mut writers } = self;
        let pattern_exprs = slices_to_exprs(&patterns);
        let template_exprs = slices_to_exprs(&templates);

        ctx.0.space.transform_multi_multi(&pattern_exprs, &mut readers, &template_exprs, &mut writers, BytesTrieMap::new());   
    }
    #[allow(unused)]
    fn is_read_write(&self) -> bool {
        self.patterns.len()== self.readers.len()
        && self.templates.len() == self.writers.len() 
        && self.patterns.len()  > 0
        && self.templates.len() > 0
    }
    #[allow(unused)]
    fn is_read(&self) -> bool {
        self.patterns.len()== self.readers.len()
        && self.writers.len()  == 0
        && self.patterns.len()  > 0 
        && self.templates.len() > 0
    }
    #[allow(unused)]
    fn is_write(&self) -> bool {
        self.templates.len() == self.writers.len() 
        && self.readers.len()  == 0
        && self.patterns.len()  > 0
        && self.templates.len() > 0
    }
}


async fn prep_transform_multi_multi(ctx: &ServerSpace, src : &str) -> Result<PatternTemplateArgs, CommandError> {
        let (patterns, templates) = pattern_template_args(
            &ctx, src
        ).map_err(|e| CommandError::external(StatusCode::BAD_REQUEST, format!("{e:?}")))?;

        let readers = prefix_readers(&ctx, &patterns).await?;
        let writers = prefix_writers(&ctx, &templates).await?;

        Ok(PatternTemplateArgs { patterns, readers, templates, writers })
}
async fn prefix_readers(ctx : &ServerSpace, patterns : &[impl AsRef<[u8]>]) -> Result<Vec<ReadPermission>, CommandError> {
    let mut readers = Vec::with_capacity(patterns.len());
    for pattern in patterns {
        if pattern.as_ref().is_empty() {
            return Err(CommandError::internal(String::from("unexpected empty Expr")));
        }
        let reader = ctx.new_reader_async(derive_prefix_from_expr_slice(pattern.as_ref()).till_constant_to_full(), &()).await?;
        readers.push(reader);
    }
    Ok(readers)
}
async fn prefix_writers(ctx : &ServerSpace, templates : &[impl AsRef<[u8]>]) -> Result<Vec<WritePermission>, CommandError> {
    let mut writers = Vec::with_capacity(templates.len());
    for template in templates {
        if template.as_ref().is_empty() {
            return Err(CommandError::internal(String::from("unexpected empty Expr")));
        }
        let writer = ctx.new_writer_async(derive_prefix_from_expr_slice(template.as_ref()).till_constant_to_full(), &()).await?;
        writers.push(writer);
    }
    Ok(writers)
}
fn slices_to_exprs(slices : &[impl AsRef<[u8]>])->Vec<mork_bytestring::Expr>{
    slices.into_iter().map(|pattern| mork_bytestring::Expr { ptr : pattern.as_ref().as_ptr() as *mut _ }).collect()
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
fn pattern_template_from_sexpr_pair(space : &ServerSpace, pattern : &str, template : &str)->Result<(Vec<u8>, Vec<u8>), TransformMultiMultiError> {
        let formatted = format!(
            "(transform (, {}) (, {}) )",
            pattern, 
            template,
        );
        let (mut patterns, mut templates) = pattern_template_args(&space, &formatted)?;
        // Ok((patterns.pop().unwrap(), templates.pop().unwrap()))
        Ok((patterns.pop().unwrap_or(Vec::new()), templates.pop().unwrap_or(Vec::new())))

}
fn pattern_template_args(space : &ServerSpace,input : &str)->Result<(Vec<Vec<u8>>, Vec<Vec<u8>>), TransformMultiMultiError> {
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


    Ok((out_paterns,out_templates))
}

fn comma_list_expr(space : &ServerSpace, expr : mork_bytestring::Expr) -> Result<Vec<Vec<u8>>, &'static str> {

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
                out.push(unsafe { &*sub.span() }.to_vec())
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
    async fn work(ctx: MorkService, cmd: Command, thread: Option<WorkThreadHandle>, mut req: Request<IncomingBody>) -> Result<Bytes, CommandError> {
        let format = cmd.properties[0].as_ref().map(|fmt_arg| fmt_arg.as_str()).unwrap_or("metta");
        let format = DataFormat::from_str(format).ok_or_else(|| CommandError::external(StatusCode::BAD_REQUEST, format!("Unrecognized format: {format}")))?;

        let (pattern, template) = pattern_template_from_sexpr_pair(&ctx.0.space, cmd.args[0].as_str(), cmd.args[1].as_str())
            .map_err(|e| CommandError::external(StatusCode::BAD_REQUEST, format!("{e:?}")))?;

        let mut writer = ctx.0.space.new_writer(derive_prefix_from_expr_slice(&template).till_constant_to_full(), &())?;

        //Read all the data from the post request

        // Do the Parsing
        //========================
        let ctx_clone   = ctx.clone();
        let src_buf     = get_all_post_frame_bytes(&mut req).await?;
        let data_format = format;
        match tokio::task::spawn_blocking(move || {
            do_parse(&ctx_clone.0.space, &src_buf[..], pattern, template, &mut writer, data_format)
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
    fn work(ctx: MorkService, cmd: Command, thread: Option<WorkThreadHandle>, req: Request<IncomingBody>) -> impl Future<Output=Result<Bytes, CommandError>> + Sync + Send;
}

/// Object-safe wrapper over CommandDefinition
pub trait CmdDefObject: 'static + Send + Sync {
    fn name(&self) -> &'static str;
    fn consume_worker(&self) -> bool;
    // fn args(&self) -> &'static [ArgDef];
    // fn properties(&self) -> &'static [PropDef];
    fn work(&self, ctx: MorkService, cmd: Command, thread: Option<WorkThreadHandle>, req: Request<IncomingBody>) -> Pin<Box<dyn Future<Output=Result<Bytes, CommandError>> + Sync + Send>>;
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
    fn work(&self, ctx: MorkService, cmd: Command, thread: Option<WorkThreadHandle>, req: Request<IncomingBody>) -> Pin<Box<dyn Future<Output=Result<Bytes, CommandError>> + Sync + Send>> {
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
            StatusRecord::ExecSyntaxError(err) =>Self::external(StatusCode::CONFLICT, err),
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



#[cfg(test)]
#[tokio::test]
async fn misbehaving_transform() -> Result<(), ()> {
    let s = ServerSpace::new();

    let (pattern, mut template) = pattern_template_from_sexpr_pair(&s, "", "c").unwrap();
    let Err(_) = prefix_readers(&s, &[&pattern]).await else {panic!()};

    let mut writer = prefix_writers(&s, &[&template]).await.unwrap();
    core::assert!(writer.len() == 1);

    s.transform_multi_multi( &[] , &mut [], &[ mork_bytestring::Expr{ptr: template.as_mut_ptr()}], &mut writer, BytesTrieMap::new());

    drop(writer);

    let (mut pattern, mut templates) = pattern_template_from_sexpr_pair(&s, "$x", "$x").unwrap();
    let mut reader = prefix_readers(&s, &[&pattern]).await.unwrap();

    let mut out = Vec::new();
    s.dump_as_sexpr(&mut out, (&mut reader[0] , mork_bytestring::Expr{ptr : pattern.as_mut_ptr()}), mork_bytestring::Expr {ptr : templates.as_mut_ptr()}).unwrap();

    // this prints "c" !
    println!("{}", unsafe {
        core::mem::transmute::<_, String>(out)
    });

    Ok(())
}