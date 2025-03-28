
use core::pin::Pin;
use std::future::Future;
use std::path::Path;
use std::io::{Read, Write};

use mork::Space;
use pathmap::zipper::{ZipperIteration, ZipperMoving, ZipperWriting};
use tokio::fs::File;
use tokio::io::{BufWriter, AsyncWriteExt};

use bytes::BytesMut;
use hyper::{Request, StatusCode};
use hyper::body::{Incoming as IncomingBody, Bytes};
use http_body_util::BodyExt;

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
    fn properties() -> &'static [PropDef] { &[] }
    async fn gather(_ctx: MorkService, _cmd: Command, _req: Request<IncomingBody>) -> Result<Option<Resources>, CommandError> {
        Ok(None)
    }
    async fn work(_ctx: MorkService, thread: Option<WorkThreadHandle>, cmd: Command, _resources: Option<Resources>) -> Result<Bytes, CommandError> {
        thread.unwrap().dispatch_blocking_task(cmd, move |cmd| {
            let millis = cmd.args[0].as_u64();
            std::thread::sleep(std::time::Duration::from_millis(millis));
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
            arg_type: ArgType::Path,
            name: "path",
            desc: "The map path to clear",
            required: true
        }]
    }
    fn properties() -> &'static [PropDef] {
        &[]
    }
    async fn gather(ctx: MorkService, cmd: Command, _req: Request<IncomingBody>) -> Result<Option<Resources>, CommandError> {
        let map_path = cmd.args[0].as_path();
        let writer = ctx.0.space.new_writer(map_path, &())?;
        Ok(Some(Resources::new(writer)))
    }
    async fn work(ctx: MorkService, _thread: Option<WorkThreadHandle>, _cmd: Command, resources: Option<Resources>) -> Result<Bytes, CommandError> {
        let mut writer = resources.unwrap().downcast::<WritePermission>();
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
            arg_type: ArgType::Path,
            name: "src_path",
            desc: "The map path from which to copy",
            required: true
        },
        ArgDef{
            arg_type: ArgType::Path,
            name: "dst_path",
            desc: "The map path to copy into",
            required: true
        }]
    }
    fn properties() -> &'static [PropDef] {
        &[]
    }
    async fn gather(ctx: MorkService, cmd: Command, _req: Request<IncomingBody>) -> Result<Option<Resources>, CommandError> {
        let src_path = cmd.args[0].as_path();
        let reader = ctx.0.space.new_reader(src_path, &())?;
        let dst_path = cmd.args[1].as_path();
        let writer = ctx.0.space.new_writer(dst_path, &())?;
        Ok(Some(Resources::new(CopyCmdResources{reader, writer})))
    }
    async fn work(ctx: MorkService, _thread: Option<WorkThreadHandle>, _cmd: Command, resources: Option<Resources>) -> Result<Bytes, CommandError> {
        let mut resources = resources.unwrap().downcast::<CopyCmdResources>();
        let rz = ctx.0.space.read_zipper(&mut resources.reader);
        let mut wz = ctx.0.space.write_zipper(&mut resources.writer);
        wz.graft(&rz);
        Ok("ACK. Copied".into())
    }
}

struct CopyCmdResources {
    reader: ReadPermission,
    writer: WritePermission,
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
            arg_type: ArgType::Path,
            name: "path",
            desc: "The path in the map from which to count the values",
            required: true
        }]
    }
    fn properties() -> &'static [PropDef] {
        &[]
    }
    async fn gather(ctx: MorkService, cmd: Command, _req: Request<IncomingBody>) -> Result<Option<Resources>, CommandError> {
        let map_path = cmd.args[0].as_path();
        let reader = ctx.0.space.new_reader(map_path, &())?;
        Ok(Some(Resources::new(reader)))
    }
    async fn work(ctx: MorkService, thread: Option<WorkThreadHandle>, cmd: Command, resources: Option<Resources>) -> Result<Bytes, CommandError> {
        tokio::task::spawn(async move {
            match do_count(&ctx, thread.unwrap(), &cmd, resources.unwrap()).await {
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

async fn do_count(ctx: &MorkService, thread: WorkThreadHandle, _cmd: &Command, resources: Resources) -> Result<(), CommandError> {

    let ctx_clone = ctx.clone();
    tokio::task::spawn_blocking(move || -> Result<(), CommandError> {
        let mut reader = resources.downcast::<ReadPermission>();
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
            arg_type: ArgType::Path,
            name: "src_path",
            desc: "The path in the map from which to export",
            required: true
        }]
    }
    fn properties() -> &'static [PropDef] {
        &[
            PropDef {
                arg_type: ArgType::String,
                name: "format",
                desc: "The format to export, default is metta S-Expressions",
                required: false
            }
        ]
    }
    async fn gather(ctx: MorkService, cmd: Command, _req: Request<IncomingBody>) -> Result<Option<Resources>, CommandError> {
        let format = cmd.properties[0].as_ref().map(|fmt_arg| fmt_arg.as_str()).unwrap_or("metta");
        let format = DataFormat::from_str(format).ok_or_else(|| CommandError::external(StatusCode::BAD_REQUEST, format!("Unrecognized format: {format}")))?;

        //Get the reader for this path in the map, which makes it off-limits to writers
        let map_path = cmd.args[0].as_path();
        let reader = ctx.0.space.new_reader(map_path, &())?;
        Ok(Some(Resources::new(ExportCmdResources{
            format,
            reader
        })))
    }
    async fn work(ctx: MorkService, thread: Option<WorkThreadHandle>, _cmd: Command, resources: Option<Resources>) -> Result<Bytes, CommandError> {
        let export_resources = resources.unwrap().downcast::<ExportCmdResources>();

        let out = tokio::task::spawn_blocking(move || -> Result<Bytes, CommandError> {
            do_export(&ctx, export_resources)
        }).await??;

        thread.unwrap().finalize().await;
        println!("Export command successful"); // TODO log this!

        Ok(out)
    }
}

struct ExportCmdResources {
    format: DataFormat,
    reader: ReadPermission,
}

/// Do the actual serialization
fn do_export(ctx: &MorkService, ExportCmdResources { mut reader, format }: ExportCmdResources) -> Result<Bytes, CommandError> {

    let buffer = match format {
        DataFormat::Metta => {
            let mut buffer = Vec::with_capacity(4096);
            let mut writer = std::io::BufWriter::new(&mut buffer);
            ctx.0.space.dump_as_sexpr(&mut writer, &mut reader).map_err(|e|CommandError::internal(format!("failed to serialize to MeTTa S-Expressions: {e:?}")))?;
            writer.flush()?;
            drop(writer);
            buffer
        },
        DataFormat::Csv |
        DataFormat::Json => {
            b"Export Error: Unimplemented Export Format".to_vec()
        },
        DataFormat::Raw => {
            let mut buffer = Vec::with_capacity(4096);
            let mut writer = std::io::BufWriter::new(&mut buffer);
            let mut rz = ctx.0.space.read_zipper(&mut reader);
            while let Some(_) = rz.to_next_val() {
                writeln!(writer, "{:?}", rz.path()).map_err(|e|CommandError::internal(format!("Error occurred writing raw paths: {e:?}")))?;
            }
            writer.flush()?;
            drop(writer);
            buffer
        }
    };

    Ok(hyper::body::Bytes::from(buffer))
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
            arg_type: ArgType::Path,
            name: "dst_path",
            desc: "The path in the map at which to import the file",
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
    async fn gather(ctx: MorkService, cmd: Command, _req: Request<IncomingBody>) -> Result<Option<Resources>, CommandError> {
        //Make sure we can get a place to download the file to, and we don't have an existing download in-progress
        let file_uri = cmd.properties[0].as_ref().unwrap().as_str();
        let file_handle = ctx.0.resource_store.new_resource(file_uri, cmd.cmd_id).await?;

        //Flag this path in the map as being busy, and therefore off-limits to other operations
        let map_path = cmd.args[0].as_path();
        let writer = ctx.0.space.new_writer(map_path, &())?;

        Ok(Some(Resources::new(ImportCmdResources{
            file: file_handle,
            writer,
        })))
    }
    async fn work(ctx: MorkService, thread: Option<WorkThreadHandle>, cmd: Command, resources: Option<Resources>) -> Result<Bytes, CommandError> {

        //QUESTION: Should we let the fetch run for a small amount of time (like 300ms) to see if
        // it fails straight away, so we can report that failure immediately?
        //My thinking is no, because the caller needs to write code to handle the case when the
        // fetch takes too long.  So it we always return success, and then caller has one fewer
        // case to worry about.

        tokio::task::spawn(async move {
            match do_import(&ctx, thread.unwrap(), &cmd, resources.unwrap()).await {
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

struct ImportCmdResources {
    file: ResourceHandle,
    writer: WritePermission,
}

async fn do_import(ctx: &MorkService, thread: WorkThreadHandle, cmd: &Command, resources: Resources) -> Result<(), CommandError> {
    let file_uri = cmd.properties[0].as_ref().unwrap().as_str();
    let mut resources = resources.downcast::<ImportCmdResources>();

    // Do the remote fetching
    //========================
    let mut response = ctx.0.http_client.get(&*file_uri).send().await?;
    if !response.status().is_success() {
        //User-facing error
        println!("Import Failed. unable to fetch remote resource: {}", response.status()); //GOAT, log this failure to fetch remote resource
        let fetch_err = FetchError::new(response.status(), format!("Failed to load remote resource: {}", response.status()));
        return ctx.0.space.set_user_status(resources.writer.path(), StatusRecord::FetchError(fetch_err))
    }

    let mut writer = BufWriter::new(File::create(resources.file.path()?).await?);

    //GOAT!!!  We need to communicate back to the user if the download craps out in the middle
    while let Some(chunk) = response.chunk().await? {
        writer.write(&*chunk).await?;
    }
    writer.flush().await?;

    println!("Successful download from '{}', file saved to '{:?}'", file_uri, resources.file.path()?); //GOAT Log this sucessful completion

    // Do the Parsing
    //========================
    let file_path = resources.file.path()?.to_owned();
    let file_type = match detect_file_type(&file_path, file_uri) {
        Ok(file_type) => file_type,
        Err(err) => {
            //User-facing error
            println!("Import Failed. Unrecognized file type: {err:?}"); //GOAT, log this failure
            let parse_err = ParseError::new(format!("Failed to recognize file format: {err:?}"));
            return ctx.0.space.set_user_status(resources.writer.path(), StatusRecord::ParseError(parse_err))
        }
    };

    let ctx_clone = ctx.clone();
    let map_path = resources.writer.path().to_owned();
    let mut path_writer = resources.writer;
    match tokio::task::spawn_blocking(move || {
        //GOAT, Reading the whole file into a ginormous buffer is a terrible idea.
        // I'm sure the parser is capable of streaming or chunking but I gotta
        // figure out the right way to chunk the input without corrupting any data
        let mut file_handle = std::fs::File::open(&file_path)?;
        let mut buffer = Vec::new();
        file_handle.read_to_end(&mut buffer)?;

        do_parse(&ctx_clone.0.space, &buffer[..], &mut path_writer, file_type)
    }).await.map_err(CommandError::internal)? {
        Ok(()) => {},
        Err(err) => {
            //User-facing error
            println!("Import Failed. Parse error: {err:?}"); //GOAT, log this failure
            let parse_err = ParseError::new(format!("Failed to parse file: {err:?}"));
            return ctx.0.space.set_user_status(map_path, StatusRecord::ParseError(parse_err))
        }
    };

    //Finalize the resource
    let timestamp = 987654321; //GOAT, use the real timestamp from this command.
    resources.file.finalize(timestamp).await?;

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

fn do_parse(space: &ServerSpace, src_buf: &[u8], dst: &mut WritePermission, file_type: DataFormat) -> Result<(), CommandError> {
    match file_type {
        DataFormat::Metta => {
            let count = space.load_sexpr(std::str::from_utf8(src_buf)?, dst).map_err(|e| CommandError::external(StatusCode::BAD_REQUEST, format!("{e:?}")))?;
            println!("Loaded {count} atoms from MeTTa S-Expr");
        },
        DataFormat::Json => {
            let count = space.load_json(std::str::from_utf8(src_buf)?, dst).map_err(|e| CommandError::external(StatusCode::BAD_REQUEST, format!("{e:?}")))?;
            println!("Loaded {count} atoms from JSON");
        },
        DataFormat::Csv => {
            let count = space.load_csv(std::str::from_utf8(src_buf)?, dst).map_err(|e| CommandError::external(StatusCode::BAD_REQUEST, format!("{e:?}")))?;
            println!("Loaded {count} atoms from CSV");
        },
        DataFormat::Raw => {
            println!("Inimplemnted Import from raw format");
        }
    }
    Ok(())
}

#[cfg(feature="neo4j")]
mod neo4j_commands {
use crate::commands::*;

// ===***===***===***===***===***===***===***===***===***===***===***===***===***===***===***
// LoadNeo4jTriples
// ===***===***===***===***===***===***===***===***===***===***===***===***===***===***===***

pub struct LoadNeo4jTriplesCmd;
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

impl CommandDefinition for LoadNeo4jTriplesCmd {
    const NAME: &'static str = "status";
    const CONST_CMD: &'static Self = &Self;
    const CONSUME_WORKER: bool = true;
    fn args() -> &'static [ArgDef] {
        & const {
            use LoadNeo4jArg as Arg;
            const ZEROED : ArgDef = ArgDef{ arg_type: ArgType::String, name: "", desc: "", required: false}; 
            let mut args = [ZEROED; Arg::_Len as usize];
        

            args[Arg::OutputPath as usize] = 
                ArgDef{
                    arg_type: ArgType::Path,
                    name: "output_path",
                    desc: "the path where the loaded data will be stored",
                    required: true
                };


            args
        }
    }
    fn properties() -> &'static [PropDef] {
        &[]
    }
    async fn gather(_ctx: MorkService, _cmd: Command, _req: Request<IncomingBody>) -> Result<Option<Resources>, CommandError> {
        Ok(None)
    }
    async fn work(ctx: MorkService, _thread: Option<WorkThreadHandle>, cmd: Command, _resources: Option<Resources>) -> Result<Bytes, CommandError> {
        let map_path = cmd.args[0].as_path();
        let status = ctx.0.space.get_status(map_path);
        let json_string = serde_json::to_string(&status)?;
        Ok(json_string.into())
    }
}


}
#[cfg(feature="neo4j")]
#[allow(unused)]
pub use neo4j_commands::*;

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
            arg_type: ArgType::Path,
            name: "path",
            desc: "The path in the map for which to check the status",
            required: true
        }]
    }
    fn properties() -> &'static [PropDef] {
        &[]
    }
    async fn gather(_ctx: MorkService, _cmd: Command, _req: Request<IncomingBody>) -> Result<Option<Resources>, CommandError> {
        Ok(None)
    }
    async fn work(ctx: MorkService, _thread: Option<WorkThreadHandle>, cmd: Command, _resources: Option<Resources>) -> Result<Bytes, CommandError> {
        let map_path = cmd.args[0].as_path();
        let status = ctx.0.space.get_status(map_path);
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
    async fn gather(_ctx: MorkService, _cmd: Command, _req: Request<IncomingBody>) -> Result<Option<Resources>, CommandError> {
        Ok(None)
    }
    async fn work(ctx: MorkService, _thread: Option<WorkThreadHandle>, cmd: Command, _resources: Option<Resources>) -> Result<Bytes, CommandError> {
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

/// Returns the status associated with a path in the trie
pub struct TransformCmd;

#[repr(usize)]
enum TransformArg {
    FromSpacePath,
    ToSpacePath,
    Pattern,
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
            args[Arg::FromSpacePath as usize] = 
                ArgDef{
                    arg_type: ArgType::Path,
                    name: "from_space_path",
                    desc: "The path in the map to be matched, the `from_space`. It must be disjoint with the `to_space_path`",
                    required: true
                };
            args[Arg::ToSpacePath as usize] = 
                ArgDef{
                    arg_type: ArgType::Path,
                    name: "to_space_path",
                    desc: "The path in the map to be be written to, the `to_space`. It must be disjoint with the `from_space_path`",
                    required: true
                };
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
    async fn gather(ctx: MorkService, _cmd: Command, _req: Request<IncomingBody>) -> Result<Option<Resources>, CommandError> {
        // get path permissions
        let from_space = ctx.0.space.new_reader(_cmd.args[TransformArg::FromSpacePath as usize].as_path(), &())?;
        let to_space = ctx.0.space.new_writer(_cmd.args[TransformArg::ToSpacePath as usize].as_path(), &())?;

        Ok(Some(Resources::new(TransformResourses {
                from_space,
                to_space,
                pattern: 
                    ctx.0.space.sexpr_to_expr(_cmd.args[TransformArg::Pattern as usize].as_str())
                    .map_err(|e| CommandError::external(StatusCode::EXPECTATION_FAILED, format!("Failed to parse `pattern` : {e:?}")) )?,
                template: 
                    ctx.0.space.sexpr_to_expr(_cmd.args[TransformArg::Template as usize].as_str())
                    .map_err(|e| CommandError::external(StatusCode::EXPECTATION_FAILED, format!("Failed to parse `template` : {e:?}")) )?,
            })))
    }
    async fn work(ctx: MorkService, _thread: Option<WorkThreadHandle>, cmd: Command, _resources: Option<Resources>) -> Result<Bytes, CommandError> {
        let work_thread = _thread.unwrap();
        let TransformResourses { from_space : mut reader, to_space : mut writer, mut pattern, mut template } = _resources.unwrap().downcast(); 

        work_thread.dispatch_blocking_task(cmd, move |_c| {
            ctx.0.space.transform(&mut reader, &mut writer, mork_bytestring::Expr { ptr: pattern.as_mut_ptr() }, mork_bytestring::Expr { ptr: template.as_mut_ptr() });
            Ok(())
        }).await;

        Ok(Bytes::from("ACK. Tranform dispatched"))
    }
}
struct TransformResourses {
    from_space : ReadPermission,
    to_space   : WritePermission,
    pattern    : mork::OwnedExpr,
    template   : mork::OwnedExpr,
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
            arg_type: ArgType::Path,
            name: "dst_path",
            desc: "The path in the map at which to put the uploaded data",
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
    async fn gather(ctx: MorkService, cmd: Command, mut req: Request<IncomingBody>) -> Result<Option<Resources>, CommandError> {
        let format = cmd.properties[0].as_ref().map(|fmt_arg| fmt_arg.as_str()).unwrap_or("metta");
        let format = DataFormat::from_str(format).ok_or_else(|| CommandError::external(StatusCode::BAD_REQUEST, format!("Unrecognized format: {format}")))?;

        //Flag this path in the map as being busy, and therefore off-limits to other operations
        let map_path = cmd.args[0].as_path();
        let writer = ctx.0.space.new_writer(map_path, &())?;

        //Read all the data from the post request
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

        Ok(Some(Resources::new(UploadCmdResources{
            format: format,
            writer,
            data: post_data_buf.freeze(),
        })))
    }
    async fn work(ctx: MorkService, thread: Option<WorkThreadHandle>, _cmd: Command, resources: Option<Resources>) -> Result<Bytes, CommandError> {
        let resources = resources.unwrap().downcast::<UploadCmdResources>();

        // Do the Parsing
        //========================
        let ctx_clone = ctx.clone();
        let mut path_writer = resources.writer;
        let src_buf = resources.data;
        let data_format = resources.format;
        match tokio::task::spawn_blocking(move || {
            do_parse(&ctx_clone.0.space, &src_buf[..], &mut path_writer, data_format)
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

struct UploadCmdResources {
    format: DataFormat,
    writer: WritePermission,
    data: Bytes,
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

    /// Function to gather resources needed to execute the command
    fn gather(ctx: MorkService, cmd: Command, req: Request<IncomingBody>) -> impl Future<Output=Result<Option<Resources>, CommandError>> + Sync + Send;

    /// Method to perform the execution.  If anything CPU-intensive is done in this method,
    /// it should call `dispatch_blocking_task` for that work
    fn work(ctx: MorkService, thread: Option<WorkThreadHandle>, cmd: Command, resources: Option<Resources>) -> impl Future<Output=Result<Bytes, CommandError>> + Sync + Send;
}

/// An abstract type to contain the resources needed to execute the command
pub struct Resources(Box<dyn core::any::Any + Send + Sync>);

impl Resources {
    pub fn new<T: Send + Sync + 'static>(t: T) -> Self {
        //GOAT, Figure out something better than this double-box!!!
        Resources(Box::new(Some(Box::new(t))))
    }
    pub fn downcast<T: 'static>(mut self) -> T {
        let inner = self.0.downcast_mut::<Option<Box<T>>>().unwrap();
        *core::mem::take(inner).unwrap()
    }
}

/// Object-safe wrapper over CommandDefinition
pub trait CmdDefObject: 'static + Send + Sync {
    fn name(&self) -> &'static str;
    fn consume_worker(&self) -> bool;
    // fn args(&self) -> &'static [ArgDef];
    // fn properties(&self) -> &'static [PropDef];
    fn gather(&self, ctx: MorkService, cmd: Command, req: Request<IncomingBody>) -> Pin<Box<dyn Future<Output=Result<Option<Resources>, CommandError>> + Sync + Send>>;
    fn work(&self, ctx: MorkService, thread: Option<WorkThreadHandle>, cmd: Command, resources: Option<Resources>) -> Pin<Box<dyn Future<Output=Result<Bytes, CommandError>> + Sync + Send>>;
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
    fn gather(&self, ctx: MorkService, cmd: Command, req: Request<IncomingBody>) -> Pin<Box<dyn Future<Output=Result<Option<Resources>, CommandError>> + Sync + Send>> {
        Box::pin(Self::gather(ctx, cmd, req))
    }
    fn work(&self, ctx: MorkService, thread: Option<WorkThreadHandle>, cmd: Command, resources: Option<Resources>) -> Pin<Box<dyn Future<Output=Result<Bytes, CommandError>> + Sync + Send>> {
        Box::pin(Self::work(ctx, thread, cmd, resources))
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
    pub(crate) log_message: String,
    pub(crate) status_code: StatusCode,
}

impl ExternalError {
    pub fn new<M: Into<String>>(status_code: StatusCode, log_message: M) -> Self {
        Self {
            status_code, log_message: log_message.into()
        }
    }
}

impl CommandError {
    pub fn internal<Desc: Into<Box<dyn core::error::Error + Send + Sync>>>(desc: Desc) -> Self {
        Self::Internal(desc.into())
    }
    pub fn external<M: Into<String>>(status_code: StatusCode, log_message: M) -> Self {
        Self::External(ExternalError{ status_code, log_message: log_message.into() })
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
    Flag, Int, UInt, Path, String
}

#[derive(Clone, Debug, Default)]
pub enum ArgVal {
    #[default]
    None,
    Flag,
    Int(i64),
    UInt(u64),
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
}
