
use core::pin::Pin;
use std::future::Future;
use std::path::Path;
use std::io::{BufRead, BufReader, Read, Write};

use mork::Space;
use pathmap::zipper::{ZipperAbsolutePath, ZipperForking, ZipperIteration, ZipperMoving, ZipperWriting};
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
    async fn work(_ctx: MorkService, cmd: Command, thread: Option<WorkThreadHandle>, _req: Request<IncomingBody>) -> Result<Bytes, CommandError> {
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
        let expr = cmd.args[0].as_expr();
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
        let src_expr = cmd.args[0].as_expr();
        let src_prefix = derive_prefix_from_expr_slice(&src_expr).till_constant_to_till_last_constant();
        let mut reader = ctx.0.space.new_reader_async(src_prefix, &()).await?;

        let dst_expr = cmd.args[1].as_expr();
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
        let expr = cmd.args[0].as_expr();
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
        &[
            PropDef {
                arg_type: ArgType::String,
                name: "format",
                desc: "The format to export, default is metta S-Expressions",
                required: false
            }
        ]
    }
    async fn work(ctx: MorkService, cmd: Command, thread: Option<WorkThreadHandle>, _req: Request<IncomingBody>) -> Result<Bytes, CommandError> {

        let (pattern, template) = pattern_template_from_sexpr_pair(&ctx.0.space, cmd.args[0].as_str(), cmd.args[1].as_str())
        .map_err(|e| CommandError::external(StatusCode::BAD_REQUEST, format!("{e:?}")))?;

        let pat_reader = ctx.0.space.new_reader_async(&derive_prefix_from_expr_slice(&pattern).till_constant_to_till_last_constant(), &()).await?;

        let format = cmd.properties[0].as_ref().map(|fmt_arg| fmt_arg.as_str()).unwrap_or("metta");
        let format = DataFormat::from_str(format).ok_or_else(|| CommandError::external(StatusCode::BAD_REQUEST, format!("Unrecognized format: {format}")))?;

        let out = tokio::task::spawn_blocking(move || -> Result<Bytes, CommandError> {
            do_export(&ctx, (pat_reader, pattern), template, format)
        }).await??;

        thread.unwrap().finalize().await;
        println!("Export command successful"); // TODO log this!

        Ok(out)
    }
}

/// Do the actual serialization
fn do_export(ctx: &MorkService, (mut reader, mut pattern): (ReadPermission, Vec<u8>), mut template: Vec<u8>, format: DataFormat) -> Result<Bytes, CommandError> {

    let buffer = match format {
        DataFormat::Metta => {
            let mut buffer = Vec::with_capacity(4096);
            let mut writer = std::io::BufWriter::new(&mut buffer);
            ctx.0.space.dump_as_sexpr(&mut writer, (&mut reader, mork_bytestring::Expr { ptr: pattern.as_mut_ptr() }), mork_bytestring::Expr { ptr: template.as_mut_ptr() }).map_err(|e|CommandError::internal(format!("failed to serialize to MeTTa S-Expressions: {e:?}")))?;
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
            while rz.to_next_val() {
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

    let space_prefix = derive_prefix_from_expr_slice(&template).till_constant_to_till_last_constant().to_owned();

    // Do the remote fetching
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

    // Do the Parsing
    //========================
    let file_path = file_resource.path()?.to_owned();
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
            println!("Inimplemnted Import from raw format");
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
        &[ArgDef{
            arg_type: ArgType::Expr,
            name: "location",
            desc: "The location of the execution of a metta thread. The location must be a ground (no variable bindings or references).\
                  \nThe thread will run and consume expressions of the form (exec <loc> (, <..patterns>) (, <..templates>)) until there are none left.\
                  \nIt is an error to spawn a thread at the same location or to execute an exec expression where the patterns and templates are not in (, <..args>) form\n
                  \nThe final status of the execution can be queried at (exec <location>)",
            required: true
        }]
    }
    fn properties() -> &'static [PropDef] {
        &[]
    }
    async fn work(ctx: MorkService, cmd: Command, _thread: Option<WorkThreadHandle>, _req: Request<IncomingBody>) -> Result<Bytes, CommandError> {
        let thread  = _thread.unwrap();

        let expr = cmd.args[0].as_expr().to_owned();

        let status_lock = move |server_space : &ServerSpace, path : Vec<u8>| {
            let status_writer = server_space.new_writer(&path, &());
            status_writer.ok().and_then(|writer|
                Option::<( _,Box<dyn for<'b> FnOnce(&'b _,_,_) + Send + Sync + 'static> )>::Some((
                    writer, 
                    Box::new(move |server_space : &ServerSpace, writer : <ServerSpace as Space>::Writer<'_>, result : Result<(), mork::space::ExecSyntaxError>|{
                        if let Err(syntax_error) = result {
                            server_space.set_user_status(writer.path(), match syntax_error {
                                mork::space::ExecSyntaxError::ExpectedArity4(e)             => unreachable!("`.to_next_val()` likely has a logic bug, the prefix should protect against this; offending expr : `{}`", e),
                                mork::space::ExecSyntaxError::ExpectedCommaListPatterns(e)  => StatusRecord::ExecSyntaxError(format!("the exec pattern list was not syntactically correct; `{}`", e)),
                                mork::space::ExecSyntaxError::ExpectedCommaListTemplates(e) => StatusRecord::ExecSyntaxError(format!("the exec template list was not syntactically correct; `{}`", e)),
                            });
                        }
                    })
                ))
            ) 
        };
        

        let (mut status_writer, fut) = match ctx.0.space.metta_calculus_localized(mork_bytestring::Expr { ptr: expr.as_ptr().cast_mut()}, status_lock) {
            Ok(f) => f,
            Err(error) => match error {
                mork::space::MettaCalculusLocalizedError::LocationWasNotAConstantExpression           => return Err(CommandError::external(StatusCode::BAD_REQUEST, "Loaction was not a ground expression.")),
                mork::space::MettaCalculusLocalizedError::LocationWasAlreadyDispatchedOnAnotherThread => return Err(CommandError::external(StatusCode::CONFLICT, "Thread is already running at that loacation.")),
            },
        };

        let status_wz = ctx.0.space.write_zipper(&mut status_writer);
        let status_path_reader = status_wz.fork_read_zipper();
        let status_location = mork_bytestring::serialize(status_path_reader.origin_path());
        drop(status_path_reader);
        drop(status_wz);
        
        thread.dispatch_blocking_task(cmd, move |_| {
            let handle = tokio::runtime::Handle::current();
            handle.block_on( 
                async move {
                    fut(&ctx.0.space, status_writer).await;
                }
            );
            Ok(())
        }).await;

        Ok(Bytes::from(format!("Thread at location `{}` was dispatched. Errors will be found at the status location of `{status_location}`", mork_bytestring::serialize(&expr))))
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
        let expr = cmd.args[0].as_expr();
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
    // ToSpacePath,
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

        ctx.0.space.transform_multi_multi(&pattern_exprs, &mut readers, &template_exprs, &mut writers);   
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


    let mut expr = space.sexpr_to_expr(input).map_err(|_| TransformMultiMultiError::ParseError)?;
    let expr_ = 
        mork_bytestring::Expr { ptr : expr.as_mut_ptr() };
    let mut expr_z = mork_bytestring::ExprZipper::new(expr_);


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
    Expr(Vec<u8>),
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
    pub fn as_expr(&self) -> &[u8] {
        match self {
            Self::Expr(expr) => &*expr,
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
        let $PREFIX = derive_prefix_from_expr_slice(& $EXPR);
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

    s.transform_multi_multi( &[] , &mut [], &[ mork_bytestring::Expr{ptr: template.as_mut_ptr()}], &mut writer);

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