
use std::borrow::Cow;
use std::net::SocketAddr;
use std::sync::{Arc, atomic::AtomicU64};
use std::future::Future;
use std::pin::Pin;
use std::path::PathBuf;

use tokio::sync::Notify;

use http_body_util::{combinators::BoxBody, BodyExt, Empty, Full};

use hyper::service::Service;
use hyper::{Method, Request, Response, StatusCode, Uri};
use hyper::body::{Incoming as IncomingBody, Bytes};
use hyper::server::conn::http1;
use hyper_util::rt::TokioIo;
use tokio::net::TcpListener;

const SERVER_ADDR_ENV_VAR: &str = "MORK_SERVER_ADDR";
const SERVER_PORT_ENV_VAR: &str = "MORK_SERVER_PORT";
const RESOURCE_DIR_ENV_VAR: &str = "MORK_SERVER_DIR";
const DEFAULT_SERVER_ADDR: &str = "127.0.0.1";
const DEFAULT_SERVER_PORT: &str = "8000";
const DEFAULT_RESOURCE_DIR: &str = "/tmp/mork_server_files";

mod commands;
use commands::*;

mod status_map;
mod server_space;
use server_space::*;
use mork::{Space, OwnedExpr};

mod resource_store;
use resource_store::*;

type BoxedErr = Box<dyn std::error::Error + Send + Sync>;

fn server_addr() -> SocketAddr {
    let addr_str = std::env::var(SERVER_ADDR_ENV_VAR).unwrap_or(DEFAULT_SERVER_ADDR.to_string());
    let port_str = std::env::var(SERVER_PORT_ENV_VAR).unwrap_or(DEFAULT_SERVER_PORT.to_string());

    //First try to parse the address with a port included
    match addr_str.parse() {
        Ok(socket_addr) => return socket_addr,
        Err(_) => {
            //If that failed, parse the address as a stand-alone IP address with a separate port
            let addr = addr_str.parse::<std::net::IpAddr>().expect("Invalid IP Address Format");
            return SocketAddr::new(addr, port_str.parse().expect("Invalid Port Format"))
        }
    }
}

fn resource_dir() -> PathBuf {
    let path_str = std::env::var(RESOURCE_DIR_ENV_VAR).unwrap_or(DEFAULT_RESOURCE_DIR.to_string());
    PathBuf::from(path_str)
}

#[derive(Clone)]
pub struct MorkService(Arc<MorkServiceInternals>);

struct MorkServiceInternals {
    /// Signal when a shutdown command has been executed
    stop_cmd: Notify,
    /// Pool of worker threads to handled blocking pathmap operations
    workers: WorkerPool,
    /// Versioned storage for on-disk resources
    resource_store: ResourceStore,
    /// The http client used to fetch remote files
    http_client: reqwest::Client,
    /// The MORK kernel space
    space: ServerSpace,
    /// A monotonically incrementing counter so each request has a unique ID
    request_counter: AtomicU64,

    //GOAT, need cmd-logger to facilitate replay, and maybe a separate human-readable log
    //GOAT, need permissions model
}

impl MorkService {
    pub async fn new() -> Self {

        let http_client_builder = reqwest::Client::builder();
        let http_client = http_client_builder
                .gzip(true)
                .deflate(true)
                .build().unwrap();

        // Init the ResourceStore
        let resource_store = ResourceStore::new_with_dir_path(&resource_dir()).await.unwrap();
        resource_store.reset().await.unwrap();

        // GOAT, this needs to come from the backup
        let request_counter = AtomicU64::new(0);

        let space = ServerSpace::new();

        let internals = MorkServiceInternals {
            stop_cmd: Notify::new(),
            workers: WorkerPool::new(),
            space,
            resource_store,
            http_client,
            request_counter,
        };
        Self(Arc::new(internals))
    }
    pub async fn run(&self, addr: SocketAddr) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let http = http1::Builder::new();
        let shutdown_watcher = hyper_util::server::graceful::GracefulShutdown::new();

        let listener = TcpListener::bind(addr).await?;
        println!("Server starting. {} worker threads. Listening on {addr:?}...", self.0.workers.thread_count()); //GOAT Log this

        //Connection listener loop
        loop {
            tokio::select! {
                Ok((stream, _addr)) = listener.accept() => {
                    let io = TokioIo::new(stream);
                    let mork_service_clone = self.clone();
                    let conn = http.serve_connection(io, mork_service_clone);
                    let future = shutdown_watcher.watch(conn);
                    tokio::task::spawn(async move {
                        if let Err(err) = future.await {
                            println!("Internal Server Error: Failed to serve connection: {:?}", err); //GOAT log this.  Likely the client closed the connection before we could reply
                        }
                    });
                },
                _ = self.0.stop_cmd.notified() => {
                    break;
                }
                _ = got_cntl_c() => {
                    break;
                }
            }
        }

        println!("Beginnging shutdown.  No new connections will be accepted"); //GOAT log this.

        //Wait for all connections finish
        shutdown_watcher.shutdown().await;
        drop(listener);

        // *===***===*
        // At this point, there are no open server connections, but the server may still be performing work
        // *===***===*

        //Wait for all work to complete
        self.0.workers.wait_for_worker_completion().await;

        // *===***===*
        // At this point all work is finished
        // *===***===*

        println!("Server terminating"); //GOAT Log this

        Ok(())
    }
    /// Attempts to allocate a worker thread to run `work_f`, and replies with an `ack` or a busy response
    fn dispatch_work(&self, command: Command, req: Request<IncomingBody>) -> <Self as Service<Request<IncomingBody>>>::Future {
        let work_thread = if command.def.consume_worker() {
            //See if we have a spare worker thread to dedicate to this work
            match self.0.workers.assign_worker() {
                Some(work_thread) => Some(work_thread),
                None => {
                    let response = MorkServerError::log_err(StatusCode::SERVICE_UNAVAILABLE, "Rejected Connection: Busy").error_response();
                    return Box::pin(async { Ok(response) })
                }
            }
        } else {
            None
        };

        //Acquire the resources (mainly zippers) to perform the operation
        let ctx = self.clone();
        Box::pin(async move {
            println!("Processing: cmd={}, args={:?}", command.def.name(), command.args); //GOAT Log this
            match command.def.work(ctx.clone(), command.clone(), work_thread, req).await {
                Ok(response_bytes) => {
                    Ok(ok_response(response_bytes))
                },
                Err(err) => {
                    let response = MorkServerError::cmd_err(err, &command).error_response();
                    Ok(response)
                }
            }
        })
    }
}

async fn got_cntl_c() {
    // Wait for the CTRL+C signal
    tokio::signal::ctrl_c()
        .await
        .expect("failed to install CTRL+C signal handler");
}

//GOAT, I don't know if it actually makes any sense for `MorkServerError` to be an object, since, we now
// create it and consume it in immediate succession, so perhaps the most sensible thing is to just turn
// `MorkServerError` into a set of functions.
//
/// Encapsulates an error that can be returned to the client, either immediately or eventually
#[derive(Debug)]
pub struct MorkServerError {
    /// The http status code to return to the client
    status_code: StatusCode,
}

impl MorkServerError {
    /// Creates a new MorkServerError and logs the error immediately to the logs
    #[inline]
    pub fn log_err<Desc: core::fmt::Display>(status_code: StatusCode, log_description: Desc) -> Self {
        println!("{}", log_description); //GOAT Log this
        Self {status_code}
    }
    /// Creates a new MorkServerError originating from a command, and logs the error immediately to the logs
    #[inline]
    pub fn cmd_err(cmd_err: CommandError, cmd: &Command) -> Self {
        match cmd_err {
            CommandError::Internal(err) => {
                Self::log_err(StatusCode::INTERNAL_SERVER_ERROR, format!("Error: \"{err}\" while executing command: {}", cmd.def.name()))
            },
            CommandError::External(err) => {
                Self::log_err(err.status_code, err.log_message)
            }
        }
    }
    /// Constructs a corresponding HTTP error response for the `MorkServerError`
    #[inline]
    pub fn error_response(&self) -> Response<BoxBody<Bytes, hyper::Error>> {
        error_response(self.status_code)
    }
}

/// Utility function to make an error response
fn error_response(status_code: StatusCode) -> Response<BoxBody<Bytes, hyper::Error>> {
    let response_body = Empty::<Bytes>::new()
        .map_err(|never| match never {})
        .boxed();
    let mut response = Response::new(response_body);
    *response.status_mut() = status_code;
    response
}
/// Utility function to make an "Ok 200" response body with the supplied text
fn ok_response<T: Into<Bytes>>(chunk: T) -> Response<BoxBody<Bytes, hyper::Error>> {
    let response_body = Full::new(chunk.into())
        .map_err(|never| match never {})
        .boxed();
    Response::new(response_body)
}

/// Returns and logs a "Bad Request"
fn bad_request_err(e: <MorkService as Service<Request<IncomingBody>>>::Error) -> <MorkService as Service<Request<IncomingBody>>>::Future {
    let response = MorkServerError::log_err(StatusCode::BAD_REQUEST, format!("Failed to parse request args: {e:?}")).error_response();
    Box::pin(async { Ok(response) })
}

/// If `result` is `Err`, then this macro returns the error from the parent function as a future.  Like
/// the '?' operator, but for situaitons where the calling function is not `async`
macro_rules! fut_err {
    ($result:expr, $err_func:ident) => {
        match $result {
            Ok(val) => val,
            Err(e) => return $err_func(e)
        }
    };
}

/// Parse a command from a request URI
fn parse_command<CmdDef: CommandDefinition>(space: &ServerSpace, remaining_path: &str, uri: &Uri, cmd_id: u64) -> Result<Command, BoxedErr> {
    let args = parse_path(space, remaining_path, CmdDef::args())?;
    let mut properties = Vec::with_capacity(CmdDef::properties().len());
    for prop_def in CmdDef::properties() {
        let prop = match parse_property(space, uri.query().unwrap_or(""), prop_def)? {
            Some(prop) => Some(prop),
            None => {
                if prop_def.required {
                    return Err(format!("missing `{}` parameter in query string", prop_def.name).into());
                } else {
                    None
                }
            }
        };
        properties.push(prop);
    }

    let command = Command { args, properties, def: CmdDef::CONST_CMD, cmd_id };
    Ok(command)
}

/// Parse command arguments separated by '/' in the request path
fn parse_path(space: &ServerSpace, in_str: &str, arg_types: &[ArgDef]) -> Result<Vec<ArgVal>, BoxedErr> {
    let mut remaining = in_str;
    let mut vals = Vec::with_capacity(arg_types.len());
    for (i, arg) in arg_types.iter().enumerate() {
        match arg.arg_type {
            ArgType::Expr => {
                let (expr_str, rem) = split_str(remaining)?;
                if expr_str.len() == 0 {
                    return Err(format!("missing argument `{}` at position {i}", arg.name).into())
                }
                remaining = rem;
                let expr = space.sexpr_to_expr(&expr_str)
                    .map_err(|e| BoxedErr::from(format!("Failed to parse expression: {e:?}")))?;
                vals.push(ArgVal::Expr(expr.into()));
            },
            ArgType::Flag => { unreachable!() }, //Flags only make sense as optional properties
            ArgType::Int => {
                let (val, rem) = split_int(remaining)?;
                remaining = rem;
                vals.push(ArgVal::Int(val));
            },
            ArgType::UInt => {
                let (val, rem) = split_uint(remaining)?;
                remaining = rem;
                vals.push(ArgVal::UInt(val));
            },
            ArgType::Path => {
                match split_bytes(remaining) {
                    Some((path, rem)) => {
                        remaining = rem;
                        vals.push(ArgVal::Path(path.to_vec()));
                    },
                    None => {
                        return Err(format!("missing argument `{}` at position {i}", arg.name).into())
                    }
                }
            },
            ArgType::String => {
                let (string, rem) = split_str(remaining)?;
                if string.len() == 0 {
                    return Err(format!("missing argument `{}` at position {i}", arg.name).into())
                }
                remaining = rem;
                vals.push(ArgVal::String(string.to_string()));
            },
        }
    }
    if remaining.len() == 0 {
        Ok(vals)
    } else {
        Err("additional unknown argument(s)".into())
    }
}

/// Splits the "command" as the first substring in a '/' separated argument path
fn split_command(in_str: &str) -> (&str, &str) {
    let in_str = if in_str.len() > 0 && in_str.as_bytes()[0] == b'/' {
        &in_str[1..]
    } else {
        ""
    };
    in_str.split_once('/').unwrap_or((in_str, ""))
}

/// Splits an integer as the next substring in a '/' separated argument path
fn split_int(in_str: &str) -> Result<(i64, &str), BoxedErr> {
    let (val_str, remaining) = in_str.split_once('/').unwrap_or((in_str, ""));
    i64::from_str_radix(val_str, 10)
        .map(|val| (val, remaining))
        .map_err(|e| Box::new(e) as BoxedErr)
}

/// Splits an unsized integer as the next substring in a '/' separated argument path
fn split_uint(in_str: &str) -> Result<(u64, &str), BoxedErr> {
    let (val, remaining) = split_int(in_str)?;
    if val >= 0 {
        Ok((val as u64, remaining))
    } else {
        Err("arg must be positive".into())
    }
}

/// Splits a buffer of bytes as the next substring in a '/' separated argument path
fn split_bytes(in_str: &str) -> Option<(Cow<'_, [u8]>, &str)> {
    let (val_str, remaining) = in_str.split_once('/').unwrap_or((in_str, ""));
    let bytes = urlencoding::decode_binary(val_str.as_bytes());
    if bytes.len() == 0 && !in_str.contains('/') {
        return None
    }
    Some((bytes, remaining))
}

/// Splits the next substring in a '/' separated argument path
fn split_str(in_str: &str) -> Result<(Cow<'_, str>, &str), BoxedErr> {
    let (val_str, remaining) = in_str.split_once('/').unwrap_or((in_str, ""));
    Ok((urlencoding::decode(val_str)?, remaining))
}

/// Extracts `key` from a URI query string formatted as `key=value&key2=value2`, but does not
/// attempt to undo percent encoding
fn get_query_key_raw<'a>(in_str: &'a str, key: &str) -> Option<&'a str> {
    if let Some((_before_key, after_key)) = in_str.split_once(key) {
        if after_key.len() > 0 {
            if after_key.as_bytes()[0] == b'=' {
                let after_key = &after_key[1..];
                let (val_str, _) = after_key.split_once('&').unwrap_or((after_key, ""));
                return Some(val_str)
            }
        } else {
            return Some("")
        }
    }
    None
}

/// Checks `key` in a URI query string, returning `ArgVal::Flag` if it's there
fn get_query_key_flag<'a>(in_str: &'a str, key: &str) -> Option<ArgVal> {
    match get_query_key_raw(in_str, key) {
        Some(query_str) => {
            //QUESTION, do we want to allow "flag=yes" or "flag=no"?
            //Right now, we just go by the absence of presence of "flag"
            debug_assert_eq!(query_str, "");
            Some(ArgVal::Flag)
        },
        None => None
    }
}

/// Extracts `key` from a URI query string formatted as `key=value&key2=value2`
fn get_query_key_bytes<'a>(in_str: &'a str, key: &str) -> Result<Option<Cow<'a, [u8]>>, BoxedErr> {
    match get_query_key_raw(in_str, key) {
        Some(val_str) => {
            if val_str.len() > 0 {
                Ok(Some(urlencoding::decode_binary(val_str.as_bytes())))
            } else {
                Ok(None)
            }
        },
        None => Ok(None)
    }
}

/// Extracts `key` from a URI query string formatted as `key=value&key2=value2`
fn get_query_key_str<'a>(in_str: &'a str, key: &str) -> Result<Option<Cow<'a, str>>, BoxedErr> {
    match get_query_key_raw(in_str, key) {
        Some(val_str) => {
            if val_str.len() > 0 {
                urlencoding::decode(val_str)
                    .map(|the_str| Some(the_str))
                    .map_err(|decode_err| BoxedErr::from(format!("Failed to decode string in {key}: {decode_err:?}")))
            } else {
                Ok(None)
            }
        },
        None => Ok(None)
    }
}

/// Extracts `key` from a URI query string formatted as `key=value&key2=value2`
fn get_query_key_expr<'a>(space: &ServerSpace, in_str: &'a str, key: &str) -> Result<Option<OwnedExpr>, BoxedErr> {
    match get_query_key_str(in_str, key)? {
        Some(expr_str) => {
            space.sexpr_to_expr(&expr_str)
                .map(|expr| Some(expr))
                .map_err(|e| BoxedErr::from(format!("Failed to parse expression '{key}': {e:?}")))
        },
        None => Ok(None)
    }
}

/// Parses a single property out of a query string.  Does not respect `PropDef::required == false`
fn parse_property(space: &ServerSpace, in_str: &str, prop_def: &PropDef) -> Result<Option<ArgVal>, BoxedErr> {
    match prop_def.arg_type {
        ArgType::Flag => Ok(get_query_key_flag(in_str, prop_def.name)),
        ArgType::Int |
        ArgType::UInt => { unimplemented!() },
        ArgType::Path => Ok(get_query_key_bytes(in_str, prop_def.name)?.map(|val| ArgVal::Path(val.to_vec()))),
        ArgType::Expr => Ok(get_query_key_expr(space, in_str, prop_def.name)?.map(|expr| ArgVal::Expr(expr))),
        ArgType::String => Ok(get_query_key_str(in_str, prop_def.name)?.map(|val| ArgVal::String(val.to_string()))),
    }
}

impl Service<Request<IncomingBody>> for MorkService {
    type Response = Response<BoxBody<Bytes, hyper::Error>>;
    type Error = BoxedErr;
    type Future = Pin<Box<dyn Future<Output = Result<Self::Response, Self::Error>> + Send>>;

    fn call(&self, req: Request<IncomingBody>) -> Self::Future {

        //Get a new connection_id for the request
        let cmd_id = self.0.request_counter.fetch_add(1, std::sync::atomic::Ordering::Relaxed);

        //Decode the request
        let (command_name, remaining) = split_command(req.uri().path());

        // NOTE ! this macro is making use of lexical scope!
        macro_rules! dispatch {
            ($(| $METHOD:tt => $CMD:ty)*) => {
                match (req.method(), command_name) {$(
                    (&Method::$METHOD, <$CMD>::NAME) => {
                        let command = fut_err!((|| {
                            parse_command::<$CMD>(&self.0.space, remaining, req.uri(), cmd_id)
                        })(), bad_request_err);
                        self.dispatch_work(command, req)
                    },
                )*
                    // Return 404 Not Found for other routes.
                    _ => {
                        let response = MorkServerError::log_err(StatusCode::NOT_FOUND, format!("Unknown URL: {}", req.uri().path())).error_response();
                        return Box::pin(async { Ok(response) })
                    }
                }
            };
        }
        #[cfg(not(feature="neo4j"))]
        dispatch!{
            | GET => BusywaitCmd
            | GET => ClearCmd
            | GET => CopyCmd
            | GET => CountCmd
            | GET => ExploreCmd
            | GET => ExportCmd
            | GET => ImportCmd
            | GET => StatusCmd
            | GET => StopCmd
            | POST => UploadCmd
            | GET => TransformCmd


            | GET => MettaThreadCmd
            | GET => MettaThreadSuspendCmd
            | POST => TransformMultiMultiCmd
        }
        #[cfg(feature="neo4j")]
        dispatch!{
            | GET => BusywaitCmd
            | GET => ClearCmd
            | GET => CopyCmd
            | GET => CountCmd
            | GET => ExploreCmd
            | GET => ExportCmd
            | GET => ImportCmd
            | GET => StatusCmd
            | GET => StopCmd
            | POST => UploadCmd
            | GET => TransformCmd
            // neo4j
            | GET => LoadNeo4jTriplesCmd
            | GET => LoadNeo4jNodePropertiesCmd
            | GET => LoadNeo4jNodeLabelsCmd


            | GET => MettaThreadCmd
            | GET => MettaThreadSuspendCmd
            | POST => TransformMultiMultiCmd
        }
    }
}

#[cfg(feature = "tokio_workers")]
mod worker_pool {
    use std::sync::{atomic::AtomicU64, Arc};
    use super::{BoxedErr, Command};

    pub struct WorkerPool {
        thread_count: usize,
        /// We'll use the Arc's strong_count to keep track of the number of threds in use.  Since the
        /// `Arc` inside `WorkThreadHandle` is private and `WorkThreadHandle` is `!Clone`, we can use
        /// this as an atomic counter
        thread_counter: Arc<()>,
        job_counter: AtomicU64,
    }

    #[allow(dead_code)] //The inner Arc is just to keep an atomic count so we don't ever access it
    pub struct WorkThreadHandle(Arc<()>);

    impl WorkThreadHandle {
        /// Dispatches a blocking task to the work thread, to complete in the background
        pub async fn dispatch_blocking_task<F>(self, cmd: Command, task: F)
            where F: FnOnce(Command) -> Result<(), BoxedErr> + 'static + Send
        {
            //Spin off a thread to do the work
            tokio::task::spawn_blocking(move || {
                match task(cmd.clone()) {
                    Ok(()) => {
                        println!("Successful completion: cmd={}", cmd.def.name()); //GOAT Log this sucessful completion
                    },
                    Err(e) => {
                        println!("Command encountered error: cmd={} err={}", cmd.def.name(), e); //GOAT Log this error
                    }
                }

                // **VERY** important that the closure captures the Arc in self, otherwise it will be
                // dropped, and the thread will appear available
                let _ = Arc::strong_count(&self.0);
            });
        }
        /// Consumes the work thread ensuring it has a chance to complete
        pub async fn finalize(self)
        {
            let _ = Arc::strong_count(&self.0);
        }
    }

    impl WorkerPool {
        pub fn new() -> Self {
            // We want to reserve one OS thread for dealing with the responses and the watchdog
            let thread_count = tokio::runtime::Handle::current().metrics().num_workers() - 1;
            assert!(thread_count >= 1);

            Self {
                thread_count,
                thread_counter: Arc::new(()),
                job_counter: AtomicU64::new(0),
            }
        }
        /// Returns the total number of worker threads
        pub fn thread_count(&self) -> usize {
            self.thread_count
        }
        /// Returns the number of available workers at the point in time when it is called
        pub fn available_workers(&self) -> usize {
            self.thread_count + 1 - Arc::strong_count(&self.thread_counter)
        }
        /// Returns `Some` if a worker is available, otherwise returns `None`
        pub fn assign_worker(&self) -> Option<WorkThreadHandle> {
            self.job_counter.fetch_add(1, std::sync::atomic::Ordering::Relaxed);

            //ATOMICITY NOTE: by doing the clone first and then the check, we could end up in a situation
            // where two tasks attempt to get the last worker, do this clone, and both see too many threads
            // are taken so fail.  I.e there is a small chance we report busy when there was one thread
            // available.  There is no chance, however, that more threads are given out than are allowed.
            let new_arc = self.thread_counter.clone();
            //Note: +2 = +1 for the Arc in the pool, and +1 for le vs lt
            if Arc::strong_count(&new_arc) < self.thread_count+2 {
                Some(WorkThreadHandle(new_arc))
            } else {
                None
            }
        }
        //GOAT, now dropping the worker is all that's needed
        // /// Puts the worker thread back into the pool, ready to accept new work
        // pub fn replace_worker(&self, _thread: WorkThreadHandle) {
        //     //Dropping the `WorkThreadHandle` is all that's needed
        // }

        /// Returns as soon as there are no outstanting worker threads
        ///
        /// NOTE: this polling loop is a little cheezy, should probably do a cond_var or something
        pub async fn wait_for_worker_completion(&self) {
            while !self.is_idle() {
                tokio::time::sleep(core::time::Duration::from_millis(5)).await;
            }
        }

        /// Returns `true` if no work is currently in progress on any worker threads
        pub fn is_idle(&self) -> bool {
            self.available_workers() == self.thread_count
        }

        /// Returns the monotonically incrementing job counter for the worker pool
        pub fn job_counter(&self) -> u64 {
            self.job_counter.load(std::sync::atomic::Ordering::Relaxed)
        }
    }
}

#[cfg(feature = "tokio_workers")]
use worker_pool::*;

#[cfg(feature = "mork_workers")]
struct WorkerPool {
    thread_count: usize,
    threads: scc::Stack<()>,
}

#[cfg(feature = "mork_workers")]
type WorkThreadHandle = ();

#[cfg(feature = "mork_workers")]
impl WorkerPool {
    fn new() -> Self {
        // Keep one core free to handle all the async stuff
        let thread_count = num_cpus::get() - 1;
        assert!(thread_count >= 1);

        // Spin up the worker threads
        let threads = scc::Stack::default();
        for _i in 0..thread_count {
            //GOAT, actually start them them

            threads.push(());
        }

        Self {
            thread_count,
            threads
        }
    }
    #[allow(dead_code)]
    fn available_workers(&self) -> usize {
        self.threads.len()
    }
    fn assign_worker(&self) -> Option<WorkThreadHandle> {
        self.threads.pop().map(|_| ())
    }
    fn replace_worker(&self, _thread: WorkThreadHandle) {
        self.threads.push(());
    }
}

//GOAT, Use a "current_thread" runtime if we want a different thread pool for doing the actual work, and
// the multi_thread runtime for the tokio threads option
#[tokio::main(flavor = "multi_thread")]
// #[tokio::main(flavor = "current_thread")]
async fn main() -> Result<(), Box<dyn std::error::Error + Send + Sync>> {

    //Init the Mork network service
    let service = MorkService::new().await;

    //Run the Mork service
    service.run(server_addr()).await?;

    Ok(())
}

//GOAT
// merge import and fetch
//   property to specify fmt
//   support file:// URLs
//