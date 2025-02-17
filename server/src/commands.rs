
use core::any::Any;
use core::pin::Pin;
use std::future::Future;
use std::io::{Write, BufWriter};
use std::path::PathBuf;

use hyper::StatusCode;

use pathmap::zipper::ZipperCreation;

use super::{BoxedErr, MorkService, WorkThreadHandle};

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
    async fn gather(_ctx: MorkService, _cmd: Command) -> Result<Option<Resources>, CommandError> {
        Ok(None)
    }
    async fn work(_ctx: MorkService, thread: Option<WorkThreadHandle>, cmd: Command, _resources: Option<Resources>) -> Result<(), CommandError> {
        thread.unwrap().dispatch_blocking_task(cmd, move |cmd| {
            let millis = cmd.args[0].as_u64();
            std::thread::sleep(std::time::Duration::from_millis(millis));
            Ok(())
        }).await;
        Ok(())
    }
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
            name: "map_path",
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
    async fn gather(ctx: MorkService, cmd: Command) -> Result<Option<Resources>, CommandError> {
        let file_uri = cmd.properties[0].as_ref().unwrap().as_str();
        let file_path = ctx.0.resource_store.new_path_for_resource(file_uri).await?;

        let map_path = cmd.args[0].as_path();
        //GOAT, come back here
        // ctx.0.zipper_head.write_zipper_at_exclusive_path(map_path)
        //     .map(|zipper| Some(Box::new(zipper) as Resources))
        //     .map_err(|err| err.into())
        // Err("goat".into())

        Ok(Some(Box::new(file_path)))
    }
    async fn work(ctx: MorkService, _thread: Option<WorkThreadHandle>, cmd: Command, resources: Option<Resources>) -> Result<(), CommandError> {

        //QUESTION: Should we let the fetch run for a small amount of time (like 300ms) to see if
        // it fails straight away, so we can report that failure immediately?
        //My thinking is no, because the caller needs to write code to handle the case when the
        // fetch takes too long.  So it we always return success, and then caller has one fewer
        // case to worry about.

        //Spin off a task to handle the download
        tokio::task::spawn(async move {
            let file_uri = cmd.properties[0].as_ref().unwrap().as_str();
            let local_file_path = resources.unwrap().downcast::<PathBuf>().unwrap();

            let mut response = ctx.0.http_client.get(&*file_uri).send().await.unwrap(); //GOAT NO UNWRAP!!
            if response.status().is_success() {

                let mut writer = BufWriter::new(std::fs::File::create(&*local_file_path).unwrap());//GOAT NO UNWRAP!!

                while let Some(chunk) = response.chunk().await.unwrap() {//GOAT NO UNWRAP!!
                    writer.write(&*chunk).unwrap();//GOAT NO UNWRAP!!
                }

                println!("Successful download: file saved to '{:?}'", local_file_path); //GOAT Log this sucessful completion

            } else {
                //GOAT, Update the status map
                // println!("Failed to load remote resource: {}", response.status());
            }
        });

        Ok(())
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
        &[]
    }
    async fn gather(_ctx: MorkService, _cmd: Command) -> Result<Option<Resources>, CommandError> {
        Ok(None)
    }
    async fn work(ctx: MorkService, _thread: Option<WorkThreadHandle>, _cmd: Command, _resources: Option<Resources>) -> Result<(), CommandError> {
        ctx.0.stop_cmd.notify_waiters();
        Ok(())
    }
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

/// An abstract type to contain the resources needed to execute the command
pub type Resources = Box<dyn Any + Send + Sync>;

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
    fn gather(ctx: MorkService, cmd: Command) -> impl Future<Output=Result<Option<Resources>, CommandError>> + Sync + Send;

    /// Method to perform the execution.  If anything CPU-intensive is done in this method,
    /// it should call `dispatch_blocking_task` for that work
    fn work(ctx: MorkService, thread: Option<WorkThreadHandle>, cmd: Command, resources: Option<Resources>) -> impl Future<Output=Result<(), CommandError>> + Sync + Send;
}

/// Object-safe wrapper over CommandDefinition
pub trait CmdDefObject: 'static + Send + Sync {
    fn name(&self) -> &'static str;
    fn consume_worker(&self) -> bool;
    // fn args(&self) -> &'static [ArgDef];
    // fn properties(&self) -> &'static [PropDef];
    fn gather(&self, ctx: MorkService, cmd: Command) -> Pin<Box<dyn Future<Output=Result<Option<Resources>, CommandError>> + Sync + Send>>;
    fn work(&self, ctx: MorkService, thread: Option<WorkThreadHandle>, cmd: Command, resources: Option<Resources>) -> Pin<Box<dyn Future<Output=Result<(), CommandError>> + Sync + Send>>;
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
    fn gather(&self, ctx: MorkService, cmd: Command) -> Pin<Box<dyn Future<Output=Result<Option<Resources>, CommandError>> + Sync + Send>> {
        Box::pin(Self::gather(ctx, cmd))
    }
    fn work(&self, ctx: MorkService, thread: Option<WorkThreadHandle>, cmd: Command, resources: Option<Resources>) -> Pin<Box<dyn Future<Output=Result<(), CommandError>> + Sync + Send>> {
        Box::pin(Self::work(ctx, thread, cmd, resources))
    }
}

/// An invocation of a command, that can be (or has been) executed by the server
#[derive(Clone)]
pub struct Command {
    pub def: &'static dyn CmdDefObject,
    pub args: Vec<ArgVal>,
    pub properties: Vec<Option<ArgVal>>
}

/// An error type that can be returned from a command
#[derive(Debug)]
pub enum CommandError {
    /// An internal server error that is not the result of a client action
    Internal(BoxedErr),
    /// An error originating from an action done by the client
    External(ExternalError)
}

#[derive(Debug)]
pub struct ExternalError {
    pub(crate) log_message: String,
    pub(crate) status_code: StatusCode,
}

impl CommandError {
    pub fn internal<Desc: Into<Box<dyn core::error::Error + Send + Sync>>>(desc: Desc) -> Self {
        Self::Internal(desc.into())
    }
    pub fn external<M: Into<String>>(status_code: StatusCode, log_message: M) -> Self {
        Self::External(ExternalError{ status_code, log_message: log_message.into() })
    }
}

impl<E: core::error::Error + Send + Sync + 'static> From<E> for CommandError {
    fn from(err: E) -> Self {
        Self::Internal(Box::new(err))
    }
}

#[derive(Clone, Copy, Debug)]
pub enum ArgType {
    Int, UInt, Path, String
}

#[derive(Clone, Debug, Default)]
pub enum ArgVal {
    #[default]
    None,
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
