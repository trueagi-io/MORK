#![feature(gen_blocks)]
#![feature(coroutine_trait)]
#![feature(coroutines)]
#![feature(stmt_expr_attributes)]
#![feature(more_float_constants)]

pub mod space;
pub mod shard_zipper;
mod sources;
mod sinks;
mod pure;

pub use sinks::WriteResourceRequest;
pub use sources::ResourceRequest;
