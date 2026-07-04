#![feature(gen_blocks)]
#![feature(coroutine_trait)]
#![feature(coroutines)]
#![feature(stmt_expr_attributes)]
#![feature(more_float_constants)]

#[cfg(feature = "pathspace_oracles")]
pub mod path_space_ops;
pub mod space;
mod sources;
mod sinks;
mod pure;

pub use sinks::WriteResourceRequest;
pub use sources::ResourceRequest;
