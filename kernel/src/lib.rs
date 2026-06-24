#![feature(gen_blocks)]
#![feature(coroutine_trait)]
#![feature(coroutines)]
#![feature(stmt_expr_attributes)]
#![feature(more_float_constants)]

pub mod space;
mod sources;
mod sinks;
mod pure;

pub use sinks::WriteResourceRequest;
pub use sources::ResourceRequest;
#[cfg(feature = "einsum")]
pub mod graph_tensor;
pub mod term_identity;

#[doc(hidden)]
pub use mork_expr as __mork_expr;
