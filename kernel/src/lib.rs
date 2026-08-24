#![feature(gen_blocks)]
#![feature(coroutine_trait)]
#![feature(coroutines)]
#![feature(stmt_expr_attributes)]
#![feature(more_float_constants)]

pub mod space;
/// Choosing which conjunct of a body to descend first. Compiled only under the
/// `conjunct_order` feature, which is also what routes the space-to-space transform through it.
#[cfg(feature = "conjunct_order")]
pub mod conjunct_order;
/// The worst-case-optimal leapfrog join. The `leapfrog` feature routes conjunctive bodies to
/// it; without the feature the engine is unchanged. The module also carries the body
/// decomposition and the trie subterm cursor that `conjunct_order` costs an order with, so it
/// compiles whenever either feature asks for it.
#[cfg(any(feature = "leapfrog", feature = "conjunct_order"))]
pub mod leapfrog;
mod sources;
mod sinks;
mod pure;

pub use sinks::WriteResourceRequest;
pub use sources::ResourceRequest;
