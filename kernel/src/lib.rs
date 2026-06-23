#![feature(gen_blocks)]
#![feature(coroutine_trait)]
#![feature(coroutines)]
#![feature(stmt_expr_attributes)]
#![feature(more_float_constants)]

pub mod space;
mod sources;
mod sinks;
mod pure;
pub mod term_identity;
pub mod binding_env;
pub mod pattern_relations;
pub mod arrangements;
pub mod binding_space;
pub mod binding_plan;

#[cfg(test)]
mod test_sidecar_queries;

#[doc(hidden)]
pub use mork_expr as __mork_expr;
