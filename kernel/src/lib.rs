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
pub use sinks::{
    wasm_linear_memory_policy, WasmLinearMemoryPolicy, WASM_LINEAR_MEMORY_GUARD_BYTES,
    WASM_LINEAR_MEMORY_RESERVATION_BYTES,
};
