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
#[doc(hidden)]
pub use mork_expr as __mork_expr;
#[doc(hidden)]
pub use mork_frontend as __mork_frontend;

pub mod prefix {
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    pub struct Prefix<'a> {
        pub slice: &'a [u8],
    }

    impl<'a> Prefix<'a> {
        pub fn path(&self) -> &'a [u8] {
            self.slice
        }
    }
}
