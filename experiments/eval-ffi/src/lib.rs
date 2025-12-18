#![no_std]

#[cfg(feature = "std")]
extern crate alloc;

pub mod sink;
pub mod source;

pub use sink::{ExprSink, SinkItem};
pub use source::{ExprSource, SourceItem};
pub use mork_expr::Tag;

pub type FuncPtr = extern "C" fn(*mut ExprSource, *mut ExprSink) -> Result<(), EvalError>;

#[derive(Debug)]
pub enum EvalError {
    NotEnoughSpace,
    Msg { ptr: *const u8, len: usize },
}

impl core::fmt::Display for EvalError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            EvalError::NotEnoughSpace => write!(f, "EvalError: not enough space"),
            EvalError::Msg { ptr, len } => {
                let msg = unsafe { core::slice::from_raw_parts(*ptr, *len) };
                write!(f, "EvalError: {:?}", core::str::from_utf8(msg))
            }
        }
    }
}

impl core::convert::From<&'static str> for EvalError {
    fn from(s: &'static str) -> Self {
        EvalError::Msg { ptr: s.as_ptr(), len: s.len() }
    }
}

impl core::error::Error for EvalError {}
