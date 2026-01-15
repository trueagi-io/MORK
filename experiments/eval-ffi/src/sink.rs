use mork_expr::{Tag, item_byte, SourceItem};

#[repr(C)]
pub struct ExprSink {
    ptr: *mut u8,
    len: usize,
    capacity: usize,
}
impl Default for ExprSink {
    fn default() -> Self {
        Self { ptr: core::ptr::null_mut(), len: 0, capacity: 0}
    }
}

#[cfg(feature = "std")]
use alloc::vec::Vec;

impl ExprSink {
    pub fn expr(&self) -> mork_expr::Expr {
        mork_expr::Expr{ ptr: self.ptr }
    }
    #[cfg(feature = "std")]
    pub fn new(vec: Vec<u8>) -> Self {
        // let (ptr, len, capacity) = vec.into_raw_parts();
        let (ptr, len, capacity) = (vec.as_ptr() as *mut u8, vec.len(), vec.capacity());
        core::mem::forget(vec);
        Self { ptr, len, capacity }
    }
    #[cfg(feature = "std")]
    pub fn with_capacity(capacity: usize) -> Self {
        Self::new(Vec::with_capacity(capacity))
    }
    #[cfg(feature = "std")]
    pub fn finish(self) -> Vec<u8> {
        unsafe { Vec::from_raw_parts(self.ptr, self.len, self.capacity) }
    }
    fn push(&mut self, byte: u8) -> Result<(), crate::EvalError> {
        if self.len >= self.capacity {
            return Err(crate::EvalError::NotEnoughSpace);
        }
        unsafe {
            *self.ptr.add(self.len) = byte;
        }
        self.len += 1;
        Ok(())
    }
    pub fn extend_from_slice(&mut self, slice: &[u8]) -> Result<(), crate::EvalError> {
        if self.len + slice.len() > self.capacity {
            return Err(crate::EvalError::NotEnoughSpace);
        }
        unsafe {
            core::ptr::copy_nonoverlapping(slice.as_ptr(), self.ptr.add(self.len), slice.len());
        }
        self.len += slice.len();
        Ok(())
    }
    pub fn write(&mut self, item: SourceItem) -> Result<(), crate::EvalError> {
        match item {
            SourceItem::Tag(Tag::SymbolSize(_)) => {
                panic!("sink uses WriteSymbol for symbols, gotten Tag::SymbolSize")
            }
            SourceItem::Tag(tag) => {
                self.push(item_byte(tag))?;
            }
            SourceItem::Symbol(slice) => {
                debug_assert!(slice.len() < 64);
                self.push(item_byte(Tag::SymbolSize(slice.len() as _)))?;
                self.extend_from_slice(slice)?;
            }
        }
        Ok(())
    }
}

impl core::convert::AsRef<[u8]> for ExprSink {
    fn as_ref(&self) -> &[u8] {
        unsafe { core::slice::from_raw_parts(self.ptr, self.len) }
    }
}

impl core::convert::AsMut<[u8]> for ExprSink {
    fn as_mut(&mut self) -> &mut [u8] {
        unsafe { core::slice::from_raw_parts_mut(self.ptr, self.len) }
    }
}
