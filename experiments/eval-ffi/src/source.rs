use mork_expr::{byte_item, Tag};

use crate::EvalError;

pub enum SourceItem<'a> {
    Tag(Tag),
    Symbol(&'a[u8]),
}

#[derive(Clone)]
#[repr(C)]
pub struct ExprSource {
    ptr: *const u8,
    // len: usize,
    position: usize,
}

#[cfg(feature = "std")]
use alloc::string::String;

impl ExprSource {
    #[cfg(feature = "std")]
    pub fn print(&self) -> String {
        use alloc::vec::Vec;
        use core::fmt::Write;
        let mut rv = String::new();
        let mut length = Vec::new();
        length.push(1);
        let mut pos = 0;
        while let Some(len) = length.last_mut() {
            if *len == 0 {
                length.pop();
                if !length.is_empty() {
                    rv.push(')');
                }
                continue;
            }
            *len -= 1;
            let is_last = *len == 0;

            let byte = unsafe { *self.ptr.add(pos) };
            pos += 1;
            let tag = byte_item(byte);
            match tag {
                Tag::SymbolSize(len) => {
                    let symbol = unsafe { core::slice::from_raw_parts(self.ptr.add(pos), len as usize) };
                    let s = if symbol.iter().any(|&b| b.is_ascii_graphic()) {
                        core::str::from_utf8(symbol).ok()
                    } else {
                        None
                    };
                    if let Some(s) = s {
                        write!(&mut rv, "\"{}\"", s).unwrap();
                    } else {
                        write!(&mut rv, "{:?}", symbol).unwrap();
                    }
                    pos += len as usize;
                }
                Tag::Arity(arity) => {
                    rv.push('(');
                    length.push(arity as usize);
                }
                Tag::NewVar => {
                    rv.push('$');
                }
                Tag::VarRef(n) => {
                    write!(&mut rv, "${}", n).unwrap();
                }
            }
            if !is_last {
                rv.push(' ');
            }
        }
        rv
    }
    pub fn new(ptr: *const u8) -> Self {
        // let len = vec.len();
        Self { ptr, position: 0 }
    }
    pub fn read(&mut self) -> SourceItem {
        let byte = unsafe { *self.ptr.add(self.position) };
        self.position += 1;
        let tag = byte_item(byte);
        match tag {
            Tag::SymbolSize(len) => {
                let slice = unsafe { core::slice::from_raw_parts(self.ptr.add(self.position), len as usize) };
                self.position += len as usize;
                SourceItem::Symbol(slice)
            }
            _ => SourceItem::Tag(tag),
        }
    }
    /// Consumes head of a list, returning (number of remaining items, head symbol)
    pub fn consume_head(&mut self) -> Result<(usize, &[u8]), EvalError> {
        let mut items;
        match self.read() {
            SourceItem::Tag(Tag::Arity(arity)) => {
                items = arity as usize;
            }
            _ => return Err(EvalError::from("not a list2")),
        }
        let head;
        match self.read() {
            SourceItem::Symbol(slice) => {
                head = slice;
                items -= 1;
            }
            _ => return Err(EvalError::from("head is not a symbol")),
        }
        Ok((items, head))
    }

    /// Consumes head of a list, checking that the head symbol matches the provided one.
    pub fn consume_head_check(&mut self, symbol: &[u8]) -> Result<usize, EvalError> {
        let mut expr2 = self.clone();
        let (items, head) = expr2.consume_head()?;
        if head != symbol {
            return Err(EvalError::from("incorrect head symbol provided"));
        }
        *self = expr2;
        Ok(items)
    }

    /// Consumes an i32 symbol from the expression.
    pub fn consume_i32(&mut self) -> Result<i32, EvalError> {
        let array;
        const SIZE: usize = core::mem::size_of::<i32>();
        match self.read() {
            SourceItem::Symbol(slice) if slice.len() == SIZE => {
                array = unsafe { slice.as_ptr().cast::<[u8; SIZE]>().read() };
            }
            SourceItem::Symbol(slice) => {
                return Err(EvalError::from("invalid symbol size of i32"));
            }
            _ => return Err(EvalError::from("trying to read i32 from not a symbol"))
        }
        Ok(i32::from_be_bytes(array))
    }
}
