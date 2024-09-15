use std::fs::File;
use std::io::Read;
use std::{io, ptr};

use std::fmt::format;
use std::ptr::slice_from_raw_parts;
use std::str::Utf8Error;

use mork_bytestring::{Expr, ExprZipper, Tag, item_byte, byte_item};


fn indexOf<A : Eq>(s: &Vec<A>, e: &A) -> i64 {
  let mut i = 0;
  for e_ in s {
    if e.eq(e_) { return i }
    else { i += 1 }
  }
  return -1
}

fn isWhitespace(c: char) -> bool {
  c == ' ' || c == '\t' || c == '\n'
}

fn isDigit(c: char) -> bool {
  c == '0' || c == '1' || c == '2' || c == '3' || c == '4' ||
  c == '5' || c == '6' || c == '7' || c == '8' || c == '9'
}

pub struct BufferedIterator<R : Read> {
  pub file: R,
  pub buffer: [u8; 4096],
  pub cursor: usize,
  pub max: usize
}

impl <R : Read> BufferedIterator<R> {
  pub fn new(r: R) -> Self {
    BufferedIterator{ file: r, buffer: [0; 4096], cursor: 4096, max: 4096 }
  }

  fn peek(&mut self) -> std::io::Result<u8> {
    if self.cursor == self.max {
      self.max = self.file.read(&mut self.buffer)?;
      self.cursor = 0;
      Ok(self.buffer[0])
    } else {
      Ok(self.buffer[self.cursor])
    }
  }

  fn next(&mut self) -> std::io::Result<u8> {
    if self.cursor == self.max {
      self.max = self.file.read(&mut self.buffer)?;
      self.cursor = 0;
      Ok(self.buffer[0])
    } else {
      let r = self.buffer[self.cursor];
      self.cursor += 1;
      Ok(r)
    }
  }

  fn hasNext(&mut self) -> std::io::Result<bool> {
    if self.cursor != self.max {
      return Ok(true)
    } else {
      self.max = self.file.read(&mut self.buffer)?;
      self.cursor = 0;
      Ok(self.max > 0)
    }
  }
}

#[derive(Debug)]
pub enum ParserError {
  ReadError(std::io::Error),
  InputFinished(),
  NotArity(),
  UnexpectedRightBracket(),
  UnfinishedEscapeSequence()
}


pub trait Parser {
  fn tokenizer(&mut self, s: String) -> Vec<u8> { return s.as_bytes().to_vec() }

  fn sexprUnsafe<R : Read>(&mut self, it: &mut BufferedIterator<R>, variables: &mut Vec<String>, target: &mut ExprZipper) -> Result<(), ParserError> {
    use ParserError::*;
    while it.hasNext().map_err(ReadError)? {
      match it.peek().map_err(ReadError)? as char {
        ';' => { while it.next().map_err(ReadError)? != '\n' as u8 {} }
        c if isWhitespace(c) => { it.next().map_err(ReadError)?; }
        '$' => {
          let id = {
            let mut sb = "".to_string();
            let mut cont = true;
            while it.hasNext().map_err(ReadError)? && cont {
              match it.peek().map_err(ReadError)? as char {
                '(' | ')' => { cont = false }
                c if isWhitespace(c) => { cont = false }
                c => {
                  sb.push(c);
                  it.next().map_err(ReadError)?;
                }
              }
            }
            sb
          };
          let ind = indexOf(variables, &id);
          if ind == -1 {
            variables.push(id);
            target.write_new_var();
            target.loc += 1;
            return Ok(());
          } else {
            target.write_var_ref(ind as u8);
            target.loc += 1;
            return Ok(());
          }
        }
        '(' => { return {
          let arity_loc = target.loc;
          target.write_arity(0);
          target.loc += 1;
          it.next().map_err(ReadError)?;
          while it.peek().map_err(ReadError)? != ')' as u8 {
            match it.peek().map_err(ReadError)? as char {
              c if isWhitespace(c) => { it.next().map_err(ReadError)?; }
              _ => {
                self.sexprUnsafe(it, variables, target);
                unsafe {
                  let p = target.root.ptr.byte_add(arity_loc);
                  if let Tag::Arity(a) = byte_item(*p) {
                    *p = item_byte(Tag::Arity(a + 1));
                  } else { return Err(NotArity()) }
                }
              }
            }
          }
          it.next();
          Ok(())
        } }
        ')' => { return Err(UnexpectedRightBracket()) }
        _ => {
          let e = self.tokenizer({
            if it.hasNext().map_err(ReadError)? && it.peek().map_err(ReadError)? == '"' as u8 {
              {
                let mut sb = "".to_string();
                let mut cont = true;
                it.next().map_err(ReadError)?;
                sb.push('"');
                while it.hasNext().map_err(ReadError)? && cont {
                  match it.next().map_err(ReadError)? as char {
                    '"' => {
                      sb.push('"');
                      cont = false
                    }
                    '\\' => {
                      if it.hasNext().map_err(ReadError)? { sb.push(it.next().map_err(ReadError)? as char) }
                      else { return Err(UnfinishedEscapeSequence()) }
                    }
                    c => { sb.push(c) }
                  }
                }
                sb
              }
            } else {
              {
                let mut sb = "".to_string();
                let mut cont = true;
                while it.hasNext().map_err(ReadError)? && cont {
                  match it.peek().map_err(ReadError)? as char {
                    '(' | ')' => { cont = false }
                    c if isWhitespace(c) => { cont = false }
                    c => {
                      sb.push(c);
                      it.next().map_err(ReadError)?;
                    }
                  }
                }
                sb
              }
            }
          });
          target.write_symbol(&e[..]);
          target.loc += 1 + e.len();
          return Ok(());
        }
      }
    }
    Err(InputFinished())
  }
}
