use std::fs::File;
use std::io::Read;
use std::ptr;

use std::fmt::format;
use std::ptr::slice_from_raw_parts;
use std::str::Utf8Error;

use mork_bytestring::{Expr, ExprZipper, Tag, item_byte, byte_item};


fn indexOf(s: &Vec<String>, e: &String) -> i64 {
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

pub struct BufferedIterator {
  pub file: File,
  pub buffer: [u8; 4096],
  pub cursor: usize,
  pub max: usize
}

impl BufferedIterator {
  fn head(&mut self) -> u8 {
    if self.cursor == self.max {
      self.max = self.file.read(&mut self.buffer).unwrap();
      self.cursor = 0;
      self.buffer[0]
    } else {
      self.buffer[self.cursor]
    }
  }

  fn next(&mut self) -> u8 {
    if self.cursor == self.max {
      self.max = self.file.read(&mut self.buffer).unwrap();
      self.cursor = 0;
      self.buffer[0]
    } else {
      let r = self.buffer[self.cursor];
      self.cursor += 1;
      r
    }
  }

  fn hasNext(&mut self) -> bool {
    if self.cursor != self.max {
      return true
    } else {
      self.max = self.file.read(&mut self.buffer).unwrap();
      self.cursor = 0;
      self.max > 0
    }
  }
}

// impl Iterator for BufferedIterator {
//   type Item = u8;
//
//   fn next(&mut self) -> Option<Self::Item> {
//     match self.buffer.take() {
//       None => { self.iterator.next() }
//       Some(x) => {
//         Some(x)
//       }
//     }
//   }
// }

pub trait Parser {
  fn tokenizer(&mut self, s: String) -> String { return s }

  fn sexprUnsafe(&mut self, it: &mut BufferedIterator, variables: &mut Vec<String>, target: &mut ExprZipper) -> bool {
    while it.hasNext() {
      match it.head() as char {
        ';' => { while it.next() != '\n' as u8 {} }
        c if isWhitespace(c) => { it.next(); }
        '$' => {
          let id = {
            let mut sb = "".to_string();
            let mut cont = true;
            while it.hasNext() && cont {
              match it.head() as char {
                '(' | ')' => { cont = false }
                c if isWhitespace(c) => { cont = false }
                c => {
                  sb.push(c);
                  it.next();
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
            return true;
          } else {
            target.write_var_ref(ind as u8);
            target.loc += 1;
            return true;
          }
        }
        '(' => { return {
          let arity_loc = target.loc;
          target.write_arity(0);
          target.loc += 1;
          it.next();
          while it.head() != ')' as u8 {
            match it.head() as char {
              c if isWhitespace(c) => { it.next(); }
              _ => {
                self.sexprUnsafe(it, variables, target);
                unsafe {
                  let p = target.root.ptr.byte_add(arity_loc);
                  if let Tag::Arity(a) = byte_item(*p) {
                    *p = item_byte(Tag::Arity(a + 1));
                  } else { panic!("not arity") }
                }
              }
            }
          }
          it.next();
          true
        } }
        ')' => { panic!("Unexpected right bracket") }
        _ => {
          let e = self.tokenizer({
            if it.hasNext() && it.head() == '"' as u8 {
              {
                let mut sb = "".to_string();
                let mut cont = true;
                it.next();
                sb.push('"');
                while it.hasNext() && cont {
                  match it.next() as char {
                    '"' => {
                      sb.push('"');
                      cont = false
                    }
                    '\\' => {
                      if it.hasNext() { sb.push(it.next() as char) }
                      else { panic!("Escaping sequence is not finished") }
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
                while it.hasNext() && cont {
                  match it.head() as char {
                    '(' | ')' => { cont = false }
                    c if isWhitespace(c) => { cont = false }
                    c => {
                      sb.push(c);
                      it.next();
                    }
                  }
                }
                sb
              }
            }
          });
          target.write_symbol(e.as_bytes());
          target.loc += 1 + e.len();
          return true;
        }
      }
    }
    false
  }
}
