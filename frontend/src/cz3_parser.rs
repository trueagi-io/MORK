#![allow(non_snake_case)]
use std::fs::File;
use std::io::Read;


#[derive(Copy, Clone)]
struct Breadcrumb {
  parent: u32,
  arity: u8,
  seen: u8,
}

#[derive(Copy, Clone)]
pub enum Item {
  NewVar,
  VarRef(u8),
  Symbol(u32),
  Arity(u8),
}

pub struct Expr {
  pub ptr: *mut Item,
}

pub struct ExprZipper {
  pub root: Expr,
  loc: usize,
  trace: Vec<Breadcrumb>,
}

#[allow(unused)]
impl ExprZipper {
  pub fn new(e: Expr) -> Self {
    match unsafe { *e.ptr } { // todo, should a zipper be allowed on a single item?
      Item::NewVar => { Self { root: e, loc: 0, trace: vec![] } }
      Item::VarRef(r) => { Self { root: e, loc: 0, trace: vec![] } }
      Item::Symbol(s) => { Self { root: e, loc: 0, trace: vec![] } }
      Item::Arity(a) => {
        Self {
          root: e,
          loc: 0,
          trace: vec![Breadcrumb { parent: 0, arity: a, seen: 0 }],
        }
      }
    }
  }

  fn value(&self) -> Item { unsafe { *self.root.ptr.add(self.loc) } }
  fn subexpr(&self) -> Expr { unsafe { Expr { ptr: self.root.ptr.add(self.loc) } } }

  fn write_arity(&mut self, arity: u8) -> bool {
    unsafe {
      *self.root.ptr.add(self.loc) = Item::Arity(arity);
      true
    }
  }
  fn write_symbol(&mut self, value: u32) -> bool {
    unsafe {
      *self.root.ptr.add(self.loc) = Item::Symbol(value);
      true
    }
  }
  fn write_new_var(&mut self) -> bool {
    unsafe {
      *self.root.ptr.add(self.loc) = Item::NewVar;
      true
    }
  }
  fn write_var_ref(&mut self, index: u8) -> bool {
    unsafe {
      *self.root.ptr.add(self.loc) = Item::VarRef(index);
      true
    }
  }

  fn loc_str(&self) -> String {
    match self.value() {
      Item::NewVar => { "$".to_string() }
      Item::VarRef(r) => { format!("_{}", r + 1) }
      Item::Symbol(s) => { format!("{}", s) }
      Item::Arity(a) => { format!("[{}]", a) }
    }
  }

  fn next(&mut self) -> bool {
    match self.trace.last_mut() {
      None => { false }
      Some(&mut Breadcrumb { parent: p, arity: a, seen: ref mut s }) => {
        if *s < a {
          self.loc += 1;
          *s += 1;
          if let Item::Arity(a) = self.value() {
            self.trace.push(Breadcrumb { parent: self.loc as u32, arity: a, seen: 0 })
          }
          true
        } else {
          self.trace.pop();
          self.next()
        }
      }
    }
  }

  fn parent(&mut self) -> bool {
    let Some(Breadcrumb { parent: p, arity: a, seen: s }) = self.trace.last() else { return false; };
    self.loc = *p as usize;
    self.trace.pop();
    true
  }

  fn next_child(&mut self) -> bool {
    loop {
      if !self.next() { return false; }
      let l = self.trace.len() - 1;
      let parent = self.trace[l].parent;
      if let Item::Arity(_) = self.value() {
        if parent == self.loc as u32 && self.trace[l - 1].parent == 0 {
          return true;
        }
      } else {
        if parent == 0 {
          return true;
        }
      }
    }
  }

  /// Debug traversal
  pub fn traverse(&self, i: usize) -> usize {
    match unsafe { *self.root.ptr.add(self.loc + i) } {
      Item::NewVar => { print!("$"); 1 }
      Item::VarRef(r) => { print!("_{}", r + 1); 1 }
      Item::Symbol(s) => { print!("{}", s); 1 }
      Item::Arity(a) => {
        print!("(");
        let mut offset = 1;
        for k in 0..a {
          offset += self.traverse(i + offset);
          if k != (a - 1) { print!(" ") }
        }
        print!(")");
        offset
      }
    }
  }
}

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
pub fn isDigit(c: char) -> bool {
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
  fn tokenizer(&mut self, s: String) -> i64;

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
                unsafe { let Item::Arity(ref mut a) = *target.root.ptr.add(arity_loc) else { panic!("not arity") }; *a += 1; }
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
          target.write_symbol(e as u32);
          target.loc += 1;
          return true;
        }
      }
    }
    false
  }
}
