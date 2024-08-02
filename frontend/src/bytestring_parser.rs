use std::fs::File;
use std::io::Read;
use std::ptr;

use std::fmt::format;
use std::ptr::slice_from_raw_parts;
use std::str::Utf8Error;

#[derive(Copy, Clone, Debug)]
pub struct Breadcrumb {
  parent: u32,
  arity: u8,
  seen: u8,
}

#[derive(Copy, Clone)]
pub enum Tag {
  NewVar,
  VarRef(u8),
  SymbolSize(u8),
  Arity(u8),
}

pub fn item_byte(b: Tag) -> u8 {
  match b {
    Tag::NewVar => { 0b1100_0000 | 0 }
    Tag::SymbolSize(s) => { debug_assert!(s > 0 && s < 64); 0b1100_0000 | s }
    Tag::VarRef(i) => { debug_assert!(i < 64); 0b1000_0000 | i }
    Tag::Arity(a) => { debug_assert!(a < 64); 0b0000_0000 | a }
  }
}

fn byte_item(b: u8) -> Tag {
  if b == 0b1100_0000 { return Tag::NewVar; }
  else if (b & 0b1100_0000) == 0b1100_0000 { return Tag::SymbolSize(b & 0b0011_1111) }
  else if (b & 0b1100_0000) == 0b1000_0000 { return Tag::VarRef(b & 0b0011_1111) }
  else if (b & 0b1100_0000) == 0b0000_0000 { return Tag::Arity(b & 0b0011_1111) }
  else { panic!("reserved {}", b) }
}

#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Expr {
  pub ptr: *mut u8,
}

impl Expr {
  pub fn span(self) -> *const [u8] {
    let root = self.ptr;
    let mut ez = ExprZipper::new(self);
    loop {
      if !ez.next() {
        let size = ez.loc + match ez.tag() {
          Tag::NewVar => { 1 }
          Tag::VarRef(r) => { 1 }
          Tag::SymbolSize(s) => { 1 + (s as usize) }
          Tag::Arity(a) => { unreachable!() /* expression can't end in arity */ }
        };
        return slice_from_raw_parts(root, size)
      }
    }
  }
}

#[derive(Clone)]
pub struct ExprZipper {
  pub root: Expr,
  pub loc: usize,
  pub trace: Vec<Breadcrumb>,
}

impl ExprZipper {
  pub fn new(e: Expr) -> Self {
    match unsafe { byte_item(*e.ptr) } {
      Tag::NewVar => { Self { root: e, loc: 0, trace: vec![] } }
      Tag::VarRef(r) => { Self { root: e, loc: 0, trace: vec![] } }
      Tag::SymbolSize(s) => { Self { root: e, loc: 0, trace: vec![] } }
      Tag::Arity(a) => {
        Self {
          root: e,
          loc: 0,
          trace: vec![Breadcrumb { parent: 0, arity: a, seen: 0 }],
          // trace: vec![],
        }
      }
    }
  }

  fn tag(&self) -> Tag { unsafe { byte_item(*self.root.ptr.byte_add(self.loc)) } }
  fn item(&self) -> Result<Tag, &[u8]> {
    let tag = self.tag();
    if let Tag::SymbolSize(n) = tag { return unsafe { Err(&*slice_from_raw_parts(self.root.ptr.byte_add(self.loc + 1), n as usize)) } }
    else { return Ok(tag) }
  }
  pub fn subexpr(&self) -> Expr { unsafe { Expr { ptr: self.root.ptr.byte_add(self.loc) } } }

  fn write_arity(&mut self, arity: u8) -> bool {
    unsafe {
      *self.root.ptr.byte_add(self.loc) = item_byte(Tag::Arity(arity));
      true
    }
  }
  pub fn write_move(&mut self, value: &[u8]) -> bool {
    unsafe {
      let l = value.len();
      std::ptr::copy_nonoverlapping(value.as_ptr(), self.root.ptr.byte_add(self.loc), l);
      self.loc += l;
      true
    }
  }
  pub fn write_symbol(&mut self, value: &[u8]) -> bool {
    unsafe {
      let l = value.len();
      debug_assert!(l < 64);
      let w = self.root.ptr.byte_add(self.loc);
      *w = item_byte(Tag::SymbolSize(l as u8));
      std::ptr::copy_nonoverlapping(value.as_ptr(), w.byte_add(1), l);
      true
    }
  }
  fn write_new_var(&mut self) -> bool {
    unsafe {
      *self.root.ptr.byte_add(self.loc) = item_byte(Tag::NewVar);
      true
    }
  }
  fn write_var_ref(&mut self, index: u8) -> bool {
    unsafe {
      *self.root.ptr.byte_add(self.loc) = item_byte(Tag::VarRef(index));
      true
    }
  }

  pub fn tag_str(&self) -> String {
    match self.tag() {
      Tag::NewVar => { "$".to_string() }
      Tag::VarRef(r) => { format!("_{}", r + 1) }
      Tag::SymbolSize(s) => { format!("({})", s) }
      Tag::Arity(a) => { format!("[{}]", a) }
    }
  }

  fn item_str(&self) -> String {
    match self.item() {
      Ok(tag) => {
        match tag {
          Tag::NewVar => { "$".to_string() }
          Tag::VarRef(r) => { format!("_{}", r + 1) }
          Tag::Arity(a) => { format!("[{}]", a) }
          _ => { unreachable!() }
        }
      }
      Err(s) => {
        match std::str::from_utf8(s) {
          Ok(string) => { format!("{}", string) }
          Err(_) => { format!("{:?}", s) }
        }
      }
    }
  }

  pub fn next(&mut self) -> bool {
    // let t = self.tag();
    // let ct = self.tag_str();
    match self.trace.last_mut() {
      None => { false }
      Some(&mut Breadcrumb { parent: p, arity: a, seen: ref mut s }) => {
        // println!("parent {} loc {} tag {}", p, self.loc, ct);
        // println!("{} < {}", s, a);
        if *s < a {
          *s += 1;

          self.loc += if let Tag::SymbolSize(n) = self.tag() { n as usize + 1 } else { 1 };

          if let Tag::Arity(a) = self.tag() {
            self.trace.push(Breadcrumb { parent: self.loc as u32, arity: a, seen: 0 })
          }

          // println!("returned true");
          true
        } else {
          self.trace.pop();
          self.next()
        }
      }
    }
  }

  pub fn parent(&mut self) -> bool {
    let Some(Breadcrumb { parent: p, arity: a, seen: s }) = self.trace.last() else { return false; };
    self.loc = *p as usize;
    self.trace.pop();
    true
  }

  pub fn next_child(&mut self) -> bool {
    loop {
      // println!("#");
      if !self.next() { return false; }
      let l = self.trace.len() - 1;
      let parent = self.trace[l].parent;
      if let Tag::Arity(_) = self.tag() {
        if l > 0 && self.trace[l - 1].parent == 0 {
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
    match unsafe { byte_item(*self.root.ptr.byte_add(self.loc + i)) } {
      Tag::NewVar => { print!("$"); 1 }
      Tag::VarRef(r) => { print!("_{}", r + 1); 1 }
      Tag::SymbolSize(s) => {
        let slice = unsafe { &*slice_from_raw_parts(self.root.ptr.byte_add(self.loc + i + 1), s as usize) };
        match std::str::from_utf8(slice) {
          Ok(string) => { print!("{}", string) }
          Err(_) => { for b in slice { print!("\\x{:x}", b) } }
        }
        s as usize + 1
      }
      Tag::Arity(a) => {
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
