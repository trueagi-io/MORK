use std::io::{BufRead, Read};

use mork_bytestring::{ExprZipper, Tag, item_byte, byte_item};

#[allow(non_snake_case)]
fn isWhitespace(c: u8) -> bool {
  c == b' ' || c == b'\t' || c == b'\n'
}

#[allow(non_snake_case, unused)]
fn isDigit(c: u8) -> bool {
  c == b'0' || c == b'1' || c == b'2' || c == b'3' || c == b'4' ||
  c == b'5' || c == b'6' || c == b'7' || c == b'8' || c == b'9'
}

#[derive(Debug)]
pub enum ParserError {
  TooManyVars,
  UnexpectedEOF,
  InputFinished,
  NotArity,
  UnexpectedRightBracket,
  UnfinishedEscapeSequence,
  OtherIOErr,
}

impl From<std::io::Error> for ParserError {
  fn from(io_err: std::io::Error) -> Self {
    match io_err.kind() {
      std::io::ErrorKind::UnexpectedEof => ParserError::UnexpectedEOF,
      _ => ParserError::OtherIOErr,
    }
  }
}

/// State associated with the parsing of a stream of s-expressions
pub struct ParseContext<SrcStream> {
  /// The stream from which to read the source expressions
  src: SrcStream,
  /// An offset relative to the beginning of the source expression stream
  byte_idx: usize,
  /// The mapping between DeBruijn indices and variable names, as indices into the `var_names` field
  var_indices: Vec<usize>,
  /// A buffer containing all the variables name that have been found
  var_names: Vec<u8>,
  /// A temporary buffer for reading from the stream
  tmp_buf: Vec<u8>,
}

impl<SrcStream: BufRead + Read> ParseContext<SrcStream> {
  /// Make a new `ParseContext` to parse the stream
  pub fn new(src: SrcStream) -> Self {
    Self{ src, byte_idx: 0, var_indices: vec![], var_names: vec![], tmp_buf: vec![] }
  }

  /// Returns index of the 
  pub fn byte_idx(&self) -> usize {
    self.byte_idx
  }

  #[inline(always)]
  fn peek(&mut self) -> Result<u8, ParserError> {
    let reader_buf = self.src.fill_buf().unwrap();
    if reader_buf.len() == 0 {
      Err(ParserError::UnexpectedEOF)
    } else {
      Ok(unsafe{ *reader_buf.get_unchecked(0) })
    }
  }

  #[inline(always)]
  fn next(&mut self) -> Result<u8, ParserError> {
    let mut c: u8 = 0;
    self.src.read_exact(core::slice::from_mut(&mut c)).map_err(|e| ParserError::from(e))?;
    self.byte_idx += 1;
    Ok(c)
    //GOAT old impl
    // let reader_buf = self.src.fill_buf().unwrap();
    // if reader_buf.len() == 0 {
    //   Err(ParserError::UnexpectedEOF)
    // } else {
    //   let r = unsafe{ *reader_buf.get_unchecked(0) };
    //   self.src.consume(1);
    //   self.byte_idx += 1;
    //   Ok(r)
    // }
  }

  #[inline(always)]
  fn next_to_tmp_buf(&mut self) -> Result<u8, ParserError> {
    let c = self.next()?;
    self.tmp_buf.push(c);
    Ok(c)
  }

  #[inline(always)]
  fn has_next(&mut self) -> bool {
    let reader_buf = self.src.fill_buf().unwrap();
    reader_buf.len() != 0
  }

  /// Finds the DeBruijn index of the named var in the `tmp_buf` among the variables that have already been
  /// encountered or saves the var name if it's the first time seeing it
  #[inline]
  fn var_in_tmp_buf(&mut self) -> Result<Option<u8>, ParserError> {
    let mut var_name_start = 0;
    for (i, &var_name_end) in self.var_indices.iter().enumerate() {
      let ctx_var = &self.var_names[var_name_start..var_name_end];
      if self.tmp_buf == ctx_var { return Ok(Some(i as u8)) }
      var_name_start = var_name_end;
    }

    if self.var_indices.len() < 64 {
      // we can only have 64 variables, we don't need a vec here, perhaps uninit array?
      self.var_names.extend(&self.tmp_buf[..]);
      self.var_indices.push(self.var_names.len());
      self.tmp_buf.clear();
      Ok(None)
    } else {
      Err(ParserError::TooManyVars)
    }
  }
}

pub trait Parser {
  fn tokenizer<'r>(&mut self, s: &[u8]) -> &'r [u8];

  /// Parse a single s-expression from the ParseContext
  fn sexpr<SrcStream: BufRead + Read>(&mut self, it: &mut ParseContext<SrcStream>, target: &mut ExprZipper) -> Result<(), ParserError> {
    use ParserError::*;
    it.var_names.clear();
    it.var_indices.clear();

    while it.has_next() {
      match it.peek()? {
        b';' => { while it.next()? != b'\n' {} }
        c if isWhitespace(c) => { it.next()?; }
        b'$' => {
          it.tmp_buf.clear();
          while it.has_next() {
            match it.peek()? {
              b'(' | b')' => { break }
              c if isWhitespace(c) => { break }
              _ => { it.next_to_tmp_buf()?; }
            }
          }

          match it.var_in_tmp_buf()? {
            None => { target.write_new_var(); target.loc += 1; }
            Some(ind) => { target.write_var_ref(ind); target.loc += 1; }
          }
          return Ok(());
        }
        b'(' => {
          let arity_loc = target.loc;
          target.write_arity(0);
          target.loc += 1;
          it.next()?;
          while it.peek()? != b')' {
            match it.peek()? {
              c if isWhitespace(c) => { it.next()?; }
              _ => {
                self.sexpr(it, target)?;
                unsafe {
                  let p = target.root.ptr.byte_add(arity_loc);
                  if let Tag::Arity(a) = byte_item(*p) { *p = item_byte(Tag::Arity(a + 1)); }
                  else { return Err(NotArity) }
                }
              }
            }
          }
          it.next()?;
          return Ok(())
        }
        b')' => { return Err(UnexpectedRightBracket) }
        _ => {
          it.tmp_buf.clear();
          if it.has_next() && it.peek()? == b'"' {
            it.next_to_tmp_buf()?;
            while it.has_next() {
              match it.next_to_tmp_buf()? {
                b'"' => { break }
                b'\\' => {
                  if it.has_next() { it.next_to_tmp_buf()?; }
                  else { return Err(UnfinishedEscapeSequence) }
                }
                _ => {}
              }
            }
          } else {
            while it.has_next() {
              match it.peek()? {
                b'(' | b')' => { break }
                c if isWhitespace(c) => { break }
                _ => { it.next_to_tmp_buf()?; }
              }
            }
          }

          let e = self.tokenizer(&it.tmp_buf[..]);
          target.write_symbol(e);
          target.loc += 1 + e.len();
          return Ok(());
        }
      }
    }
    Err(InputFinished)
  }
}
