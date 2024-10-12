
extern crate alloc;
extern crate core;
extern crate std;


use {
crate::{Val, Sym, DyckStructureZipperU64, DbgVal},

  core::{result::Result, option::Option, iter::Iterator, clone::Clone},
  alloc::vec::Vec,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DeBruijnLevel {
  Intro,
  Ref(core::num::NonZeroIsize),
}
impl DeBruijnLevel {
  fn as_index(self) -> usize {
    match self {
      DeBruijnLevel::Intro => 0,
      DeBruijnLevel::Ref(nzu) => (!nzu.get()) as usize,
    }
  }
  const fn var(self)->Val { 
    match self {
      DeBruijnLevel::Intro => Val::INTRO,
      DeBruijnLevel::Ref(r) => {
        core::assert!(r.get() < 0);
        Val(r.get())
      },
    }
  }
}


#[derive(Debug, Clone, PartialEq)]
pub struct Variables {
  /// de bruin levels, but the indexing for the first variable starts at 1 instead of 0, 0 represents the introduction of a variable
  store: Vec<(usize, Sym)>,
}
impl Variables {
  fn new() -> Variables {
    Variables { store: Vec::new() }
  }
  fn aquire_de_bruin(&mut self, pos: usize, sym: Sym) -> DeBruijnLevel {
    if let level @ DeBruijnLevel::Ref(_) = self.lookup(sym) {
      return level;
    }
    self.store.push((pos, sym));
    DeBruijnLevel::Intro
  }

  fn clear(&mut self) {
    self.store.clear();
  }

  /// returns DebruijnLevel::Intro if the value is not yet in the table
  fn lookup(&self, sym: Sym) -> DeBruijnLevel {
    let offset = 0;
    let mut idx = self.store.len();
    while idx != 0 {
      idx -= 1;
      if self.store[idx].1 == sym {
        // Safety: `idx` never enters the loop if it is equal to `0`
        return DeBruijnLevel::Ref(unsafe { core::num::NonZeroIsize::new_unchecked(!((idx + offset) as isize)) });
      }
    }
    DeBruijnLevel::Intro
  }
}


#[derive(Debug)]
pub enum ParseErr {
  TooManyClosingParenthesis(LineCol),
  MissingOpenParrenthesis(LineCol),
  TokenizationError(TokenErr),
  DyckReprLimitedTo32Elements(LineCol),
}
#[derive(Debug)]
pub enum TokenErr {
  InvalidHexEscape(LineCol),
  InvalidUnicodeEscape(LineCol),
  InvalidEscapeSequence(LineCol),
  InvalidStringLiteral(LineCol),
  InvalidIdentifier(LineCol),
}
#[derive(Debug)]
pub struct LineCol(pub usize, pub usize);

struct Token {
  src_offset: usize,
  r#type: TokenType,
}
#[derive(Debug, Clone, Copy)]
pub enum TokenType {
  LPar,
  RPar,
  Var(Sym),
  Atom(Sym),
}

/// The Dyck Parser can either make applicative or list Sexprs into Zippers.
pub struct DyckParser<'a> {
  tokenizer: Tokenizer<'a>,
  /** Tokenizer has the src too, but this keeps lifetimes simpler */
  src: &'a str,
  threaded_variables: Option<Variables>,
}

struct DyckParserIterState<'a, 't> {
  tokenizer: &'t mut Tokenizer<'a>,
  src: &'a str,
  s_expr_vec: Vec<Val>,
  list_length: u8,
  depth: usize,
  stack: [u8; 32],
  dyck_word: u64,
  variables: Variables,
  cur_token: Token,
}
impl<'a, 't> DyckParserIterState<'a, 't> {
  #[cfg_attr(rustfmt, rustfmt::skip)]
  fn init(DyckParser { tokenizer, src , threaded_variables}: &'t mut DyckParser<'a>) -> Result<Option<Self>, ParseErr> {
    let Option::Some(Result::Ok(Token { src_offset, r#type})) = tokenizer.next() else { return Result::Ok(Option::None); };
    let TokenType::LPar                                       = r#type           else { return Result::Err(ParseErr::MissingOpenParrenthesis(Tokenizer::at_line(src, src_offset))); };
    Result::Ok(Option::Some(Self {
      tokenizer,
      src,
      s_expr_vec  : Vec::with_capacity(32),
      list_length : 0,
      depth       : 0,
      stack       : [0u8; 32],
      dyck_word   : 0,
      variables   : if let Option::Some(vars) = threaded_variables {vars.clone()} else {Variables::new()},
      cur_token   : Token {src_offset, r#type}
    }))
  }

  fn append_element(&mut self, e: Val) {
    self.s_expr_vec.push(e);
    self.list_length += 1;
    self.dyck_word <<= 1;
    self.dyck_word |= 1;
  }
  #[cfg_attr(rustfmt, rustfmt::skip)]
  fn consume_till_balanced(&mut self) {
    loop {
      let Option::Some(t)                                                                 = self.tokenizer.next() else { return };
      let Result::Ok(Token{ r#type : par_tok @ (TokenType::LPar | TokenType::RPar) ,.. }) = t                     else { continue };
    
      match par_tok {
        TokenType::RPar if self.depth == 0 => return,
        TokenType::RPar                => self.depth-=1,
        TokenType::LPar                => self.depth+=1,
        _                              => {},
      }
    }
  }
  fn push(&mut self) -> Result<(), ParseErr> {
    if self.depth == 32 {
      self.consume_till_balanced();
      return Result::Err(ParseErr::DyckReprLimitedTo32Elements(Tokenizer::at_line(self.src, self.cur_token.src_offset)));
    }
    self.stack[self.depth] = self.list_length;
    self.depth += 1;
    self.list_length = 0;
    Result::Ok(())
  }
  fn pop(&mut self) -> bool {
    if self.depth == 0 {
      return false;
    }
    self.depth -= 1;
    self.list_length = self.stack[self.depth];
    self.list_length += 1;
    true
  }
  fn make_singleton(&mut self) {
    let new_index = self.s_expr_vec.len();
    self.append_element(Val::atom(Sym::new("Singleton")));
    self.s_expr_vec.swap(new_index - 1, new_index);
  }
  fn make_empty(&mut self) {
    self.append_element(Val::atom(Sym::new("Empty")))
  }

  fn make_var(&mut self, sym: Sym) -> Result<(), ParseErr> {
    if self.s_expr_vec.len() == 32 {
      self.consume_till_balanced();
      return Result::Err(ParseErr::DyckReprLimitedTo32Elements(Tokenizer::at_line(self.src, self.cur_token.src_offset)));
    }
    let elem = self.variables.aquire_de_bruin(self.s_expr_vec.len(), sym).var();
    self.append_element(elem);
    Result::Ok(())
  }
  fn make_atom(&mut self, sym: Sym) -> Result<(), ParseErr> {
    if self.s_expr_vec.len() == 32 {
      self.consume_till_balanced();
      return Result::Err(ParseErr::DyckReprLimitedTo32Elements(Tokenizer::at_line(self.src, self.cur_token.src_offset)));
    }
    let elem = Val::atom(sym);
    self.append_element(elem);
    Result::Ok(())
  }
  fn next_token(&mut self) -> Option<Result<Token, ParseErr>> {
    let r = self.tokenizer.next();
    match r {
      Option::Some(Result::Ok(t @ Token { src_offset, r#type })) => {
        self.cur_token = Token { src_offset, r#type };
        Option::Some(Result::Ok(t))
      }
      Option::Some(Result::Err(e)) => {
        self.consume_till_balanced();
        Option::Some(Result::Err(ParseErr::TokenizationError(e)))
      }
      Option::None => Option::None,
    }
  }
}

impl<'a> DyckParser<'a> {
  pub fn new(src: &'a str) -> Self {
    Self { tokenizer: Tokenizer::init(src), src, threaded_variables: Option::None }
  }
  pub(crate) fn clear_variables(&mut self) {self.threaded_variables = Option::None;}
  pub(crate) fn thread_variables(&mut self, mut vars: Option<Variables>) -> Option<Variables> {
    core::mem::swap(&mut vars, &mut self.threaded_variables);
    vars
  }
  /// the applicative representation
  #[cfg_attr(rustfmt, rustfmt::skip)]
  pub fn parse_first_sexrs_to_dyck_app_repr(&mut self) -> Option<Result<(DyckStructureZipperU64, Vec<Val>, Variables), ParseErr>> {
    self.parse_first_sexrs_to_dyck_select::<true>()
  }

  /// the list representation
  #[cfg_attr(rustfmt, rustfmt::skip)]
  pub fn parse_first_sexrs_to_dyck_list_repr(&mut self) -> Option<Result<(DyckStructureZipperU64, Vec<Val>, Variables), ParseErr>> {
    self.parse_first_sexrs_to_dyck_select::<false>()
  }

  fn parse_first_sexrs_to_dyck_select<const APP_REPR : bool>(&mut self) -> Option<Result<(DyckStructureZipperU64, Vec<Val>, Variables), ParseErr>> {
    #![cfg_attr(rustfmt, rustfmt::skip)]
    #[allow(non_snake_case)]
    let LIST_REPR : bool = !APP_REPR;

    let err = |e| Option::Some(Result::Err(e));

    let mut state = match DyckParserIterState::init(self) {
        Result::Ok(s) => s?,
        Result::Err(e) => return err(e),
    };

    'build_sexpr : while let Option::Some(result) = state.next_token() {
      match result {
        Result::Err(e)                  => return err(e) ,
        Result::Ok(Token { r#type,.. }) =>
          match r#type {
            TokenType::LPar      => if let Result::Err(e) = state.push() { return err(e); },
            TokenType::RPar       => { match state.list_length {
                                         0 => state.make_empty(),
                                         1 => {
                                           state.make_singleton();
                                        
                                           if APP_REPR { state.dyck_word<<=1; }
                                         }
                                         _ => {}
                                       }
                                     
                                       if LIST_REPR {
                                         for _ in 0..state.list_length-1 { state.dyck_word<<=1 }
                                       }
                                     
                                       if !state.pop() { break 'build_sexpr; }

                                       if APP_REPR && state.list_length > 1 { state.dyck_word<<=1 }
                                     },
            TokenType::Var(sym)  => { if let Result::Err(e) = state.make_var(sym)  { return err(e) }
                                      if APP_REPR && state.list_length > 1 { state.dyck_word<<=1 }
                                    }
            TokenType::Atom(sym) => { if let Result::Err(e) = state.make_atom(sym) { return err(e) }
                                      if APP_REPR && state.list_length > 1 { state.dyck_word<<=1 }
                                    },
          },
      }
    }
    let zipper = DyckStructureZipperU64::new(state.dyck_word).unwrap();
    let s_expr_vec = state.s_expr_vec;
    let variables = state.variables;
    if let Option::Some(v) =  &mut self.threaded_variables { *v = variables.clone() };

    Option::Some(Result::Ok((zipper, s_expr_vec, variables)))
  }
}
impl<'a> Iterator for DyckParser<'a> {
  type Item = Result<(DyckStructureZipperU64, Vec<Val>, Variables), ParseErr>;
  fn next(&mut self) -> Option<Self::Item> {
    self.parse_first_sexrs_to_dyck_app_repr()
  }
}

struct Tokenizer<'a> {
  src: &'a str,
  indicies_chars: core::iter::Peekable<core::str::CharIndices<'a>>,
}

impl<'a> Tokenizer<'a> {
  fn init(src: &'a str) -> Self {
    Tokenizer { src: src, indicies_chars: src.char_indices().peekable() }
  }

  fn at_line(src: &str, idx: usize) -> LineCol {
    if let Option::Some((line_idx, precedeing)) = src.get(0..idx).unwrap().lines().enumerate().last() {
      LineCol(line_idx, precedeing.len())
    } else {
      LineCol(0, 0)
    }
  }

  /// doing Rust style escape sequence
  #[cfg_attr(rustfmt, rustfmt::skip)]
  fn escape_sequence(src: &'a str, (lead_idx, _lead_char): (usize, char), indicies_chars: &mut impl Iterator<Item = (usize, char)>) -> Result<(), TokenErr> {

    let err = |idx, err : fn(_)->_| Result::Err(err(Tokenizer::at_line(src, idx)));

    let Option::Some((escape_idx, escape)) = indicies_chars.next()          else { return err(lead_idx,   TokenErr::InvalidEscapeSequence); };
    core::debug_assert_eq!('\\', src.get(escape_idx-1..).unwrap().chars().next().unwrap());

    macro_rules! hex {() => { 'a'..='f'|'A'..='F'|'0'..='9'};}
    macro_rules! ret_err {($TOK_ERR:ident) => { return err(escape_idx, TokenErr::$TOK_ERR) };}
    match escape {
      'n' | 'r' | 't' | '\\' | '0' | '\'' | '\"' => {}
      'x' =>  '_ascii_hex_escape: {
                let h_l = [indicies_chars.next(), indicies_chars.next()];
                let [Option::Some((_, high)), Option::Some((_, low))] = h_l else { ret_err!(InvalidHexEscape) };
                let ['0'..='7', hex!()] = [high, low]                       else { ret_err!(InvalidHexEscape) };
              }
      'u' =>  '_unicode_escape: {
                let mut buf = ['\0'; 6];
                for i in 0..6 {
                  let Option::Some((_, c)) = indicies_chars.next()          else { ret_err!(InvalidHexEscape) };
                  buf[i] = c
                }
                let ['{', '0'..='7', hex!(), hex!(), hex!(), '}'] = buf     else { ret_err!(InvalidUnicodeEscape) };
              }
      _   =>                                                                       ret_err!(InvalidEscapeSequence),
    }
    Result::Ok(())
  }
}

impl<'a> Iterator for Tokenizer<'a> {
  type Item = Result<Token, TokenErr>;
  fn next(&mut self) -> Option<Self::Item> {
let Self { src, indicies_chars } = self;

#[cfg_attr(rustfmt, rustfmt::skip)]
'_make_token: loop {
  let Option::Some(&lead @ (lead_idx, lead_char)) = indicies_chars.peek() else {
    return Option::None;
  };
  let item = |i                                | Option::Some(Result::Ok(Token{src_offset: lead_idx, r#type : i}));
  let err  = |err_type: fn(LineCol) -> TokenErr| Option::Some(Result::Err(err_type(Tokenizer::at_line(src, lead_idx))));
  let sym  = |end_idx                          | Sym::new(unsafe { src.get_unchecked(lead_idx..end_idx) });

  match lead_char {
    '(' => { indicies_chars.next(); return item(TokenType::LPar);}
    ')' => { indicies_chars.next(); return item(TokenType::RPar);}
    ';' => 'ignore_comment: loop {
      let Option::Some((_, c)) = indicies_chars.next() else { break 'ignore_comment; };
      if let '\n' = c { break 'ignore_comment; }
    },
    '\"' => 'string: {
      /* ground string, rust style, we do not support raw strings */
      indicies_chars.next();
      loop {
        let Option::Some((_, c)) = indicies_chars.next() else { break 'string; };
        match c {
          '\"' => { let Option::Some(&(e_idx, e)) = indicies_chars.peek() else { break 'string; };
                    let valid =  core::matches!(e, '('|')') || e.is_whitespace();
                    return if valid { item(TokenType::Atom(sym(e_idx))) }
                           else     { err(TokenErr::InvalidStringLiteral) }
                  }
          '\\' => if let Result::Err(e) = Tokenizer::escape_sequence(src, lead, indicies_chars) {return Option::Some(Result::Err(e));},
          _    => {}
        }
      }
    },
    w if w.is_whitespace() => core::mem::drop(indicies_chars.next()),
    x => 'ident :{
      // a var that is just "$" is a hole ? */
      let token_type = if let '$' = x { TokenType::Var } else { TokenType::Atom};

      loop {
        let Option::Some(&(c_idx, c)) = indicies_chars.peek() else { break 'ident; };
        let var_or_atom = || item(token_type(sym(c_idx)) );
        match c {
          '\"'                   => return err(TokenErr::InvalidIdentifier),
          '(' | ')'              => return var_or_atom(),
          w if w.is_whitespace() => return var_or_atom(),
          _                      => indicies_chars.next(),
        };
      };
    }
  };
}
  }
}

#[cfg(test)]
#[test]
fn test_dyck_parser() {
  let s = r#"
  (+ 1 2 3)
  (- 4 5 6)

  (eq ($X 3) (4 $Y) ($X $Y))

  (let ((x "given a lot of \x4A \u{0001}")
  (y "yup"))
  (print x y))

  ((\ (x) x) of love)

  )))
  ((\ (x) x) of love)
  ((\ (x) x) of love
  ((\ (x) x) of love)
  ((\ (x) x) of love)
  )))))))
  (a b c d e)
  (a (b c) (d e f))
  (a be e)
  (()(()))
  "#;

  // let path = std::dbg!(std::path::PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap()).join("tmp/edges5000.metta"));
  // let s = std::fs::read_to_string(path).unwrap();

  // let p = DyckParser::new(&s);
  let mut count = 0;
  let start = std::time::Instant::now();
  for _ in 0..1000 {
for _each in DyckParser::new(&s) {
  count += 1;
  // comment `continue` for printing 
  continue; 
  #[allow(unreachable_code)]
  match _each {
    Result::Ok((zip, store, vars)) => {
      std::print!("\n{zip:?}store: [  ");
      for leaf in store.iter().copied().map(DbgVal) {
        std::print!("{leaf:?}  ")
      }
      std::print!("]\nvars  : [");
      for leaf in vars.store.iter() {
        std::print!("{leaf:?}  ")
      }
      std::println!("]")
    }
    Result::Err(e) => std::println!("{e:?}"),
  }
}
  }
  let end = start.elapsed().as_millis();
  std::println!("count : {count}\ntime : {end}")
}
