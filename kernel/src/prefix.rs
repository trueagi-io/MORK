use std::convert::AsRef;
use std::ptr::{null, slice_from_raw_parts};
use mork_bytestring::{byte_item, Expr, ExprZipper, ExtractFailure, item_byte, parse, compute_length, Tag};
use mork_bytestring::Tag::{Arity, SymbolSize};


pub(crate) enum PrefixComparison {
  BothEmpty,
  FirstEmpty,
  SecondEmpty,
  Disjoint,
  PrefixOf,
  PrefixedBy,
  Sharing,
  Equals,
}

pub struct Prefix<'a> {
  pub slice: &'a [u8]
}

impl <'a> Prefix<'a> {
  pub const NONE: Prefix<'a> = Prefix { slice: &[] };

  // pub const fn constant(s: &str) -> Prefix<'a> {
  //     const N: usize = compute_length(s);
  //     Prefix { slice: parse::<N>(s).as_ref() }
  // }

  pub fn path(&self) -> &[u8] {
    self.slice
  }

  pub fn of_expr(e: Expr) -> Option<Prefix<'a>> {
    e.prefix().map(|x| Prefix { slice: unsafe { &*x } }).ok()
  }

  pub fn compare(&self, other: &Self, n: &mut usize) -> PrefixComparison {
    use PrefixComparison::*;
    let left = self.path();
    let right = other.path();
    let left_len = left.len();
    let right_len = right.len();
    if left_len == 0 && right_len == 0 { return BothEmpty }
    if left_len == 0 { return FirstEmpty }
    if right_len == 0 { return SecondEmpty }
    if unsafe { left.get_unchecked(0) != right.get_unchecked(0) } { return Disjoint }

    *n = 1;
    loop {
      let left_finished = *n == left_len;
      let right_finished = *n == right_len;
      if left_finished && right_finished { return Equals }
      if left_finished { return PrefixOf }
      if right_finished { return PrefixedBy }
      if unsafe { left.get_unchecked(*n) != right.get_unchecked(*n) } { return Sharing }
      *n += 1;
    }
  }
}

