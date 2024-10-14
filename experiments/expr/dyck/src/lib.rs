#![no_implicit_prelude]
// #![allow(unused_imports, unused_variables, dead_code)]

extern crate alloc;
extern crate core;
extern crate std;

extern crate bnum;
extern crate num_bigint;

use alloc::vec::Vec;
use core::{
  clone::Clone,
  cmp::Ord,
  convert::From,
  iter::{IntoIterator, Iterator, Extend},
  option::Option,
  result::Result,
  str,
};
use num_bigint::BigUint;


pub mod test_parser;

mod cz2_unit_tests;
pub(crate) mod left_branch_impl;

mod dyck_zipper;
pub(crate) use dyck_zipper::*;

mod sym;
use sym::Sym;
mod zipper_tests;

pub(crate) mod solving;



/// importantly, the leading zeros are relevant!
#[repr(transparent)]
#[derive(Clone, Copy)]
pub struct Bits(pub u64);
impl core::fmt::Debug for Bits {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    core::write!(f, "{:#066b}", self.0)
  }
}


/// Represents the structure of a binary tree.  
/// 
/// for the sake of simplifying the implementation of other parts a [`DyckWord`] is defined to be non-empty
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct DyckWord {
  word: u64,
}
impl DyckWord {
  pub const LEAF : Self = DyckWord {word : 1};
  pub const fn new(word: u64) -> Option<Self> {
    if DyckWord::valid_non_empty(word) {
     Option::Some( DyckWord { word } )      
    } else {
      Option::None
    }
  }
  const fn new_debug_checked(word: u64) -> Self {
    core::debug_assert!{DyckWord::valid_non_empty(word)}
    DyckWord { word }
  }
  pub const fn zipper(self) -> DyckStructureZipperU64 {
    let mut stack = [crate::dyck_zipper::SubtreeSlice::zeroes(); DyckStructureZipperU64::MAX_LEAVES];
    stack[0].terminal = (u64::BITS).wrapping_sub(self.word.leading_zeros()) as u8;

    DyckStructureZipperU64 { structure: self.word, current_depth: 0, stack }
  }
  const fn valid_non_empty(word: u64)->bool {
    let leading = word.leading_zeros();
    if leading == 0 {return false;}
    
    let mut cursor = 1 << u64::BITS - leading - 1;
    let mut sum: i32 = 0;
    
    // a valid structure must have enough children to pair up before constructing a branch
    loop {
      if sum.is_negative() { return false; }
      if cursor == 0       { return sum == 1 }
    
      sum += if (cursor & word) == 0 { -1 } else { 1 };
      cursor >>= 1;
    }
  }  
  pub fn applicative_sexpr_viewer(self) -> Result<alloc::string::String, (SexprViewerError, Bits)> {
    use alloc::collections::VecDeque;
    use core::convert::From;
    use SexprViewerError as SVE;
    let mut stack = Vec::new();
    let word = self.word;
    if word == 0 {
      return Result::Err((SVE::Empty, Bits(0)));
    }
    if (word & (1 << u64::BITS - 1)) != 0 {
      return Result::Err((SVE::TopBitNonZero, Bits(1 << u64::BITS - 1)));
    }
    enum S {
      One,
      Nested(VecDeque<u8>),
    }

    let mut cursor = 1 << u64::BITS - word.leading_zeros() - 1;

    while cursor != 0 {
      let bit = cursor & word;
      cursor >>= 1;

      if bit != 0 {
        stack.push(S::One);
        continue;
      }
      let Option::Some(r) = stack.pop() else {
        return Result::Err((SVE::TooManyPairs, Bits(cursor)));
      };
      let Option::Some(l) = stack.pop() else {
        return Result::Err((SVE::TooManyPairs, Bits(cursor)));
      };

      stack.push(match (l, r) {
        (S::One, S::One) => S::Nested(VecDeque::from(Vec::from(b"1 1"))),
        (S::One, S::Nested(mut n)) => {
          n.push_back(b')');
          for &each in b"1 (".into_iter().rev() {
            n.push_front(each)
          }
          S::Nested(n)
        }
        (S::Nested(mut n), S::One) => {
          n.push_back(b' ');
          n.push_back(b'1');
          S::Nested(n)
        }
        (S::Nested(mut n1), S::Nested(mut n2)) => {
          n2.push_front(b'(');
          n2.push_back(b')');

          n1.push_back(b' ');
          n1.extend(n2);
          S::Nested(n1)
        }
      })
    }
    if stack.len() != 1 {
      return Result::Err((SVE::TooFewPairs, Bits(0)));
    }
    let top = stack.pop().unwrap();
    Result::Ok(match top {
      S::One => alloc::string::String::from("1"),
      S::Nested(mut n) => {
        n.push_front(b'(');
        n.push_back(b')');
        // Safety: only contains ascii values b'1', b' ', b'(', and b')'
        alloc::string::String::from(unsafe { str::from_utf8_unchecked(n.make_contiguous()) })
      }
    })
  }
}
#[derive(Debug)]
pub enum SexprViewerError {
  Empty,
  TopBitNonZero,
  TooManyPairs,
  TooFewPairs,
}
impl core::fmt::Debug for DyckWord {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
      core::write!(f, "0b_{:b}", self.word)
  }
}




#[allow(unused)]
type Int = u32;

// only run this test if `Int`` is u8, u16, or u32
#[allow(unused)]
fn all_trees() -> Vec<Int> {
  let max_leaves = Int::BITS / 2;

  use alloc::collections::BTreeMap;
  use alloc::collections::BTreeSet;
  use core::iter::Iterator;

  type Leaves = u32;
  let mut trees = BTreeMap::<Leaves, BTreeSet<Int>>::new();
  trees.insert(0, BTreeSet::from([0]));
  trees.insert(1, BTreeSet::from([1]));

  for each in 2..=max_leaves {
    let mut s = BTreeSet::<Int>::new();
    for left in 1..each {
      let right = each - left;

      for l in &trees[&left] {
        for r in &trees[&right] {
          let val = (*l << right * 2 - 1 | *r) << 1;
          s.insert(val);
        }
      }
    }
    trees.insert(each, s);
  }
  trees.into_iter().flat_map(|(_, v)| v).collect::<Vec<_>>()
}



mod val;
pub use val::{Val, ValPattern, DbgVal};
