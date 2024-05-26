#![no_implicit_prelude]

extern crate alloc;
extern crate core;
extern crate std;


extern crate num_bigint;

use alloc::{sync::Arc, vec::Vec};
use core::{
  clone::Clone,
  convert::From,
  default::Default,
  iter::{Extend, IntoIterator, Iterator},
  option::Option,
  result::Result,
};
use num_bigint::{BigInt, BigUint, ToBigInt};
use std::default;

mod finite;

type Shared<T> = Arc<T>;
type PathInt = u64;

pub struct BoundedDyck<L> {
  path: PathInt,
  leaves: Arc<[L]>,
}

pub struct UnboundedDyck<L> {
  path: BigUint,
  leaves: Arc<[L]>,
}

pub enum Dyck<L> {
  Bounded(BoundedDyck<L>),
  UnboundedDyck(UnboundedDyck<L>),
}

impl<L> BoundedDyck<L> {
  fn zero() -> Self {
    Self { path: 0, leaves: Shared::from([]) }
  }
  unsafe fn new_unchecked(path: PathInt, leaves: Arc<[L]>) -> Self {
    Self { path, leaves }
  }
  fn new(path: PathInt, leaves: Arc<[L]>) -> Option<Self> {
    if path.count_ones() as usize > leaves.len() {
      return Option::None;
    }
    unsafe { Option::Some(Self::new_unchecked(path, leaves)) }
  }
}
impl<L> UnboundedDyck<L> {
  fn zero() -> Self {
    Self { path: BigUint::ZERO, leaves: Shared::from([]) }
  }
  unsafe fn new_unchecked(path: BigUint, leaves: Shared<[L]>) -> Self {
    Self { path, leaves }
  }
  fn new(path: BigUint, leaves: Shared<[L]>) -> Option<Self> {
    if path.count_ones() as usize > leaves.len() {
      return Option::None;
    }
    unsafe { Option::Some(Self::new_unchecked(path, leaves)) }
  }
}

impl<L> Dyck<L> {
  fn new_unchecked(path: &[u32], leaves: Shared<[L]>) -> Self {
    if path.len() * u32::BITS as usize > PathInt::BITS as usize {
      let mut v: Vec<u32> = path.into_iter().rev().copied().collect();
      let path_bui = BigUint::new(v);
      unsafe { Dyck::UnboundedDyck(UnboundedDyck::new_unchecked(path_bui, leaves)) }
    } else {
      let mut path_i = 0;
      for each in path {
        path_i <<= 1;
        path_i |= *each as u64;
      }
      unsafe { Dyck::Bounded(BoundedDyck::new_unchecked(path_i, leaves)) }
    }
  }

  fn new(path: &[u32], leaves: Shared<[L]>) -> Option<Self> {
    if path.len() * u32::BITS as usize > PathInt::BITS as usize {
      let mut v: Vec<u32> = path.into_iter().rev().copied().collect();
      let path_bui = BigUint::new(v);
      UnboundedDyck::new(path_bui, leaves).map(Dyck::UnboundedDyck)
    } else {
      let mut path_i = 0;
      for each in path {
        path_i <<= u32::BITS;
        path_i |= *each as u64;
      }
      BoundedDyck::new(path_i, leaves).map(Dyck::Bounded)
    }
  }
}

struct DyckZipper<'a, L> {
  path_offset: usize,
  //? path_len: usize, // to slice
  //? depth  // to avoid masking off top when doing popcnt check
  view_of: &'a Dyck<L>,
}

impl<'a, L> Clone for DyckZipper<'a, L> {
  fn clone(&self) -> Self {
    // Safety: we are implementing a Copy type
    unsafe { core::ptr::read(self) }
  }
}
impl<'a, L> core::marker::Copy for DyckZipper<'a, L> {}

// impl<'a, L> DyckZipper<'a, L> {
//   fn go_left(self)->Option<Self>{
//   }
// }

#[cfg(test)]
mod test {
  use crate::*;
  #[test]
  fn test_bed() {
    /*

    splits :
      L R
    | 1 10  (trivial_subtree)

    | _ 10  (left_tree right_leaf_partial_apply_branch)
    | 0 11  (left_branch end_of_right_branch)   unless last branch (because leading zeros)

           if the offest is here, the popcnt of the diff is 2, 1 would mean valid tree,
           so it is not a valid left branch, if the diff was ever 0, it would be "malformed"
           v
    1__11100_110_0__0

    */

    let structure_0 = 0b_1_11010_1101100_00_u64;

    let top_bit = |s: u64| ((!0_u64 << u64::BITS - s.leading_zeros()) >> 1).wrapping_neg();
    let left_split = /* 0 11 pattern represents a "non-trivial" split, where 0 is the left node */
    ( !structure_0>> 1 & structure_0 &  structure_0 << 1 
    & !top_bit(structure_0)
    ) << 1;
    //                           0b_1__11010_1101100_00_u64;
    core::assert_eq!(left_split, 0b_0__00001_0010000_00);

    let structure_0 = 0b_1_11010_1101100_00_u64;

    let top_bit = |s: u64| ((!0_u64 << u64::BITS - s.leading_zeros()) >> 1).wrapping_neg();
    let left_split = /* 0 11 pattern represents a "non-trivial" split, where 0 is the left node */
      !structure_0 & structure_0 <<1  &  structure_0 << 2;

    //                           0b___1__11010_1101100_00_u64;
    core::assert_eq!(left_split, 0b_1_0__00001_0010000_00, "{:b}", left_split);

    //                                                  0b_1__11010_1101100_00_u64;
    core::assert_eq!(left_split & !top_bit(left_split), 0b_0__00001_0010000_00, "{:b}", left_split & !top_bit(left_split));
  }
}

type Int = u16;
// fn left_branch

fn left_branch(structure: Int) -> Int {
  // left branches can only appear inn trees, not nodes or the empty tree
  // core::assert!(structure.count_ones() > 1);
  if structure.count_ones() <=1 { return 0;}

  if 0b10 & structure == 0b10 {
    return 0b100;
  }

  /* 011 bit pattern represents a "non-trivial" split, where 0 is the left node
     the bit one past the end will always be a "non-trivial" split,
  */
  let left_splits = !structure & structure << 1 & structure << 2;

  let top_mask = !(1 << Int::BITS - structure.leading_zeros() - 1);
  let mut remaining = left_splits;

  // moving from right to left
  loop {
    let current = remaining & remaining.wrapping_neg();
    match remaining.count_ones() {
      1 => break remaining >> 1,
      2 => break current,

      _ => {
        let mask_out = top_mask | (current << 1) - 1;
        if (structure & !mask_out).count_ones() - (structure | mask_out).count_zeros() == 0 {
          break current;
        }

        remaining ^= current;
      }
    }
  }
}

#[test]
fn test_for_byte(){
  let trees = all_trees();
  let count = trees.len();
  for each in trees
  {
    std::println!("num\t{each:016b} at\t{:016b}", left_branch(each))
  }
  std::println!("count : {count}")
}

fn all_trees()->Vec<Int> {
  let max_leaves = Int::BITS/2;

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
      
      core::debug_assert_ne!(left,each);
      core::debug_assert_ne!(left,0);
      core::debug_assert_ne!(right,0);

      for l in &trees[&left] {
        for r in &trees[&right] {
          let val = (*l<<right*2-1 | *r) << 1 ;
          s.insert(val);
        }
      }
    }
    trees.insert(each, s);
  }
  trees.into_iter().flat_map(|(_,v)|v).collect::<Vec<_>>()
}
