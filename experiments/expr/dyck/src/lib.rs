#![no_implicit_prelude]

extern crate alloc;
extern crate core;
extern crate std;

extern crate bnum;
extern crate num_bigint;

use alloc::{sync::Arc, vec::Vec};
use core::{
  clone::Clone,
  convert::From,
  default::Default,
  iter::{IntoIterator, Iterator},
  option::Option,
  result::Result,
  cmp::Ord,
};
use num_bigint::BigUint;

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
      let v: Vec<u32> = path.into_iter().rev().copied().collect();
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






#[derive(Clone, Copy)]
pub(crate) struct SubtreeSlice {
  /// the position of the terminating __0__ bit after the last leaf
  pub(crate) terminal: u8,
  pub(crate) head: u8,
}
impl SubtreeSlice {
  fn is_leaf(&self) -> bool {
    1 == self.terminal - self.head
  }
  fn left_subtree_head(self, structure: u64) -> u64 {
    let slice = (structure & (10_u64 << self.terminal - 1).wrapping_sub(1)) >> self.head;

    left_branch_impl::u64::left_branch(slice) << self.head
  }
}

pub struct DyckStructureZipperU64 {
  structure: u64,
  current_depth: u8,
  stack: [SubtreeSlice; DyckStructureZipperU64::STACK_LEN],
}

impl core::fmt::Debug for DyckStructureZipperU64 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
      core::write!(f, "\
        DyckStructureZipperU64 {{\
        \n  structure     : {:b},\
        \n  current_depth : {},\
        \n  stack         : [ ", self.structure, self.current_depth)?;
      for each in &self.stack[..=self.current_depth as usize] {
        core::write!(f,"\n\t{{ term:{}, head:{} }} => ", each.terminal, each.head)?;
        for _ in 0..u64::BITS as u8-each.terminal {
          core::write!(f,"_")?
        }
        core::write!(f,"{:b}", (self.structure&((1 << each.terminal) - (1 << each.head))) >> each.head )?;
        for _ in 0..each.head {
          core::write!(f,"_")?
        }
        core::write!(f,",")?
      }

      core::writeln!(f,"\n  ],\n}}")
    }
}

impl DyckStructureZipperU64 {
  const STACK_LEN: usize = u64::BITS as usize / 2;

  // TODO : add debug assert that checks that the tree is valid
  pub fn new(structure: u64) -> Option<Self> {
    if let 0 = structure {
      return Option::None;
    }

    let mut stack = [SubtreeSlice { terminal: 0, head: 0 }; Self::STACK_LEN];
    stack[0].terminal = (u64::BITS).wrapping_sub(structure.leading_zeros()) as u8;

    Option::Some(Self { structure, current_depth: 0, stack })
  }

  pub fn decend_left(&mut self) -> bool {
    let cur = self.stack[self.current_depth as usize];
    if cur.is_leaf() {
      return false;
    }
    let l_head @ (1..=u64::MAX) = cur.left_subtree_head(self.structure) else {
      return false;
    };

    self.current_depth += 1;
    self.stack[self.current_depth as usize] = SubtreeSlice { terminal: cur.terminal, head: l_head.trailing_zeros() as u8 };

    true
  }

  pub fn decend_right(&mut self) -> bool {
    let cur = self.stack[self.current_depth as usize];
    if cur.is_leaf() {
      return false;
    }
    let l_head @ (1..=u64::MAX) = cur.left_subtree_head(self.structure) else {
      return false;
    };

    self.current_depth += 1;
    self.stack[self.current_depth as usize] = SubtreeSlice { terminal: l_head.trailing_zeros() as u8, head: cur.head + 1 };

    true
  }

  pub unsafe fn switch_right_unchecked(&mut self) {
    let Self { structure, current_depth, stack } = self;
    core::debug_assert!(!core::matches!(*structure, 0 | 1));
    core::debug_assert_ne!(*current_depth, 0);

    let prev = unsafe { *stack.get_unchecked(*current_depth as usize - 1) };
    let cur = unsafe { stack.get_unchecked_mut(*current_depth as usize) };

    // is left
    core::debug_assert_eq!(prev.terminal, cur.terminal);
    // not right
    core::debug_assert_ne!(prev.head, cur.head - 1);

    *cur = SubtreeSlice { terminal: cur.head, head: prev.head + 1 };
  }
  pub fn switch_right(&mut self) -> bool {
    let Self { structure, current_depth, stack } = self;
    if *structure <= 1  || 0 == *current_depth {
      return false;
    }

    // Safety: The current depth is > 0
    let prev = unsafe { stack.get_unchecked(*current_depth as usize - 1) };
    let cur = unsafe { stack.get_unchecked(*current_depth as usize) };


    // avoid double right
    if prev.head == cur.head + 1 {
      return false;
    }

    unsafe { self.switch_right_unchecked() }

    true
  }
  pub unsafe fn switch_left_unchecked(&mut self) {
    let Self { structure, current_depth, stack } = self;
    core::debug_assert!(!core::matches!(*structure, 0 | 1));
    core::debug_assert_ne!(*current_depth, 0);

    let prev = unsafe { *stack.get_unchecked(*current_depth as usize - 1) };
    let cur = unsafe { stack.get_unchecked_mut(*current_depth as usize) };

    // not left
    core::debug_assert_ne!(prev.terminal, cur.terminal);
    // is right
    core::debug_assert_eq!(prev.head, cur.head-1);

    *cur =  SubtreeSlice { terminal: prev.terminal, head: cur.terminal };
  }
  pub fn switch_left(&mut self) -> bool {
    let Self { structure, current_depth, stack } = self;
    if *structure <= 1|| 0 == *current_depth {
      return false;
    }

    // Safety: The current depth is > 0
    let prev = unsafe { stack.get_unchecked(*current_depth as usize - 1) };
    let cur = unsafe { stack.get_unchecked(*current_depth as usize) };

    // avoid double left
    if prev.terminal == cur.terminal {
      return false;
    }

    unsafe { self.switch_left_unchecked() };

    true
  }

  pub unsafe fn closest_rightmost_store_index_unchecked(&self, tree_offset: u8) -> usize {
    core::assert_ne!(self.structure & 1<<tree_offset as u32, 0);
    (self.structure & !((0b_10 << tree_offset as u32)-1)).count_ones() as usize
  }

  pub fn current_leaf_store_index_range(&self) -> core::ops::Range<usize> {
    unsafe {
      let cur = self.stack.get_unchecked(self.current_depth as usize);
      let right = (
        ( self.structure 
        ^   self.structure 
          & ((0b_1 << (cur.head as u32))-1)
        ).trailing_zeros() as u8)
        .min(cur.terminal-1);
      
      let first = self.closest_rightmost_store_index_unchecked(cur.terminal - 1);

      let last = self.closest_rightmost_store_index_unchecked(right);

         
      first .. last.max(first)+1
    }
  }

  /// Index of the first in the current scope
  pub fn current_first_leaf_store_index(&self) -> usize {
    unsafe { 
      let cur =  self.stack.get_unchecked(self.current_depth as usize);
      self.closest_rightmost_store_index_unchecked(cur.terminal - 1) 
    }
  }

  pub fn accend(&mut self)->bool {
    if self.current_depth == 0 { return false; }
    self.current_depth-=1;
    true
  }

  pub fn accend_n(&mut self, n : u8)->bool {
    if self.current_depth < n { return false;}
    self.current_depth-=n;
    true
  }


}

pub trait DyckPathFindLeftBranch
where
  usize: From<Self::Offset>,
{
  type Offset;
  fn left_branch(self) -> Self::Offset;
}

pub(crate) mod left_branch_impl {
  pub(crate) mod u64 {
    pub(crate) fn left_branch(structure: u64) -> u64 {
      if structure <= 1 {
        return 0;
      }
      if 0b10 & structure == 0b10 {
        return 0b100;
      }
      let mut left_splits = !structure & structure << 1 & structure << 2;
      loop {
        let trailing = left_splits.trailing_zeros();
        let current = 1 << trailing;
        if let 1 = left_splits.count_ones() {
          return current >> 1;
        }
        let tmp = structure >> trailing;
        if (u64::BITS - tmp.leading_zeros() + 1).wrapping_sub(tmp.count_ones() * 2) == 0 {
          return current;
        }
        left_splits ^= current;
      }
    }
  }

  // we might be interested in testing the 512 fixed size, as that makes for 256 leaves max, which means the backing Vec can be indexed by a byte.
  // unfortunately, this appears to be as slow as the unbounded version, likely due to a subpar implementation on the U512 type if the issue is the same as Adam had.
  // It currently used the version of the algorithim that the unbounded one uses as it is a tad faster
  pub(crate) mod u512 {
    use crate::*;
    pub(crate) use bnum::types::U512;

    pub(crate) fn left_branch(mut structure: U512) -> Option<core::num::NonZeroU32> {
      let offset = 'find_offset: {
        if structure.count_ones() <= 1 {
          break 'find_offset 0;
        }

        #[allow(non_upper_case_globals)]
        const u_0b10: U512 = U512::TWO;
        #[allow(non_upper_case_globals)]
        const u_0b100: U512 = U512::FOUR;

        if structure.bit(1) && !structure.bit(0) {
          break 'find_offset 2;
        }

        /* 011 bit pattern represents a "non-trivial" split, where 0 is the left node
        the bit one past the end will always be a "non-trivial" split,
        */

        let mut left_splits = U512::ONE << structure.bits() + 1;

        // [0]11
        left_splits -= U512::ONE;
        left_splits ^= &structure;

        // [0]11 & 0[1]1 => [01]1
        structure <<= 1;
        left_splits &= &structure;

        // [01]1 & 01[1] => [011]
        structure <<= 1;
        left_splits &= &structure;

        // reset
        structure >>= 2;
        let mut current_shift = 0;

        // moving from right to left
        loop {
          let trailing = left_splits.trailing_zeros();
          if let 1 = left_splits.count_ones() {
            break 'find_offset trailing - 1;
          }

          structure >>= trailing - current_shift;

          if (structure.bits() + 1).wrapping_sub(structure.count_ones() * 2) == 0 {
            break 'find_offset trailing;
          }

          // clear right most candidate
          left_splits ^= U512::ONE << trailing;
          current_shift = trailing;
        }
      };
      core::num::NonZeroU32::new(offset)
    }
  }

  // this is for the unbounded case
  pub(crate) mod big_uint {
    use crate::*;
    pub(crate) fn left_branch(mut structure: BigUint) -> Option<core::num::NonZeroU64> {
      let offset = 'find_offset: {
        if structure.count_ones() <= 1 {
          break 'find_offset 0;
          // return BigUint::ZERO;
        }
        if structure.bit(1) && !structure.bit(0) {
          // return BigUint::from(0b100_u32);
          break 'find_offset 2;
        }

        /* 011 bit pattern represents a "non-trivial" split, where 0 is the left node
           the bit one past the end will always be a "non-trivial" split
        */
        let u_0b1 = BigUint::from(1_u32);

        let mut left_splits = &u_0b1 << structure.bits() + 1;

        // [0]11
        left_splits -= &u_0b1;
        left_splits ^= &structure;

        // [0]11 & 0[1]1 => [01]1
        structure <<= 1;
        left_splits &= &structure;

        // [01]1 & 01[1] => [011]
        structure <<= 1;
        left_splits &= &structure;

        // reset
        structure >>= 2;
        let mut current_shift = 0;

        // moving from right to left
        loop {
          let trailing = left_splits.trailing_zeros().expect("TRAILING ZEROS");

          if let 1 = left_splits.count_ones() {
            break 'find_offset trailing - 1;
          }
          // return u_0b1 << trailing-1 }

          structure >>= trailing - current_shift;

          if (structure.bits() + 1).wrapping_sub(structure.count_ones() * 2) == 0 {
            break 'find_offset trailing;
            // return u_0b1<<trailing;
          }

          // clear right most candidate
          left_splits.set_bit(trailing as u64, false);
          current_shift = trailing;
        }
      };
      core::num::NonZeroU64::new(offset)
    }
  }
}

type Int = u32;

// only run this test if Int is u8, u16, or u32
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

#[test]
fn test_for_u64() {
  let trees = all_trees();
  std::println!("count : {}", all_trees().len());
  let now = std::time::Instant::now();
  for each in trees {
    // std::print!("{each:032b}\t{:016b}\n",
    core::hint::black_box(left_branch_impl::u64::left_branch(each as u64))
      // )
      ;
  }
  std::println!("time : {} micros", now.elapsed().as_micros())
}
#[test]
fn test_for_biguint() {
  let trees = all_trees();
  let now = std::time::Instant::now();
  for each in trees {
    // std::print!("{each:032b}\t{:?}\n",
    core::hint::black_box(
          left_branch_impl::big_uint::left_branch(BigUint::from(each))
      )
      // )
      ;
  }
  std::println!("time : {} micros", now.elapsed().as_micros())
}
#[test]
fn test_for_u512() {
  let trees = all_trees();
  let now = std::time::Instant::now();
  for each in trees {
    // std::print!("{each:032b}\t{}\n",
    core::hint::black_box(
          left_branch_impl::u512::left_branch(bnum::types::U512::from_digit(each as u64))
      )
      // )
      ;
  }
  std::println!("time : {} micros", now.elapsed().as_micros())
}



#[test]
fn test_zipper_basics() {
  type DSZ = DyckStructureZipperU64;

  ///////
  // 0b_0
  ///////
  std::println!("\n# 0b_0\nNone");
  core::assert!( core::matches!( DSZ::new(0b_0), Option::None) );
  
  '_0b_1:{
    std::println!("\n# 0b_1\n");
    let mut tree_0b_1 = DSZ::new(0b_1).unwrap();
    let count = tree_0b_1.structure.count_ones() as usize;
    std::println!("{:#?}", tree_0b_1);
    // no parent
    core::assert!(!tree_0b_1.accend());
    // no children
    core::assert!(!tree_0b_1.decend_left());
    core::assert!(!tree_0b_1.decend_right());
    // no branching
    core::assert!(!tree_0b_1.switch_left());
    core::assert!(!tree_0b_1.switch_right());
    // single element
    core::assert_eq!(tree_0b_1.current_first_leaf_store_index(), 0);
    core::assert_eq!(tree_0b_1.current_leaf_store_index_range(), 0..count);
  }

  '_0b_110:{
    std::println!("\n# 0b_110\n");
    let mut tree_0b_110 = DSZ::new(0b_110).unwrap();
    let count = tree_0b_110.structure.count_ones() as usize;
    std::println!("{:#?}", tree_0b_110);

    // at root
    core::assert!(!tree_0b_110.switch_left());
    core::assert!(!tree_0b_110.switch_right());
    core::assert_eq!(tree_0b_110.current_first_leaf_store_index(), 0);
    core::assert_eq!(tree_0b_110.current_leaf_store_index_range(), 0..count);
    core::assert!(!tree_0b_110.accend());

    // cycle counterclockwise
    core::assert!(tree_0b_110.decend_left());
    core::assert_eq!(tree_0b_110.current_first_leaf_store_index(), 0);
    core::assert_eq!(tree_0b_110.current_leaf_store_index_range(), 0..1);
    core::assert!(tree_0b_110.switch_right());
    core::assert_eq!(tree_0b_110.current_first_leaf_store_index(), 1);
    core::assert_eq!(tree_0b_110.current_leaf_store_index_range(), 1..count);
    core::assert!(tree_0b_110.accend());

    // back to root
    core::assert_eq!(tree_0b_110.current_leaf_store_index_range(), 0..count);

    // cycle clockwise
    core::assert!(tree_0b_110.decend_right());
    core::assert_eq!(tree_0b_110.current_first_leaf_store_index(), 1);
    core::assert_eq!(tree_0b_110.current_leaf_store_index_range(), 1..count);
    core::assert!(tree_0b_110.switch_left());
    core::assert_eq!(tree_0b_110.current_first_leaf_store_index(), 0);
    core::assert_eq!(tree_0b_110.current_leaf_store_index_range(), 0..1);
    core::assert!(tree_0b_110.accend());
  }
  
  '_0b_11010:{
    std::println!("\n# 0b_11010\n");
    let mut tree_0b_11010 = DSZ::new(0b_11010).unwrap();
    let count = tree_0b_11010.structure.count_ones() as usize;
    std::println!("{:#?}", tree_0b_11010);

    // at root
    core::assert!(!tree_0b_11010.switch_left());
    core::assert!(!tree_0b_11010.switch_right());
    core::assert_eq!(tree_0b_11010.current_first_leaf_store_index(), 0);
    core::assert_eq!(tree_0b_11010.current_leaf_store_index_range(), 0..count);
    core::assert!(!tree_0b_11010.accend());

    // visit each, right to left
    core::assert!(tree_0b_11010.decend_right());
    std::println!("{:#?}", tree_0b_11010);
    core::assert!(!tree_0b_11010.decend_left());
    core::assert_eq!(tree_0b_11010.current_first_leaf_store_index(), 2);
    core::assert_eq!(tree_0b_11010.current_leaf_store_index_range(), 2..count);
    core::assert!(!tree_0b_11010.decend_right());

    core::assert!(tree_0b_11010.switch_left());
    std::println!("{:#?}", tree_0b_11010);

    core::assert!(tree_0b_11010.decend_right());
    std::println!("{:#?}", tree_0b_11010);
    core::assert!(!tree_0b_11010.decend_left());
    core::assert_eq!(tree_0b_11010.current_first_leaf_store_index(), 1);
    core::assert_eq!(tree_0b_11010.current_leaf_store_index_range(), 1..2);
    core::assert!(!tree_0b_11010.decend_right());

    core::assert!(tree_0b_11010.switch_left());
    std::println!("{:#?}", tree_0b_11010);
    core::assert!(!tree_0b_11010.decend_left());

    core::assert_eq!(tree_0b_11010.current_first_leaf_store_index(), 0);
    core::assert_eq!(tree_0b_11010.current_leaf_store_index_range(), 0..1);
  }

  
}

