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



pub trait DyckPathFindLeftBranch where usize : From<Self::Offset>{
  type Offset;  
  fn left_branch(self) -> Self::Offset;
}

// this can be refactored to be less repitive, but then I would have to use some traits, I'm avoiding the complexity for now
pub(crate) mod left_branch_impl {
  macro_rules! left_branch {($($INT:ident)+) => {$(
    pub(crate)mod $INT {
      pub(crate)fn left_branch(mut structure: $INT) -> $INT {
        if structure<=1 { return 0;}

        if 0b10 & structure == 0b10 {
          return 0b100;
        }

        /* 011 bit pattern represents a "non-trivial" split, where 0 is the left node
           the bit one past the end will always be a "non-trivial" split,
        */
        let mut left_splits = !structure & structure << 1 & structure << 2;
      
        // moving from right to left
        loop {
          let trailing = left_splits.trailing_zeros();
          let current = 1<<trailing;
          if let 1 = left_splits.count_ones() { return current >> 1 }
          let tmp = structure >> trailing;
          
          if ($INT::BITS-tmp.leading_zeros() + 1).wrapping_sub(tmp.count_ones() * 2) == 0 {
            return current;
          }
          
          // clear right most candidate
          left_splits ^= current;
          
        }
      }
    }
  )+};}
  left_branch! {u8 u16 u32 u64 u128 usize}

  // we might be interested in testing the 512 fixed size, as that makes for 256 leaves max, which means the backing Vec can be indexed by a byte.
  // unfortunately, this appears to be as slow as the unbounded version, likely due to a subpar implementation on the U512 type if the issue is the same as Adam had.
  // It currently used the version of the algorithim that the unbounded one uses as it is a tad faster
  pub(crate) mod u512 {
    use crate::*;
    pub(crate) use bnum::types::U512;
    
    pub(crate) fn left_branch(mut structure: U512) -> Option<core::num::NonZeroU32> {
      let offset = 'find_offset : {

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
        
        let mut left_splits = U512::ONE << structure.bits()+1;
        
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
          if let 1 = left_splits.count_ones() { break 'find_offset trailing- 1 }
          
          structure >>= trailing - current_shift;
          
          if (structure.bits() + 1).wrapping_sub(structure.count_ones() * 2) == 0 {
            break 'find_offset trailing;
          }
          
          // clear right most candidate
          left_splits ^= U512::ONE<<trailing;
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
      let offset = 'find_offset : {
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
  
      let mut left_splits = &u_0b1 << structure.bits()+1;

      // [0]11
      left_splits -= &u_0b1;
      left_splits ^= &structure; 
      
      // [0]11 & 0[1]1 => [01]1
      structure <<= 1;
      left_splits &= & structure; 

      // [01]1 & 01[1] => [011]
      structure <<= 1;
      left_splits &= & structure;
      
      // reset
      structure >>= 2;
      let mut current_shift = 0;

      // moving from right to left
      loop {
        let trailing = left_splits.trailing_zeros().expect("TRAILING ZEROS");
        
        if let 1 = left_splits.count_ones() { 
        break 'find_offset trailing-1 }
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
      // std::print!("{each:016b}\t{:016b}\n", 
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
      // std::print!("{each:016b}\t{}\n", 
        core::hint::black_box(
          left_branch_impl::u512::left_branch(bnum::types::U512::from_digit(each as u64))
      )
      // )
      ;
    }
  std::println!("time : {} micros", now.elapsed().as_micros())
}
