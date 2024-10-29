mod left_branch_tests;

pub(crate) mod u64 {
  extern crate core;
  

  /// Finds the bit location of the head of the left branch.
  /// If there is no left branch, no bit will be set.
  /// If one would like to get the position as an index, take the return value and use `.trailing_zeros()`
  pub(crate) fn left_branch(structure: u64) -> u64 {
    // the tree has a single element, there is no left branch
    if structure <= 1 {
      return 0;
    }
    // the right branch is a leaf
    if 0b10 & structure == 0b10 {
      return 0b100;
    }
    // looking for all locations of bit pattern `011`, the 0 is candidate location of a left branch
    let mut left_splits = !structure & structure << 1 & structure << 2;
    loop {
      let trailing = left_splits.trailing_zeros();
      core::debug_assert!(trailing < 64, "structure {structure:064b}");
      let current = 1 << trailing;
      if let 1 = left_splits.count_ones() {
        return current >> 1;
      }
      let tmp = structure >> trailing;
      if (u64::BITS - tmp.leading_zeros() + 1).wrapping_sub(tmp.count_ones() * 2) == 0 {
        return current;
      }
      // remove candidate
      left_splits ^= current;
    }
  }
}

// we might be interested in testing the 512 fixed size, as that makes for 256 leaves max, which means the backing Vec can be indexed by a byte.
// unfortunately, this appears to be as slow as the unbounded version, likely due to a subpar implementation on the U512 type if the issue is the same as Adam had.
// It currently used the version of the algorithim that the unbounded one uses as it is a tad faster
#[allow(unused)]
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
#[allow(unused)]
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
