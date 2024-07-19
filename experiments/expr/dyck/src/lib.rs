#![no_implicit_prelude]
// #![allow(unused)]

extern crate alloc;
extern crate core;
extern crate std;

extern crate bnum;
extern crate num_bigint;

use alloc::{boxed::Box, collections::BTreeMap, vec::Vec};
#[allow(unused_imports)]
use core::iter::Extend;
use core::{
  clone::Clone,
  cmp::Ord,
  convert::From,
  default::Default,
  iter::{IntoIterator, Iterator},
  ops::FnMut,
  option::Option,
  result::Result,
};
use std::fmt::{Debug, Display};
use num_bigint::BigUint;

mod finite;

/// It should be noted that the terminal is _NEVER_ equal to the head.
/// In the case of a leaf, the head is at the leaf position, and the terminal is one after it.
/// In other words, if t is the terminal, and h is the head, then
/// for a tree `0...001` we have `0..0th` (_t_=1, _h_=0),
///
/// example
/// - `0..0t____h` (_t_=5, _h_=0) tree `0..0011010`
/// - `0..0t__h__` (_t_=5, _h_=2) the left sub tree         
/// - `0..0___th_` (_t_=2, _h_=1) the right sub tree (a leaf)
#[derive(Clone, Copy)]
pub(crate) struct SubtreeSlice {
  /// the position right after the last leaf of a subtree.
  pub(crate) terminal: u8,
  /// the position of the subtree (the root is a subtree of itself)
  pub(crate) head: u8,
}
/// this is used exclusively for initializing data.
impl SubtreeSlice {
  const fn zeroes() -> Self {
    Self { terminal: 0, head: 0 }
  }
  fn is_leaf(&self) -> bool {
    1 == self.terminal - self.head
  }
  fn left_subtree_head(self, structure: u64) -> u64 {
    let slice = (structure & (0b_10_u64 << self.terminal - 1).wrapping_sub(1)) >> self.head;

    left_branch_impl::u64::left_branch(slice) << self.head
  }
}

#[derive(Clone)]
pub struct DyckStructureZipperU64 {
  structure: u64,
  current_depth: u8,
  stack: [SubtreeSlice; DyckStructureZipperU64::MAX_LEAVES],
}

impl core::fmt::Debug for DyckStructureZipperU64 {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    core::write!(
      f,
      "\
        DyckStructureZipperU64 {{\
        \n  structure     : {:b},\
        \n  current_depth : {},\
        \n  stack         : [ ",
      self.structure,
      self.current_depth
    )?;
    for each in &self.stack[..=self.current_depth as usize] {
      core::write!(f, "\n\t{{ term:{}, head:{} }} => ", each.terminal, each.head)?;
      for _ in 0..u64::BITS as u8 - each.terminal {
        core::write!(f, "_")?
      }
      core::write!(f, "{:b}", (self.structure & ((1 << each.terminal) - (1 << each.head))) >> each.head)?;
      for _ in 0..each.head {
        core::write!(f, "_")?
      }
      core::write!(f, ",")?
    }

    core::writeln!(f, "\n  ],\n}}")
  }
}

impl DyckStructureZipperU64 {
  const MAX_LEAVES: usize = u64::BITS as usize / 2;

  /// Creates a Zipper for the Dyck Path, if the tree is empty (Dyck path of all 0s), it will return [`Option::None`]; this avoids uneeded checks when traversing.
  /// A valid Zipper is therefore always on a non-empty tree.
  /// Validating the structure of a Zipper is costly, so it is only checked in debug builds (TODO: is there a fast algorithm for doing the check using bit shifts and masks?).
  pub fn new(structure: u64) -> Option<Self> {
    if let 0 = structure {
      return Option::None;
    }

    #[cfg(debug_assertions)]
    '_validate_structure: {
      let trailing = structure.leading_zeros();
      core::debug_assert_ne!(trailing, 0);

      let mut cursor = 1 << u64::BITS - trailing - 1;
      let mut sum: i32 = 0;

      // a valid structure must have enough children to pair up before constructing a branch
      loop {
        core::debug_assert!(!sum.is_negative());
        if cursor == 0 {
          core::debug_assert_eq!(1, sum);
          break;
        }

        sum += if (cursor & structure) == 0 { -1 } else { 1 };
        cursor >>= 1;
      }
    }

    let mut stack = [SubtreeSlice::zeroes(); Self::MAX_LEAVES];
    stack[0].terminal = (u64::BITS).wrapping_sub(structure.leading_zeros()) as u8;

    Option::Some(Self { structure, current_depth: 0, stack })
  }

  /// Decend to the left child if there is one.
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

  /// Decend to the right child if there is one.
  pub fn decend_right(&mut self) -> bool {
    if self.decend_left() {
      unsafe { self.switch_right_unchecked() };
      true
    } else {
      false
    }
  }

  /// Switch from a left branch to the sibling right branch. Invariants are enfored in debug builds.
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
  /// Switch from a left branch to the sibling right branch.
  pub fn switch_right(&mut self) -> bool {
    let Self { structure, current_depth, stack } = self;
    if *structure <= 1 || 0 == *current_depth {
      return false;
    }

    // Safety: The current depth is > 0
    let prev = unsafe { stack.get_unchecked(*current_depth as usize - 1) };
    let cur = unsafe { stack.get_unchecked(*current_depth as usize) };

    // avoid double right
    if prev.head == cur.head - 1 {
      return false;
    }

    unsafe { self.switch_right_unchecked() }

    true
  }
  /// check if the current branch is a left branch. The root is never a left branch.
  pub fn current_is_left_branch(&self) -> bool {
    let Self { current_depth, stack, .. } = self;

    if let 0 = current_depth {
      return false;
    }

    let prev = stack[*current_depth as usize - 1];
    let cur = stack[*current_depth as usize];
    prev.terminal == cur.terminal && prev.head != cur.head - 1
  }

  /// Switch from a right branch to the sibling left branch. Invariants are enfored in debug builds.
  pub unsafe fn switch_left_unchecked(&mut self) {
    let Self { structure, current_depth, stack } = self;
    core::debug_assert!(!core::matches!(*structure, 0 | 1));
    core::debug_assert_ne!(*current_depth, 0);

    let prev = unsafe { *stack.get_unchecked(*current_depth as usize - 1) };
    let cur = unsafe { stack.get_unchecked_mut(*current_depth as usize) };

    // not left
    core::debug_assert_ne!(prev.terminal, cur.terminal);
    // is right
    core::debug_assert_eq!(prev.head, cur.head - 1);

    *cur = SubtreeSlice { terminal: prev.terminal, head: cur.terminal };
  }
  /// Switch from a right branch to the sibling left branch.
  pub fn switch_left(&mut self) -> bool {
    let Self { structure, current_depth, stack } = self;
    if *structure <= 1 || 0 == *current_depth {
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

  /// Finds the index of the leaf that is at the bit offset `tree_offset`.
  /// If this function is used on a branch bit (a zero bit) it will instead find the right most leaf of that branch,
  /// and if the position is past the end of the last leaf it will create an index out of bounds; both of these cases should not be relied upon, and will panic in debug builds.
  pub unsafe fn leaf_store_index_unchecked(&self, tree_offset: u8) -> usize {
    core::assert_ne!(self.structure & 1 << tree_offset as u32, 0, "zipper :\n{:?}\ntree_offset : {}", self, tree_offset);
    (self.structure & !((0b_10 << tree_offset as u32) - 1)).count_ones() as usize
  }

  /// Produce the range of indices that can be used to subslice the store of leaf elements.
  pub fn current_leaf_store_index_range(&self) -> core::ops::Range<usize> {
    unsafe {
      let cur = self.stack.get_unchecked(self.current_depth as usize);
      let right = ((self.structure ^ self.structure & ((0b_1 << (cur.head as u32)) - 1)).trailing_zeros() as u8).min(cur.terminal - 1);

      let first = self.leaf_store_index_unchecked(cur.terminal - 1);
      let last = self.leaf_store_index_unchecked(right);

      first..last.max(first) + 1
    }
  }

  /// Index of the first leaf in the current scope
  pub fn current_first_leaf_store_index(&self) -> usize {
    unsafe {
      let cur = self.stack.get_unchecked(self.current_depth as usize);
      self.leaf_store_index_unchecked(cur.terminal - 1)
    }
  }

  /// Move up to the parent.
  pub fn accend(&mut self) -> bool {
    if self.current_depth == 0 {
      return false;
    }
    self.current_depth -= 1;
    true
  }

  /// Move to the top of the tree, setting current depth to 0.
  pub fn accend_to_root(&mut self) {
    self.current_depth = 0;
  }

  /// Move up the tree `n` times.
  pub fn accend_n(&mut self, n: u8) -> bool {
    if self.current_depth < n {
      return false;
    }
    self.current_depth -= n;
    true
  }

  /// Determines if the focus of the zipper is at a leaf.
  pub fn current_is_leaf(&self) -> bool {
    self.stack[self.current_depth as usize].is_leaf()
  }

  /// Produce an iterator that generates the indices of the leaves in depth first traversal order
  pub fn current_depth_first_indicies(&self) -> impl Iterator<Item = usize> + core::marker::Send + core::marker::Sync + 'static {
    self.current_leaf_store_index_range()
  }

  /// Produce an iterator that generates the indices of the leaves in breadth first traversal order
  pub fn current_breadth_first_indicies(&self) -> impl Iterator<Item = usize> + core::marker::Send + core::marker::Sync + 'static {
    const MAX_DEFERED: usize = DyckStructureZipperU64::MAX_LEAVES;

    // the iterator state
    let mut tmp = Self { structure: self.structure, current_depth: 0, stack: [SubtreeSlice::zeroes(); Self::MAX_LEAVES] };
    let mut ring_buffer = [SubtreeSlice::zeroes(); MAX_DEFERED];
    let mut front = 0;
    let mut end = 1;
    ring_buffer[0] = self.stack[self.current_depth as usize];

    // the iterator
    core::iter::from_fn(move || {
      loop {
        if front == end {
          break Option::None;
        }

        // dequeue
        tmp.accend_to_root();
        tmp.stack[0] = ring_buffer[front];
        front = (front + 1) % MAX_DEFERED;

        if tmp.decend_left() {
          // enqueue left
          ring_buffer[end] = tmp.stack[1];
          end = (end + 1) % MAX_DEFERED;

          unsafe { tmp.switch_right_unchecked() };

          // enqueue right
          ring_buffer[end] = tmp.stack[1];
          end = (end + 1) % MAX_DEFERED;
        } else {
          break Option::Some(unsafe { tmp.leaf_store_index_unchecked(tmp.stack[0].head) });
        }
      }
    })
  }

  /// Obtain the current subtree Dyck path.
  pub fn current_substructure(&self) -> u64 {
    let SubtreeSlice { terminal, head } = self.stack[self.current_depth as usize];
    ((1 << terminal) - 1 & self.structure) >> head
  }

  /// Match the self argument with the pattern. As Zippers must have at least one element, an empty template should have [`Option::None`] as the template argument with the template data being `&[]`
  pub fn match_template_at_current<E: MatchElement>(&self, self_data: &[E::Element], pattern: &Self, pattern_data: &[E::Element], template: Option<&Self>, template_data: &[E::Element]) -> Option<(Vec<LeafBranch>, Vec<E::Element>)>
  where
    E::Element: Clone,
  {
    core::debug_assert_eq!(self.structure.count_ones() as usize, self_data.len());
    core::debug_assert_eq!(pattern.structure.count_ones() as usize, pattern_data.len());

    // initialize zippers
    type DZ = DyckStructureZipperU64;
    const NULL_ZIPPER: DZ = DZ { structure: 0, current_depth: 0, stack: [SubtreeSlice::zeroes(); DZ::MAX_LEAVES] };
    fn init_sub_zipper(z: &DZ) -> DZ {
      let mut z1 = DZ { structure: z.structure, ..NULL_ZIPPER };
      z1.stack[0] = z.stack[z.current_depth as usize];
      z1
    }

    let maybe_template_z = if let Option::Some(t) = template {
      core::debug_assert_eq!(t.structure.count_ones() as usize, template_data.len());
      Option::Some(init_sub_zipper(t))
    } else {
      core::debug_assert_eq!(0, template_data.len());
      Option::None
    };
    let [mut self_z, mut pattern_z] = [self, pattern].map(init_sub_zipper);

    // initialize substitution table
    let mut de_bruin_level_offset: Option<usize> = Option::None;
    let mut de_bruin_offset_bindings_to_self = [Option::None; Self::MAX_LEAVES];

    // dfs the pattern and follow along with the argument
    'matching: loop {
      if pattern_z.current_is_leaf() {
        match E::element_type(&pattern_data[pattern_z.current_first_leaf_store_index()]) {
          ElementType::Atom(pat_atom) => {
            if !self_z.current_is_leaf() {
              return Option::None;
            }
            match E::element_type(&self_data[self_z.current_first_leaf_store_index()]) {
              ElementType::Atom(self_atom) => {
                if !E::atom_eq(self_atom, pat_atom) {
                  return Option::None;
                }
              }
              ElementType::Var(_) => core::unimplemented!("This matching algoritm does not do unification!"),
              ElementType::Hole => {}
            }
          }
          ElementType::Var(v) => {
            // bind pattern variables, new variables must have a higher de Bruin level
            let level = E::var_de_bruin_level(v);
            match de_bruin_level_offset {
              Option::None => de_bruin_level_offset = Option::Some(level),

              Option::Some(offset) => core::debug_assert!(offset <= level),
            }
            let idx = level - de_bruin_level_offset.unwrap_or(0);
            de_bruin_offset_bindings_to_self[idx] = Option::Some(self_z.stack[self_z.current_depth as usize]);
          }
          ElementType::Hole => {}
        }

        '_pop: {
          while !pattern_z.current_is_left_branch() {
            if pattern_z.accend() {
              self_z.accend();
            } else {
              break 'matching;
            }
          }

          // Safety: the reaching the end of the while loop
          //   guarantees that we are on a left branch, so there must be a right branch
          unsafe {
            pattern_z.switch_right_unchecked();
            self_z.switch_right_unchecked();
          };
        }
      } else {
        // current is a branch
        let both_left = self_z.decend_left() && pattern_z.decend_left();
        if !both_left {
          return Option::None;
        }
      }
    }

    let Option::Some(mut template_z) = maybe_template_z else {
      return Option::Some((Vec::new(), Vec::new()));
    };

    // construct from the template
    let mut structure = Vec::with_capacity(32);
    let mut values = Vec::with_capacity(32);

    self_z.accend_to_root();

    let out = 'templating: loop {
      if template_z.decend_left() {
        continue 'templating;
      }

      let e = &template_data[template_z.current_first_leaf_store_index()];
      match E::element_type(e) {
        ElementType::Atom(_) | ElementType::Hole => '_push_atom: {
          values.push(e.clone());
          structure.push(LeafBranch::L)
        }
        ElementType::Var(v) => '_push_binding: {
          let level = E::var_de_bruin_level(v);
          let Option::Some(offset) = de_bruin_level_offset else { core::panic!() };
          let Option::Some(binding) = de_bruin_offset_bindings_to_self[level - offset] else { core::panic!() };

          self_z.stack[0] = binding;

          let indices = self_z.current_leaf_store_index_range();
          values.extend_from_slice(&self_data[indices]);

          let sub_structure = self_z.structure >> binding.head;
          let mut bit_ptr = 1_u64 << binding.terminal - binding.head - 1;

          '_convert_subtree_structure: while bit_ptr != 0 {
            structure.push(if bit_ptr & sub_structure == 0 { LeafBranch::B } else { LeafBranch::L });
            bit_ptr >>= 1;
          }
        }
      }

      '_pop: while !template_z.switch_right() {
        if !template_z.accend() {
          core::debug_assert_eq!(structure.iter().filter(|s| **s == LeafBranch::L).count(), values.len());
          break 'templating Option::Some((structure, values));
        }
        structure.push(LeafBranch::B);
      }
    };

    out
  }
}

/// Represents a stack machine instruction for
/// building a binary tree in DFS order
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LeafBranch {
  /// Leaf
  L,
  /// Branch
  B,
}

/// An ephemeral Data Structure used to dispatch on element types in an Expr
/// Exists only for the trait [`MatchElement`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ElementType<'e, A, V> {
  /// Represents a single concrete value that is not a compound value
  Atom(&'e A),
  /// Variable that was introduced by a "transform"/"lambda";
  /// the de Bruin level is encoded in this value.
  Var(&'e V),
  /// An variable empty binding, matches anything
  Hole,
}
/// Trait interface for doing basic pattern matching
pub trait MatchElement {
  type Element;
  type Atom;
  type Var;
  /// Inspects an element to determine if it is an atom or a variable to be bound.
  fn element_type(e: &Self::Element) -> ElementType<Self::Atom, Self::Var>;
  /// Atoms that are considered equal are determined to match.
  fn atom_eq(left: &Self::Atom, right: &Self::Atom) -> bool;
  /// Variables of the same debruin index are determined to match.
  fn var_de_bruin_level(left: &Self::Var) -> usize;
}

pub(crate) mod left_branch_impl {
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
  core::assert!(core::matches!(DSZ::new(0b_0), Option::None));

  '_0b_1: {
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

  '_0b_110: {
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

  '_0b_11010: {
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

#[test]
fn test_zipper_traversal() {
  type DSZ = DyckStructureZipperU64;
  let tree_0b_110110010 = DSZ::new(0b_11010110010).unwrap();

  tree_0b_110110010
    .current_depth_first_indicies()
    .zip(0..tree_0b_110110010.structure.count_ones() as usize)
    .for_each(|(l, r)| core::assert_eq!(l, r));
  tree_0b_110110010.current_breadth_first_indicies().zip([5, 2, 3, 4, 0, 1].into_iter()).for_each(|(l, r)| core::assert_eq!(l, r));
}

#[test]
fn test_zipper_breadth_and_depth_first_traversal_perf() {
  let trees = all_trees();
  let mut idxs = Vec::with_capacity(32);
  let total_indicies = trees.iter().fold(0_u64, |acc, x| acc + x.count_ones() as u64);
  std::println!("number of trees {}\ntotal indicies {}\nperf test begin", trees.len(), total_indicies);
  let mut now = std::time::Instant::now();
  for each in trees.iter().copied().skip(1) {
    let z = DyckStructureZipperU64::new(each as u64).unwrap();

    idxs.extend(z.current_breadth_first_indicies());
    // std::println!("{each:032b}\t{:?}\n", idxs);
    idxs.clear();
  }
  let time = now.elapsed();
  std::println!("Breadth first all 16 element trees or less\n\ttime : {} micros", time.as_micros());
  core::assert!(time.as_nanos() as f64 / (total_indicies as f64) < 100.0);

  now = std::time::Instant::now();

  for each in trees.iter().copied().skip(1) {
    let z = DyckStructureZipperU64::new(each as u64).unwrap();

    idxs.extend(z.current_depth_first_indicies());
    // std::println!("{each:032b}\t{:?}\n", idxs);
    idxs.clear();
  }
  let time = now.elapsed();
  std::println!("Depth first all 16 element trees or less\n\ttime : {} micros", time.as_micros());
  core::assert!(time.as_nanos() as f64 / (total_indicies as f64) < 100.0);

  // now for all symmetric trees
  let trees2 = trees.iter().copied().skip(1).map(|x| x as u64).map(|l| ((l << u64::BITS - l.leading_zeros()) | l) << 1);
  std::println!("\nperf test symetric begin");
  let (mut min, mut max) = (u128::MAX, u128::MIN);
  let now = std::time::Instant::now();
  for each in trees2 {
    let now_inner = std::time::Instant::now();
    let z = DyckStructureZipperU64::new(each as u64).unwrap();

    idxs.extend(z.current_breadth_first_indicies());
    // std::println!("{each:032b}\t{:?}\n", idxs);

    let time = now_inner.elapsed().as_nanos();
    min = min.min(time / (idxs.len() as u128 + 1));
    max = max.max(time / (idxs.len() as u128 + 1));

    idxs.clear();
  }
  let time = now.elapsed();
  std::println!("Breadth first all duplicated 32 leaf trees or less\ntime : {} micros", time.as_micros());
  std::println!("\nmax time : {} nanos, min time : {} nanos", max, min);
  core::assert!(time.as_nanos() as f64 / (2.0 * total_indicies as f64) < 100.0);

  // now for all symmetric trees
  let trees2 = trees.iter().copied().skip(1).map(|x| x as u64).map(|l| ((l << u64::BITS - l.leading_zeros()) | l) << 1);
  std::println!("\nperf test duplicated trees begin");
  let (mut min, mut max) = (u128::MAX, u128::MIN);
  let now = std::time::Instant::now();
  for each in trees2 {
    let now_inner = std::time::Instant::now();
    let z = DyckStructureZipperU64::new(each as u64).unwrap();

    idxs.extend(z.current_depth_first_indicies());
    // std::println!("{each:032b}\t{:?}\n", idxs);

    let time = now_inner.elapsed().as_nanos();
    min = min.min(time / (idxs.len() as u128 + 1));
    max = max.max(time / (idxs.len() as u128 + 1));

    idxs.clear();
  }
  let time = now.elapsed();
  std::println!("Depth first all duplicated 32 leaf trees or less\ntime : {} micros", time.as_micros());
  std::println!("\nmax time : {} nanos, min time : {} nanos", max, min);
  core::assert!(time.as_nanos() as f64 / (2.0 * total_indicies as f64) < 100.0);
}

#[test]
fn test_naive_matching() {
  use LeafBranch::{B, L};

  #[derive(Debug, Clone, PartialEq, Eq)]
  enum E {
    A(&'static str),
    V(isize),
    Hole,
  }

  enum TestExpr {}
  #[cfg_attr(rustfmt, rustfmt::skip)]
  impl MatchElement for TestExpr {
    type Element = E;
    type Atom = &'static str;
    type Var = isize;
  
    fn element_type(e: &Self::Element) -> ElementType<Self::Atom, Self::Var> {
      match e {
        E::A(a) => ElementType::Atom(a),
        E::V(v) => ElementType::Var(v),
        E::Hole => ElementType::Hole,
      }
    }
  
    fn atom_eq(left: &Self::Atom, right: &Self::Atom) -> bool { left == right }
    fn var_de_bruin_level(left: &Self::Var) -> usize { *left as usize }
  }

  // ((a $0) (b c))
  let input_zipper = DyckStructureZipperU64::new(0b_110_110_0).unwrap();
  let input_data = [E::A("a"), E::V(0), E::A("b"), E::A("c")];
  let pattern_zipper = DyckStructureZipperU64::new(0b_110_10).unwrap();
  let pattern_data = [E::A("a"), E::Hole, E::V(1)];
  let template_zipper = DyckStructureZipperU64::new(0b_110).unwrap();
  let template_data = [E::A("x"), E::V(1)];

  let result = DyckStructureZipperU64::match_template_at_current::<TestExpr>(&input_zipper, &input_data, &pattern_zipper, &pattern_data, Option::Some(&template_zipper), &template_data).unwrap();

  let expected_structure = [L, L, L, B, B];
  let expected_data = [E::A("x"), E::A("b"), E::A("c")];

  core::assert_eq!(&result.0[..], &expected_structure[..]);
  core::assert_eq!(&result.1[..], &expected_data[..]);

  // simple point matching

  // (Point2d ((X 15.4) (Y -34.9)))
  let input_zipper = DyckStructureZipperU64::new(0b_1_1101100_0).unwrap();
  #[cfg_attr(rustfmt, rustfmt::skip)]
  let input_data = [
    "Pointed2d", "X", "15.4", 
                 "Y", "-34.9"
  ].map(E::A);
  // (Point2d ((X x) (Y x)))
  let pattern_zipper = DyckStructureZipperU64::new(0b_1_1101100_0).unwrap();
  #[cfg_attr(rustfmt, rustfmt::skip)]
  let mut pattern_data = [
    "Pointed2d", "X", "x",
                 "Y", "y"
  ].map(E::A);
  pattern_data[2] = E::V(0);
  pattern_data[4] = E::V(1);

  // (Sqrt (+ ( (* (x x))
  //            (* (y y)) )))
  let template_zipper = DyckStructureZipperU64::new(0b_11_11100_11100_000).unwrap();
  #[cfg_attr(rustfmt, rustfmt::skip)]
  let mut template_data = [
    "Sqrt","+","*","x","x",
               "*","y","y"
  ].map(E::A);

  template_data[3] = E::V(0);
  template_data[4] = E::V(0);

  template_data[6] = E::V(1);
  template_data[7] = E::V(1);

  let result = DyckStructureZipperU64::match_template_at_current::<TestExpr>(&input_zipper, &input_data, &pattern_zipper, &pattern_data, Option::Some(&template_zipper), &template_data).unwrap();

  let expected_structure = [L, L, L, L, L, B, B, L, L, L, B, B, B, B, B];
  #[cfg_attr(rustfmt, rustfmt::skip)]
  let expected_data = [
    "Sqrt","+","*", "15.4", "15.4",
               "*","-34.9","-34.9"
    ].map(E::A);

  core::assert_eq!(&result.0[..], &expected_structure[..]);
  core::assert_eq!(&result.1[..], &expected_data[..]);

  // expression point matching

  // (Point2d ((X (+ (3.0 2.2))) (Y -34.9)))
  let input_zipper = DyckStructureZipperU64::new(0b_1__1111000_110_0__0).unwrap();
  #[cfg_attr(rustfmt, rustfmt::skip)]
  let input_data = [
    "Pointed2d", "X", "+", "3.0", 
                           "2.2", 
                 "Y", "-34.9"
  ].map(E::A);
  // (Point2d ((X x) (Y x)))
  let pattern_zipper = DyckStructureZipperU64::new(0b_1_1101100_0).unwrap();
  #[cfg_attr(rustfmt, rustfmt::skip)]
  let mut pattern_data = [
    "Pointed2d", "X", "x",
                 "Y", "y"
  ].map(E::A);
  pattern_data[2] = E::V(0);
  pattern_data[4] = E::V(1);

  // (Sqrt (+ ( (* (x x))
  //            (* (y y)) )))
  let template_zipper = DyckStructureZipperU64::new(0b_11_11100_11100_000).unwrap();
  #[cfg_attr(rustfmt, rustfmt::skip)]
  let mut template_data = [
    "Sqrt","+","*","x","x",
               "*","y","y"
  ].map(E::A);

  template_data[3] = E::V(0);
  template_data[4] = E::V(0);

  template_data[6] = E::V(1);
  template_data[7] = E::V(1);

  let result = DyckStructureZipperU64::match_template_at_current::<TestExpr>(&input_zipper, &input_data, &pattern_zipper, &pattern_data, Option::Some(&template_zipper), &template_data).unwrap();

  #[cfg_attr(rustfmt, rustfmt::skip)]
  let expected_structure = [
    L,L,  L, L,L,L,B,B,
             L,L,L,B,B, B,B,

          L, L,L,       B,B,
                             B,B,B];
  #[cfg_attr(rustfmt, rustfmt::skip)]
  let expected_data = ["Sqrt","+","*", "+", "3.0", "2.2",
                                       "+", "3.0", "2.2",
                                  "*","-34.9","-34.9"
  ].map(E::A);

  core::assert_eq!(&result.0[..], &expected_structure[..]);
  core::assert_eq!(&result.1[..], &expected_data[..]);
}
// struct FixSexpr(Sexpr<alloc::boxed::Box<FixSexpr>>);

#[derive(Debug, Clone, Copy)]
enum DeBruinLevel {
  Intro,
  Ref(core::num::NonZero<usize>)
}
#[derive(Debug)]
struct Variables {
  /// de bruin levels, but the indexing for the first variable starts at 1 instead of 0, 0 represents the introduction of a variable
  store: Vec<Sym>,
}
impl Variables {
  const MAX_LEVELS : usize = 33;
  fn new() -> Variables {
    Variables { store: Vec::from([Sym("")]) }
  }
  fn aquire_de_bruin(&mut self, sym : Sym)->DeBruinLevel {
   let mut idx = self.store.len();
   while idx != 0 {
     idx -= 1;
     if self.store[idx] == sym {
      // Safety: `idx` never enters the loop if it is equal to `0`
      return DeBruinLevel::Ref(unsafe {core::num::NonZeroUsize::new_unchecked(idx)});
     }
   }
   self.store.push(sym);
   DeBruinLevel::Intro
  }
  fn clear(&mut self) {
    self.store.clear();
    self.store.push(Sym(""))
  }
}

// if string interning is slow, it could be split into buckets, and use a ReadWrite lock, perhaps even Semaphores. but for testing this should be enough
static INTERNED_STR: std::sync::Mutex<alloc::collections::BTreeSet<&'static str>> = std::sync::Mutex::new(alloc::collections::BTreeSet::new());

// Sym is valid if it has an empty str, or if it holds and interned str.
#[derive(Debug, Clone, Copy, PartialOrd, Ord, Eq)]
pub struct Sym(pub &'static str);
impl Sym {
  fn new(s: &str) -> Sym {
    '_lock_scope: {
      let mut l = INTERNED_STR.lock().unwrap();
      if let Option::Some(&interned) = l.get(s) {
        return Sym(interned);
      }
      let s_static = <str as alloc::borrow::ToOwned>::to_owned(s).leak();
      l.insert(s_static);
      Sym(s_static)
    }
  }
}
impl core::cmp::PartialEq for Sym {
  fn eq(&self, other: &Self) -> bool {
    self.0.as_ptr() == other.0.as_ptr() || (self.0.len() | other.0.len() == 0)
  }
}

// enum SExpr_ {
//   Var(usize),
//   Atom(Sym),
//   App(App<Box<SExpr_>>),
// }

/// An empty enum to make recursive cases not constructable
#[derive(Debug)]
enum Void {}


#[derive(Clone,Copy,Debug)]
enum SExpr<A> {
  Var((DeBruinLevel,Sym)),
  Atom(Sym),
  App(App<A>),
}

struct DbgSexpr<'a,A>(&'a SExpr<A>);
impl<'a, A : Debug> core::fmt::Debug for DbgSexpr<'a, A> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
      #[cfg_attr(rustfmt, rustfmt::skip)]                             
      match &self.0 {
        SExpr::Var((DeBruinLevel::Intro,Sym(sym)))  => core::write!(f,"{sym}"),
        SExpr::Var((DeBruinLevel::Ref(i),Sym(sym))) => core::write!(f,"{sym}[{i}]"),
        SExpr::Atom(Sym(sym))                       => core::write!(f,"{sym}"),
        SExpr::App(App(l,r))                        => core::write!(f,"({l:?} {r:?})"),
      }
    }
}

#[derive(Clone,Copy,Debug)]
struct App<A>(A, A);

trait Functor {
  type F<T>;
  fn fmap<A, B>(f: Self::F<A>, func: impl FnMut(A) -> B) -> Self::F<B>;
}
trait Indirect {
  type I<T>;

  fn fold<A>(i: Self::I<A>) -> A;
  fn unfold<A>(v: A) -> Self::I<A>;
}
struct FixPoint<Rec: Functor, Ind: Indirect>(Rec::F<Ind::I<Self>>);

enum SExpresion {}
enum Boxed {}
impl Functor for SExpresion {
  type F<T> = SExpr<T>;
  fn fmap<A, B>(f: Self::F<A>, mut func: impl FnMut(A) -> B) -> Self::F<B> {
    match f {
      SExpr::Var(idx) => SExpr::Var(idx),
      SExpr::Atom(atom) => SExpr::Atom(atom),
      SExpr::App(App(l, r)) => {
        let l = func(l);
        let r = func(r);
        SExpr::App(App(l, r))
      }
    }
  }
}

impl Indirect for Boxed {
  type I<T> = Box<T>;

  fn fold<A>(i: Self::I<A>) -> A {
    *i
  }
  fn unfold<A>(v: A) -> Self::I<A> {
    Box::new(v)
  }
}

type SExprFix = FixPoint<SExpresion, Boxed>;

#[derive(Debug)]
pub enum ParseErr {
  TooManyClosingParenthesis(LineCol),
  UnclosedString(LineCol),
  UnexpectedEndOfFile(LineCol),
  OnlyOneExpressionAllowed(LineCol),
  MissingOpenParrenthesis(LineCol),
  TokenizationError(TokenErr),
  DyckReprLimitedTo32Elements,
  EmptySexpr(LineCol),
  SingleElementListNotSuported(LineCol)
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

struct Token { src_offset : usize, r#type : TokenType }
#[derive(Debug)]
pub enum TokenType {
  LPar,
  RPar,
  Var(Sym),
  Atom(Sym),
}

struct DyckParser<'a>{tokenizer : Tokenizer<'a>, /** Tokenizer has the src too, but this keeps lifetimes simpler */ src : &'a str}
impl<'a> DyckParser<'a> {
  fn new(src : &'a str)->Self {
    Self { tokenizer: Tokenizer::init(src), src }
  }


  #[cfg_attr(rustfmt, rustfmt::skip)]                             
  fn parse_first_sexrs_to_dyck(&mut self) -> Option<(Result<(DyckStructureZipperU64, Vec<SExpr<Void>>, Variables), ParseErr>)> {
    let err = |e| Option::Some(Result::Err(e)); 

    let Self { ref mut tokenizer, src } = self;
    let Option::Some(Result::Ok(Token {src_offset, r#type, .. })) = tokenizer.next() else { return Option::None; };
    let TokenType::LPar = r#type else { return err(ParseErr::MissingOpenParrenthesis(Tokenizer::at_line(src, src_offset))); };
    let mut s_expr_vec = Vec::with_capacity(32);
    
    let mut list_length = 0;
    let mut depth       = 0;
    let mut stack       = [0u8;33];
    let mut dyck_word   = 0;
    let mut variables   = Variables::new();
    
    'build_sexpr : while let Option::Some(result) = tokenizer.next() { 
      // std::println!("\n\
      //   s_expr_vec  ~ {s_expr_vec:?}\n\
      //   list_length = {list_length:?}\n\
      //   depth       = {depth:?}\n\
      //   stack       = {stack:?}\n\
      //   dyck_word   = {dyck_word:b}\n\
      //   variables   = {variables:?}\n\
      // ");
      match result {
        Result::Err(e)                           => return err(ParseErr::TokenizationError(e)),
        Result::Ok(Token { src_offset, r#type }) =>
          match r#type {
            TokenType::LPar => { /* push */ 
              if depth == 33 { return err(ParseErr::DyckReprLimitedTo32Elements); }
              list_length+=1;stack[depth]=list_length; depth+=1; list_length=0;
            },
            TokenType::RPar => { /* pop */
              if list_length == 0 { return err(ParseErr::EmptySexpr(                  Tokenizer::at_line(src, src_offset)));}
              if list_length == 1 { return err(ParseErr::SingleElementListNotSuported(Tokenizer::at_line(src, src_offset)));}
              for _ in 0..list_length-1 { dyck_word<<=1 }
              // std::println!("!!! {dyck_word:b}");
              if depth       == 0 { break 'build_sexpr; }
              depth-=1; list_length=stack[depth];
            },
            TokenType::Var(sym)  => { s_expr_vec.push(SExpr::Var((variables.aquire_de_bruin(sym),sym))); list_length+=1; dyck_word<<=1; dyck_word|=1;}
            TokenType::Atom(sym) => { s_expr_vec.push(SExpr::Atom(sym));                                 list_length+=1; dyck_word<<=1; dyck_word|=1;},
          },
        }
      }

    Option::Some(Result::Ok((DyckStructureZipperU64::new(dyck_word).unwrap(), s_expr_vec, variables)))
  }
}
impl<'a> Iterator for DyckParser<'a> {
  type Item = Result<(DyckStructureZipperU64, Vec<SExpr<Void>>, Variables), ParseErr>;
  fn next(&mut self) -> Option<Self::Item> {
      self.parse_first_sexrs_to_dyck()
  }
}



struct Tokenizer<'a>{
  src : &'a str,
  indicies_chars : core::iter::Peekable<core::str::CharIndices<'a>>,
}
impl<'a> Tokenizer<'a> {
  fn init(src: &'a str)->Self {
    Tokenizer { src: src, indicies_chars: src.char_indices().peekable() }
  }
  fn at_line (src : &str, idx :usize)->LineCol {
    if let Option::Some((line_idx, precedeing)) = src.get(0..idx).unwrap().lines().enumerate().last() { LineCol(line_idx, precedeing.len()) } else { LineCol(0, 0) }
  }

  /// doing Rust style escape sequence
  #[cfg_attr(rustfmt, rustfmt::skip)]                             
  fn escape_sequence(src: &'a str, (lead_idx, lead_char): (usize, char), indicies_chars: &mut impl Iterator<Item = (usize, char)>) -> Result<(), TokenErr> {
    macro_rules! hex {() => { 'a'..='f'|'A'..='F'|'0'..='9'};}
    
    let err = |idx, err : fn(_)->_| Result::Err(err(Tokenizer::at_line(src, idx)));
    let Option::Some((escape_idx, escape)) = indicies_chars.next()  else { return err(lead_idx, TokenErr::InvalidEscapeSequence); };
    core::debug_assert_eq!('\\', src.get(escape_idx-1..).unwrap().chars().next().unwrap());
    match escape {                                                  
      'n' | 'r' | 't' | '\\' | '0' | '\'' | '\"' => {}              
      'x' => '_ascii_hex_escape: {                                  
        let h_l = [indicies_chars.next(), indicies_chars.next()];   
        let [Option::Some((_, high)), Option::Some((_, low))] = h_l else { return err(escape_idx, TokenErr::InvalidHexEscape); };
        let ['0'..='7', hex!()] = [high, low]                       else { return err(escape_idx, TokenErr::InvalidHexEscape); };
      }                                                             
      'u' => '_unicode_escape: {                                    
        let mut buf = ['\0'; 6];                                    
        for i in 0..6 {                                             
          let Option::Some((_, c)) = indicies_chars.next()          else { return err(escape_idx, TokenErr::InvalidHexEscape); };
          buf[i] = c                                                
        }                                                           
        let ['{', '0'..='7', hex!(), hex!(), hex!(), '}'] = buf     else { return err(escape_idx, TokenErr::InvalidUnicodeEscape); };
      }                                                             
      _ =>                                                                 return err(escape_idx, TokenErr::InvalidEscapeSequence),
    }
    Result::Ok(())
  }
}

impl<'a> Iterator for Tokenizer<'a>{
  type Item = Result<Token, TokenErr>;
  fn next(&mut self) -> Option<Self::Item> {
    let Self { src, indicies_chars } = self;

    #[cfg_attr(rustfmt, rustfmt::skip)]
    '_make_token: loop {
      let Option::Some(&lead @ (lead_idx, lead_char)) = indicies_chars.peek() else {
        return Option::None;
      };
      let item = |i                           | Option::Some(Result::Ok(Token{src_offset: lead_idx, r#type : i}));
      let err  = |err: fn(LineCol) -> TokenErr| Option::Some(Result::Err(err(Tokenizer::at_line(src, lead_idx))));
      let sym  = |end_idx                     | Sym::new(unsafe { src.get_unchecked(lead_idx..end_idx) });
      
      match lead_char {
        '(' => { indicies_chars.next(); return item(TokenType::LPar);}
        ')' => { indicies_chars.next(); return item(TokenType::RPar);}
        ';' => 'ignore_comment: loop {
          let Option::Some((_, c)) = indicies_chars.next() else { break 'ignore_comment; };
          indicies_chars.next();
          if let '\n' = c { break 'ignore_comment; }
        },
        '\"' => 'string: {
          /* ground string, rust style, we do not support raw strings */
          indicies_chars.next();
          loop {
            let Option::Some((_, c)) = indicies_chars.next() else { break 'string; };
            match c {
              '\"' => {
                let Option::Some(&(e_idx, e)) = indicies_chars.peek() else { break 'string; };
                let valid =  core::matches!(e, '('|')') || e.is_whitespace();
                return if valid { Option::Some(Result::Ok(Token{src_offset: lead_idx, r#type : TokenType::Atom(sym(e_idx))})) } 
                       else     { err(TokenErr::InvalidStringLiteral) }}
              '\\' => if let Result::Err(e) = Tokenizer::escape_sequence(src, lead, indicies_chars) {return Option::Some(Result::Err(e));},
              _ => {}
            }
          }
        },
        w if w.is_whitespace() => core::mem::drop(indicies_chars.next()),
        x => { 
          // a var that is just "$" is a hole */
          let token_type = if let '$' = x { TokenType::Var } else { TokenType::Atom};
          
          let _ = 'ident : loop {
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

#[test]
fn test_dyck_parser(){
  let s = r#"
    (+ 1 2 3)
    (- 4 5 6)

    (eq ($X 3) (4 $Y) ($X $Y))

    (let ((x "given a lot of \x4A \u{0001}")
          (y "yup"))
         (print x y))

    ((\ (x) x) of love)

    (a be e)
  "#;
  let p = DyckParser::new(s);
  for each in p {
    match each {
        Result::Ok((zip,store,vars)) => {
          std::print!("\n{zip:?}store: [  ");
          for leaf in store.iter().map(DbgSexpr) {
            std::print!("{leaf:?}  ")
          }
          std::print!("]\nvars  : [");
          for leaf in vars.store.iter() {
            std::print!("{leaf:?}  ")
          }
          std::println!("]")
        }
        ,
        Result::Err(e) => std::println!("{e:?}"),
    }
  }
}