#![no_implicit_prelude]
#![allow(unused_imports, unused_variables, dead_code)]

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
  str,
};
use num_bigint::BigUint;
use std::{
  ascii, env::var, fmt::{Debug, Display}, marker::PhantomData, num::{NonZeroIsize, NonZeroUsize}, ops::Neg, process::Output, usize
};

/// It should be noted that the terminal is _NEVER_ equal to the head.
/// In the case of a leaf, the head is at the leaf position, and the terminal is one after it.
/// In other words, if t is the terminal, and h is the head, then
/// for a tree `0...001` we have `0..0th` (_t_=1, _h_=0),
///
/// example
/// - `0..0t____h` (_t_=5, _h_=0) tree `0..0011010`
/// - `0..0t__h__` (_t_=5, _h_=2) the left sub tree
/// - `0..0___th_` (_t_=2, _h_=1) the right sub tree (a leaf)
#[derive(Clone, Copy, PartialEq)]
pub struct SubtreeSlice {
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

  #[repr(transparent)]
  #[derive(Clone, Copy)]
  struct Bits(pub u64);
  impl core::fmt::Debug for Bits {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
      core::write!(f, "{:#066b}", self.0)
    }
  }
  #[derive(Debug)]
  enum SexprViewerError {
    Empty,
    TopBitNonZero,
    TooManyPairs,
    TooFewPairs,
  }
  impl Bits {
    /// this should be moved to DyckWord probably
    fn dyck_word_app_sexpr_viewer(self) -> Result<alloc::string::String, (SexprViewerError, Bits)> {
      use alloc::collections::VecDeque;
      use core::convert::From;
      use SexprViewerError as SVE;
      let mut stack = Vec::new();
      let word = self.0;
      if self.0 == 0 {
        return Result::Err((SVE::Empty, Bits(0)));
      }
      if (self.0 & (1 << u64::BITS - 1)) != 0 {
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

/// Represents the structure of a binary tree.  
/// 
/// for the sake of simplifying the implementation of other parts a [`DyckWord`] is defined to be non-empty
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct DyckWord {
  word: u64,
}
impl DyckWord {
  const fn new_debug_checked(word: u64) -> Self {
    core::debug_assert!{DyckWord::valid_non_empty(word)}
    DyckWord { word }
  }
  const fn zipper(self) -> DyckStructureZipperU64 {
    let mut stack = [SubtreeSlice::zeroes(); DyckStructureZipperU64::MAX_LEAVES];
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
}
impl core::fmt::Debug for DyckWord {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    // if self.word.len() == 1 
      core::write!(f, "0b_{:b}", self.word)
  }
}

#[derive(Clone, PartialEq)]
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
  const LEAF: Self = {
    let mut stack = [SubtreeSlice::zeroes(); Self::MAX_LEAVES];
    stack[0].terminal = 1;
    Self { structure: 1, current_depth: 0, stack }
  };

  /// Creates a Zipper for the Dyck Path, if the tree is empty (Dyck path of all 0s), it will return [`Option::None`]; this avoids uneeded checks when traversing.
  /// A valid Zipper is therefore always on a non-empty tree.
  /// Validating the structure of a Zipper is costly, so it is only checked in debug builds (TODO: is there a fast algorithm for doing the check using bit shifts and masks?).
  pub const fn new(structure: u64) -> Option<Self> {
    if let 0 = structure {
      return Option::None;
    }

    let mut stack = [SubtreeSlice::zeroes(); Self::MAX_LEAVES];
    stack[0].terminal = (u64::BITS).wrapping_sub(structure.leading_zeros()) as u8;

    Option::Some(Self { structure: DyckWord::new_debug_checked(structure).word, current_depth: 0, stack })
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
      unsafe { self.left_to_right_unchecked() };
      true
    } else {
      false
    }
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

  unsafe fn side_to_side_unchecked<const LEFT_TO_RIGHT : bool>(&mut self) {
    #![inline(always)]

    let Self { structure, current_depth, stack } = self;
    core::debug_assert!(!core::matches!(*structure, 0 | 1));
    core::debug_assert_ne!(*current_depth, 0);

    let prev = unsafe { *stack.get_unchecked(*current_depth as usize - 1) };
    let cur = unsafe { stack.get_unchecked_mut(*current_depth as usize) };

    *cur = if LEFT_TO_RIGHT {
      // is left
      core::debug_assert_eq!(prev.terminal, cur.terminal);
      // not right
      core::debug_assert_ne!(prev.head, cur.head - 1);
      
      SubtreeSlice { terminal: cur.head, head: prev.head + 1 }
    } else {
      // not left
      core::debug_assert_ne!(prev.terminal, cur.terminal);
      // is right
      core::debug_assert_eq!(prev.head, cur.head - 1);
  
      SubtreeSlice { terminal: prev.terminal, head: cur.terminal }
    }
  }

  fn side_to_side<const LEFT_TO_RIGHT : bool>(&mut self) -> bool {
    let Self { structure, current_depth, stack } = self;
    if *structure <= 1 || 0 == *current_depth {
      return false;
    }

    // Safety: The current depth is > 0
    let prev = unsafe { stack.get_unchecked(*current_depth as usize - 1) };
    let cur = unsafe { stack.get_unchecked(*current_depth as usize) };

    if LEFT_TO_RIGHT {
      // avoid double right
      if prev.head == cur.head - 1 {
        return false;
      }
    } else {
      // avoid double left
      if prev.terminal == cur.terminal {
        return false;
      }
    }

    unsafe {self.side_to_side_unchecked::<LEFT_TO_RIGHT>()}
    true
  }

  /// Switch from a left branch to the sibling right branch. Invariants are enfored in debug builds.
  pub unsafe fn left_to_right_unchecked(&mut self) {
    self.side_to_side_unchecked::<true>();
  }

  /// Switch from a left branch to the sibling right branch.
  pub fn left_to_right(&mut self) -> bool {
    self.side_to_side::<true>()
  }

  /// Switch from a right branch to the sibling left branch. Invariants are enfored in debug builds.
  pub unsafe fn right_to_left_unchecked(&mut self) {
    self.side_to_side_unchecked::<false>();
  }
  /// Switch from a right branch to the sibling left branch.
  pub fn right_to_left(&mut self) -> bool {
    self.side_to_side::<false>()
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
  pub fn at_root(&self) -> bool {
    self.current_depth == 0
  }
  // This moves in a cycle. so if you return to the root and make this call, it will start the iteration again
  pub fn next_depth_first_left_to_right_action(&self) -> DFSLeftToRightAction {
    // core::todo!("ADD TESTS");

    type Action = DFSLeftToRightAction;
    let is_left = self.current_is_left_branch();
    let is_leaf = self.current_is_leaf();
    if self.current_depth == 0 {
      return if is_leaf { Action::Root } else { Action::DecendLeft };
    }
    if is_left && is_leaf {
      return Action::GoRight;
    }
    if is_left && !is_leaf {
      return Action::DecendLeft;
    }

    if self.current_depth == 1 {
      return Action::Root;
    }
    Action::AccendRight
  }

  #[cfg_attr(rustfmt, rustfmt::skip)]
  pub fn advance_depth_first_left_to_right_action(&mut self) -> DFSLeftToRightAction {
    // core::todo!("ADD TESTS");

    let action = self.next_depth_first_left_to_right_action();
    match &action {
        DFSLeftToRightAction::Root        =>        { self.accend_to_root();         }
        DFSLeftToRightAction::DecendLeft  =>        { self.decend_left();            }
        DFSLeftToRightAction::GoRight     => unsafe { self.left_to_right_unchecked();}
        DFSLeftToRightAction::AccendRight =>        { self.accend();
                                                      self.left_to_right();
                                                    }
    }
    action
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

          unsafe { tmp.left_to_right_unchecked() };

          // enqueue right
          ring_buffer[end] = tmp.stack[1];
          end = (end + 1) % MAX_DEFERED;
        } else {
          break Option::Some(unsafe { tmp.leaf_store_index_unchecked(tmp.stack[0].head) });
        }
      }
    })
  }

  /// Produce an iterator that generates the traversal metadata in breadth first traversal order
  pub fn current_breadth_first_with_traversal_metadata(&self) -> impl Iterator<Item = (SubtreeSlice, TraversalPath)> + core::marker::Send + core::marker::Sync + 'static {
    const MAX_DEFERED: usize = DyckStructureZipperU64::MAX_LEAVES;
    
    //  core::todo!("ADD TESTS");
    
    let mut tmp = self.clone();
    
    // the iterator state
    let mut ring_buffer = [(SubtreeSlice::zeroes(), TraversalPath(0b_0)); MAX_DEFERED];
    
    let mut cur_path = 0b_0;
    for each in 0..=self.current_depth {
      tmp.current_depth = each;
      cur_path <<= 1;
      if !tmp.current_is_left_branch() {
        cur_path |= 1
      }
    }

    // after this point `tmp`'s only needs to mantain the structure field from self, the rest is scratch space.
    let mut front = 0;
    let mut end = 1;
    ring_buffer[0] = (self.stack[self.current_depth as usize], TraversalPath(cur_path));
    let mut recent_enqueue = 0;

    // the iterator
    core::iter::from_fn(move || {
      loop {
        if front == end {
          break Option::None;
        }

        if recent_enqueue > 0 {
          let idx = (end - recent_enqueue) % MAX_DEFERED;
          recent_enqueue -= 1;
          break Option::Some(ring_buffer[idx]);
        }

        // dequeue
        tmp.accend_to_root();
        let traversal = ring_buffer[front].1;
        tmp.stack[0] = ring_buffer[front].0;
        front = (front + 1) % MAX_DEFERED;

        if tmp.decend_left() {
          // enqueue left
          ring_buffer[end] = (tmp.stack[1], TraversalPath(traversal.0 << 1));
          end = (end + 1) % MAX_DEFERED;

          unsafe { tmp.left_to_right_unchecked() };

          // enqueue right
          ring_buffer[end] = (tmp.stack[1], TraversalPath(traversal.0 << 1 | 1));
          end = (end + 1) % MAX_DEFERED;

          recent_enqueue = 2
        } else {
          break Option::Some((tmp.stack[0], traversal));
        }
      }
    })
  }

  /// Obtain the current subtree Dyck path.
  pub fn current_substructure(&self) -> DyckWord {
    let SubtreeSlice { terminal, head } = self.stack[self.current_depth as usize];
    DyckWord { word: ((1 << terminal) - 1 & self.structure) >> head }
  }
}
pub enum DFSLeftToRightAction {
  Root,
  DecendLeft,
  GoRight,
  // coresponds to an accend followed by an  left_to_right
  AccendRight,
}

/// ```ignore
/// // 0b0.......01 root            or []
/// // 0b0......010 left  from root or [L]
/// // 0b0......011 right from root or [R]
/// // 0b0..0101100                    [L R R L L]
/// // 0b1........1 rightmost element of a dyck word 0b01..(32 ones)..10..(31 zeroes)..0
/// ```
#[derive(Clone, Copy)]
pub struct TraversalPath(u32);

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
}
/// Trait interface for doing basic pattern matching
pub trait MatchElement {
  type Element;
  type Atom;
  type Var;
  type VarTable;
  /// Inspects an element to determine if it is an atom or a variable to be bound.
  fn element_type(e: &Self::Element) -> ElementType<Self::Atom, Self::Var>;
  /// Atoms that are considered equal are determined to match.
  fn atom_eq(left: &Self::Atom, right: &Self::Atom) -> bool;
  /// if the var is not in the table, it returns DebruijnLevel::Intro
  fn var_de_bruin_level(table: &Self::VarTable, var: &Self::Var) -> DeBruijnLevel;
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
  #![cfg_attr(rustfmt, rustfmt::skip)]

  type DSZ = DyckStructureZipperU64;

  ///////
  // 0b_0
  ///////
  // std::println!("\n# 0b_0\nNone");
  core::assert!(core::matches!(DSZ::new(0b_0), Option::None));

  '_0b_1: {
    // std::println!("\n# 0b_1\n");
    let mut tree_0b_1 = DSZ::new(0b_1).unwrap();
    let count = tree_0b_1.structure.count_ones() as usize;
    // std::println!("{:#?}", tree_0b_1);
    // no parent
    core::assert!(   !tree_0b_1.accend());
    // no children   
    core::assert!(   !tree_0b_1.decend_left());
    core::assert!(   !tree_0b_1.decend_right());
    // no branching  
    core::assert!(   !tree_0b_1.right_to_left());
    core::assert!(   !tree_0b_1.left_to_right());
    // single element
    core::assert_eq!( tree_0b_1.current_first_leaf_store_index(), 0);
    core::assert_eq!( tree_0b_1.current_leaf_store_index_range(), 0..count);
  }

  '_0b_110: {
    // std::println!("\n# 0b_110\n");
    let mut tree_0b_110 = DSZ::new(0b_110).unwrap();
    let count = tree_0b_110.structure.count_ones() as usize;
    // std::println!("{:#?}", tree_0b_110);

    // at root
    core::assert!(    !tree_0b_110.right_to_left());
    core::assert!(    !tree_0b_110.left_to_right());
    core::assert_eq!(  tree_0b_110.current_first_leaf_store_index(), 0);
    core::assert_eq!(  tree_0b_110.current_leaf_store_index_range(), 0..count);
    core::assert!(    !tree_0b_110.accend());

    // cycle counterclockwise
    core::assert!(     tree_0b_110.decend_left());
    core::assert_eq!(  tree_0b_110.current_first_leaf_store_index(), 0);
    core::assert_eq!(  tree_0b_110.current_leaf_store_index_range(), 0..1);
    core::assert!(     tree_0b_110.left_to_right());
    core::assert_eq!(  tree_0b_110.current_first_leaf_store_index(), 1);
    core::assert_eq!(  tree_0b_110.current_leaf_store_index_range(), 1..count);
    core::assert!(     tree_0b_110.accend());

    // back to root
    core::assert_eq!(  tree_0b_110.current_leaf_store_index_range(), 0..count);

    // cycle clockwise
    core::assert!(     tree_0b_110.decend_right());
    core::assert_eq!(  tree_0b_110.current_first_leaf_store_index(), 1);
    core::assert_eq!(  tree_0b_110.current_leaf_store_index_range(), 1..count);
    core::assert!(     tree_0b_110.right_to_left());
    core::assert_eq!(  tree_0b_110.current_first_leaf_store_index(), 0);
    core::assert_eq!(  tree_0b_110.current_leaf_store_index_range(), 0..1);
    core::assert!(     tree_0b_110.accend());
  }

  '_0b_11010: {
    std::println!("\n# 0b_11010\n");
    let mut tree_0b_11010 = DSZ::new(0b_11010).unwrap();
    let count = tree_0b_11010.structure.count_ones() as usize;
    // std::println!("{:#?}", tree_0b_11010);

    // at root
    core::assert!(    !tree_0b_11010.right_to_left());
    core::assert!(    !tree_0b_11010.left_to_right());
    core::assert_eq!(  tree_0b_11010.current_first_leaf_store_index(), 0);
    core::assert_eq!(  tree_0b_11010.current_leaf_store_index_range(), 0..count);
    core::assert!(    !tree_0b_11010.accend());

    // visit each, right to left
    core::assert!(     tree_0b_11010.decend_right());
    // std::println!("{:#?}", tree_0b_11010);
    core::assert!(    !tree_0b_11010.decend_left());
    core::assert_eq!(  tree_0b_11010.current_first_leaf_store_index(), 2);
    core::assert_eq!(  tree_0b_11010.current_leaf_store_index_range(), 2..count);
    core::assert!(    !tree_0b_11010.decend_right());

    core::assert!(     tree_0b_11010.right_to_left());
    // std::println!("{:#?}", tree_0b_11010);

    core::assert!(     tree_0b_11010.decend_right());
    // std::println!("{:#?}", tree_0b_11010);
    core::assert!(    !tree_0b_11010.decend_left());
    core::assert_eq!(  tree_0b_11010.current_first_leaf_store_index(), 1);
    core::assert_eq!(  tree_0b_11010.current_leaf_store_index_range(), 1..2);
    core::assert!(    !tree_0b_11010.decend_right());

    core::assert!(     tree_0b_11010.right_to_left());
    // std::println!("{:#?}", tree_0b_11010);
    core::assert!(    !tree_0b_11010.decend_left());

    core::assert_eq!(  tree_0b_11010.current_first_leaf_store_index(), 0);
    core::assert_eq!(  tree_0b_11010.current_leaf_store_index_range(), 0..1);
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



#[cfg_attr(rustfmt, rustfmt::skip)]
#[test]
fn test_naive_matching() {

  fn test_matcher(src: &str) {
    let mut parser = DyckParser::new(src);
    parser.thread_variables(Option::Some(Variables::new()));
    let mut next = || {
      let e = parser.next().unwrap().unwrap();
      parser.clear_variables();
      e
    };
    let (       input_zipper,    input_data, _) = next();
    let (     pattern_zipper,  pattern_data, _) = next();
    let (mut template_zipper, template_data, _) = next();
    let (    expected_zipper, expected_data, _) = next();

    fn prep<'a>(z : &DyckStructureZipperU64, d : &'a [SExpr])-> (DyckWord, &'a [SExpr]) {
      ( z.current_substructure(), d)
    }
    
    template_zipper.decend_right();
    let range = template_zipper.current_leaf_store_index_range();
    let result = transform_re_index_small(
      prep(&input_zipper, &input_data),
      prep(&pattern_zipper, &pattern_data),
      prep(&template_zipper, &template_data[template_zipper.current_leaf_store_index_range()]),
    ).unwrap();

    core::assert_eq!(result.word, expected_zipper.current_substructure());
    core::assert_eq!(&result.data[..result.len], &expected_data[..]);
  }

  let src1 = r"
    (a $X (b c))                              ;; input
    (a $X  $Y)                                ;; pattern
    (($X $Y)
     (x $Y))                                  ;; template
    (x (b c))                                 ;; expected
    ";
  test_matcher(src1);

  let src2 =r"
    (Point2d (X 15.4) (Y -34.9))              ;; input
    (Point2d (X   $X) (Y    $Y))              ;; pattern

    (($X $Y)
     (Sqrt (+ (*    $X    $X)
              (*    $Y    $Y))))              ;; template
    (Sqrt (+ (*  15.4  15.4)
             (* -34.9 -34.9)))                ;; expected
  ";
  test_matcher(src2);

  let src3 = r"
    (Point2d (X (+ 3.0 2.2)) (Y -34.9))       ;; input
    (Point2d (X          $X) (Y    $Y))       ;; pattern

    (($X $Y)
     (Sqrt (+ (*           $X          $X)
              (*           $Y          $Y)))) ;; template
    (Sqrt (+ (*  (+ 3.0 2.2)  (+ 3.0 2.2))
             (*        -34.9       -34.9)))   ;; expected
  ";
  test_matcher(src3);
}





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

// if string interning is slow, it could be split into buckets, and use a ReadWrite lock, perhaps even Semaphores. but for testing this should be enough
static INTERNED_STR: std::sync::Mutex<alloc::collections::BTreeSet<&'static str>> = std::sync::Mutex::new(alloc::collections::BTreeSet::new());

// Sym is valid if it has an empty str, or if it holds and interned str.
#[derive(Debug, Clone, Copy, PartialOrd, Ord, Eq)]
pub struct Sym(&'static str);
impl Sym {
  const EMPTY: Self = Sym("");
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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SExpr {
  Var(DeBruijnLevel),
  Atom(Sym),
}

#[repr(transparent)]
struct DbgSexpr(SExpr);
impl core::fmt::Debug for DbgSexpr {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    #[cfg_attr(rustfmt, rustfmt::skip)]
      match &self.0 {
        SExpr::Var(DeBruijnLevel::Intro)  => core::write!(f,"$"),
        SExpr::Var(DeBruijnLevel::Ref(i)) => core::write!(f,"$[{i}]"),
        SExpr::Atom(Sym(sym))             => core::write!(f,"{sym}"),
      }
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
  s_expr_vec: Vec<SExpr>,
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

  fn append_element(&mut self, e: SExpr) {
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
    self.append_element(SExpr::Atom(Sym::new("Singleton")));
    self.s_expr_vec.swap(new_index - 1, new_index);
  }
  fn make_empty(&mut self) {
    self.append_element(SExpr::Atom(Sym::new("Empty")))
  }

  fn make_var(&mut self, sym: Sym) -> Result<(), ParseErr> {
    if self.s_expr_vec.len() == 32 {
      self.consume_till_balanced();
      return Result::Err(ParseErr::DyckReprLimitedTo32Elements(Tokenizer::at_line(self.src, self.cur_token.src_offset)));
    }
    let elem = SExpr::Var(self.variables.aquire_de_bruin(self.s_expr_vec.len(), sym));
    self.append_element(elem);
    Result::Ok(())
  }
  fn make_atom(&mut self, sym: Sym) -> Result<(), ParseErr> {
    if self.s_expr_vec.len() == 32 {
      self.consume_till_balanced();
      return Result::Err(ParseErr::DyckReprLimitedTo32Elements(Tokenizer::at_line(self.src, self.cur_token.src_offset)));
    }
    let elem = SExpr::Atom(sym);
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
  fn clear_variables(&mut self) {self.threaded_variables = Option::None;}
  fn thread_variables(&mut self, mut vars: Option<Variables>) -> Option<Variables> {
    core::mem::swap(&mut vars, &mut self.threaded_variables);
    vars
  }
  /// the applicative representation
  #[cfg_attr(rustfmt, rustfmt::skip)]
  pub fn parse_first_sexrs_to_dyck_app_repr(&mut self) -> Option<Result<(DyckStructureZipperU64, Vec<SExpr>, Variables), ParseErr>> {
    self.parse_first_sexrs_to_dyck_select::<true>()
  }

  /// the list representation
  #[cfg_attr(rustfmt, rustfmt::skip)]
  pub fn parse_first_sexrs_to_dyck_list_repr(&mut self) -> Option<Result<(DyckStructureZipperU64, Vec<SExpr>, Variables), ParseErr>> {
    self.parse_first_sexrs_to_dyck_select::<false>()
  }

  fn parse_first_sexrs_to_dyck_select<const APP_REPR : bool>(&mut self) -> Option<Result<(DyckStructureZipperU64, Vec<SExpr>, Variables), ParseErr>> {
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
  type Item = Result<(DyckStructureZipperU64, Vec<SExpr>, Variables), ParseErr>;
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
          for leaf in store.iter().copied().map(DbgSexpr) {
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

// #[cfg_attr(rustfmt, rustfmt::skip)]
#[allow(non_snake_case)]
#[test]
fn test_examples() {
  let sym = |c| Sym::new(c);
  let [f, g, h] = ["f", "g", "h"].map(sym);
  let [a, b, c] = ["a", "b", "c"].map(sym);
  let [A, B, C] = ["A", "B", "C"].map(sym);
  let S = sym("S");
  let [eq, comma, colon, arrow, star, plus] = ["=", ",", ":", "-->", "*", "+"].map(sym);

  let parse = |src| DyckParser::new(src).next().unwrap().unwrap();
  type ParserOutput = (DyckStructureZipperU64, Vec<SExpr>, Variables);
  let [e1, e2, e3, r1] = ["(f $x a)", "(f $x $y $y $x)", "(f $y (g $y $x))", "(= (f (, $x (g (g $y)))) (h (, $x (g a)) (, $x (g $y))))"].map(parse);

  fn atom(a: Sym) -> SExpr {
    SExpr::Atom(a)
  }
  fn atoms<const L: usize>(a: [Sym; L]) -> [SExpr; L] {
    a.map(SExpr::Atom)
  }

  '_foldMap_size_fvars: {
    // shared/src/test/scala/ExprTest.scala
    // ```scala
    //   test("foldMap size fvars") {
    //   assert(e1.size == 5)
    //   assert(e1.fvars == Seq(1, 10))
    //   assert(e2.size == 9)
    //   assert(e2.fvars == Seq(1))
    //   assert(e3.size == 9)
    //   assert(e2.fvars == Seq(1))
    // }
    // ```

    // `size` can be computed with the dyck word, though to emulate the scala test, we have to include branches too
    // `fvars`` can be done with just an slice filter
    let size = |&(DyckStructureZipperU64 { structure, .. }, _, _): &ParserOutput| u64::BITS - structure.leading_zeros();
    let fvars = |(_, data, _): &ParserOutput| {
      data
        .iter()
        .copied()
        .filter(|e| match e {
          SExpr::Atom(_) => true,
          _ => false,
        })
        .collect::<Vec<_>>()
    };

    core::assert_eq!(size(&e1), 5);
    core::assert_eq!(&fvars(&e1), &atoms([f, a]));

    core::assert_eq!(size(&e2), 9);
    core::assert_eq!(&fvars(&e2), &atoms([f]));

    core::assert_eq!(size(&e3), 9);
    core::assert_eq!(&fvars(&e3), &atoms([f, g]));
  }

  '_toAbsolute_toRelative: {
    // shared/src/test/scala/ExprTest.scala
    // ```scala
    // test("toAbsolute toRelative") {
    //   val e1a = Expr(f, Expr.Var(-100), a)
    //   val e2a = Expr(f, Expr.Var(-100), Expr.Var(-101), Expr.Var(-101), Expr.Var(-100))
    //   val e3a = Expr(f, Expr.Var(-100), Expr(g, Expr.Var(-100), Expr.Var(-101)))
    //   assert(e1.toAbsolute(100) == e1a)
    //   assert(e2.toAbsolute(100) == e2a)
    //   assert(e3.toAbsolute(100) == e3a)
    //   assert(e1a.toRelative == e1)
    //   assert(e2a.toRelative == e2)
    //   assert(e3a.toRelative == e3)
    //   assert(r1.toAbsolute(100).toRelative == r1)
    //   assert(r1.toAbsolute(100).toRelative.toAbsolute(200) == r1.toAbsolute(200))
    // }
    // ```

    // changing the variables is structure independant, we need only change the underlying slice


    let var = |v| SExpr::Var(DeBruijnLevel::Ref(NonZeroIsize::new(v).unwrap()));
    let e1a = [atom(f), var(-100), atom(a)];
    let e2a = [atom(f), var(-100), var(-101), var(-101), var(-100)];
    let e3a = [atom(f), var(-100), atom(g), var(-100), var(-101)];

    core::assert_eq! {&to_absolute(&e1.1, 100), &e1a}
    core::assert_eq! {&to_absolute(&e2.1, 100), &e2a}
    core::assert_eq! {&to_absolute(&e3.1, 100), &e3a}

    core::assert_eq! {&to_relative(&e1a), &e1.1}
    core::assert_eq! {&to_relative(&e2a), &e2.1}
    core::assert_eq! {&to_relative(&e3a), &e3.1}

    core::assert_eq! { &to_relative(&to_absolute(&r1.1, 100)), &r1.1 }
    core::assert_eq! { &to_absolute(&to_relative(&to_absolute(&r1.1, 200)), 100), &to_absolute(&r1.1, 100) }
  }

  '_substReIndex: {
    // shared/src/test/scala/ExprTest.scala
    // ```scala
    // test("substReIndex") {
    //   val r1 = Expr(f, $, _1)
    //   assert(r1.substReIndex(Seq($)) == r1)
    //   assert(r1.substReIndex(Seq(Expr(a, $, $))) == Expr(f, Expr(a, $, $), Expr(a, _1, _2)))
    //   val r2 = Expr(f, $, $, _1)
    //   assert(r2.substReIndex(Seq(Expr(a, $, $), A)) == Expr(f, Expr(a, $, $), A, Expr(a, _1, _2)))
    //   assert(r2.substReIndex(Seq(Expr(a, $, $), $)) == Expr(f, Expr(a, $, $), $, Expr(a, _1, _2)))
    //   assert(r2.substReIndex(Seq(Expr(a, $, _1), $)) == Expr(f, Expr(a, $, _1), $, Expr(a, _1, _1)))
    //   val r3 = Expr(`,`, Expr(f, $, $), Expr(g, _2, $, _3))
    //   assert(r3.substReIndex(Seq(a, b, c)) == Expr(`,`, Expr(f, a, b), Expr(g, b, c, c)))
    //   assert(r3.substReIndex(Seq(a, $, c)) == Expr(`,`, Expr(f, a, $), Expr(g, _1, c, c)))
    //   assert(r3.substReIndex(Seq(a, $, $)) == Expr(`,`, Expr(f, a, $), Expr(g, _1, $, _2)))
    //   assert(r3.substReIndex(Seq($, $, $)) == Expr(`,`, Expr(f, $, $), Expr(g, _2, $, _3)))
    //   assert(r3.substReIndex(Seq(a, Expr(B, $, $), c)) == Expr(`,`, Expr(f, a, Expr(B, $, $)), Expr(g, Expr(B, _1, _2), c, c)))
    //   assert(r3.substReIndex(Seq($, Expr(B, $, $), $)) == Expr(`,`, Expr(f, $, Expr(B, $, $)), Expr(g, Expr(B, _2, _3), $, _4)))
    //   assert(r3.substReIndex(Seq($, Expr(B, $, _1), c)) == Expr(`,`, Expr(f, $, Expr(B, $, _2)), Expr(g, Expr(B, _2, _2), c, c)))
    //   assert(r3.substReIndex(Seq(Expr(A, $, $), Expr(B, $, _1), c)) == Expr(`,`, Expr(f, Expr(A, $, $), Expr(B, $, _3)), Expr(g, Expr(B, _3, _3), c, c)))
    //   assert(r3.substReIndex(Seq(Expr(A, $, $), Expr(B, $, $, _2), Expr(C, $, _1))) == Expr(`,`, Expr(f, Expr(A, $, $), Expr(B, $, $, _4)), Expr(g, Expr(B, _3, _4, _4), Expr(C, $, _5), Expr(C, _5, _5))))
    // }
    // ```

    
    let intro_var = (DyckWord::new_debug_checked(1), &[SExpr::Var(DeBruijnLevel::Intro)][..]);
    let get_word = |expr: &DyckExprSubOutput| match expr {
      DyckExprSubOutput::SmallDyckExpr(SmallDyckExpr { word, .. }) => *word,
      DyckExprSubOutput::LargeDyckExpr(LargeDyckExpr { word, .. }) => core::panic!(),
    };
    let get_data: fn(&_) -> &_ = |expr: &DyckExprSubOutput| match expr {
      DyckExprSubOutput::SmallDyckExpr(SmallDyckExpr { data, len, .. }) => &data[0..*len],
      | DyckExprSubOutput::LargeDyckExpr(LargeDyckExpr { data, .. }) => data,
    };
    let get_data_mut: fn(&mut _) -> &mut _ = |expr: &mut DyckExprSubOutput| match expr {
      DyckExprSubOutput::SmallDyckExpr(SmallDyckExpr { data, len,.. }) => &mut data[0..*len],
      | DyckExprSubOutput::LargeDyckExpr(LargeDyckExpr { data, .. }) => data,
    };
    let sub_re_index_input: fn(&(DyckStructureZipperU64, Vec<SExpr>, Variables), u8) -> (_, &_, _) = |x, offset| (x.0.current_substructure(), &x.1[..], offset);
    
    const LEAF: DyckWord = DyckWord { word: 1 };
    
    macro_rules! templates {($($ID:ident $SRC:literal)+) => {$(
      let _tmp = parse($SRC);
      #[allow(non_snake_case)]
      let $ID  = sub_re_index_input(&_tmp,0);
    )+};}

    templates! {
      r1   "(f $x $x)"
      r2   "(f $x $y $x)"
      r3   "(, (f $x $y) (g $y $z $z))"
      axy  "(a $x $y)"
      axx  "(a $x $x)"
      Bxy  "(B $x $y)"
      Bxx  "(B $x $x)"
      Axy  "(A $x $y)"
      Bxyy "(B $x $y $y)"
      Cxx  "(C $x $x)"


      i3_r1   "($a $b $c    (f $x $x))"
      i3_r2   "($a $b $c    (f $x $y $x))"
      i3_r3   "($a $b $c    (, (f $x $y) (g $y $z $z)))"
    }


    let mut tmp_ = i3_r1.0.zipper(); tmp_.decend_right(); let d3_r1 = (tmp_.current_substructure() ,&i3_r1.1[3..]);
    let mut tmp_ = i3_r2.0.zipper(); tmp_.decend_right(); let d3_r2 = (tmp_.current_substructure() ,&i3_r2.1[3..]);
    let mut tmp_ = i3_r3.0.zipper(); tmp_.decend_right(); let d3_r3 = (tmp_.current_substructure() ,&i3_r3.1[3..]);

    let s1 = subst_re_index_with_pat_offset((r1.0,r1.1, 0), &[intro_var]);
    core::assert_eq! {r1.0, get_word(&s1) }
    core::assert_eq! {r1.1,&get_data(&s1)[..]}

    macro_rules! substitutions {($($OFFSET:literal [$PAT:ident / [$($SUB:expr),*]] => $EXPECTED:literal | $INTROS:tt;)+) => {$(
      let s = subst_re_index_with_pat_offset(($PAT.0,$PAT.1, $OFFSET), &[$(($SUB.0,$SUB.1)),*]);
      let expected_ = parse($EXPECTED);
      let tmp = sub_re_index_input(&expected_,0);
      // std::println!("{:?}",tmp);
      let /* mut */ expected  = subst_re_index_with_pat_offset(tmp, &$INTROS);
      
      // if $OFFSET > 0{
      // for each in get_data_mut(&mut expected).iter_mut() {
      //   if let SExpr::Var(DeBruijnLevel::Ref(r)) = each {
      //     *r = NonZeroIsize::new(r.get()-$OFFSET).unwrap()
      //   }
      // }}
      
      // std::println!("{:?}",expected);
      core::assert_eq!(get_word(&s), get_word(&expected));
      core::assert_eq!(get_data(&s), get_data(&expected));
      // pretty_print(&s);
    )+};}
    
    let leaf_a = (DyckWord::new_debug_checked(1), &[atom(a)][..]);
    let leaf_c = (DyckWord::new_debug_checked(1), &[atom(c)][..]);
    substitutions! {
      0 [r1 / [axy]                                ] => "(f (a $x $y) (a $x $y))"                                             | [intro_var, intro_var];
      0 [r2 / [axy, (LEAF ,&[atom(A)])]            ] => "(f (a $x $y) A (a $x $y))"                                           | [intro_var, intro_var];
      0 [r2 / [axx, intro_var]                     ] => "(f (a $x $x) $ (a $x $x))"                                           | [intro_var, intro_var];
      0 [r3 / [leaf_a, (LEAF, &[atom(b)]), leaf_c] ] => "(, (f a b) (g b c c))"                                               | [];
      0 [r3 / [leaf_a, intro_var, leaf_c]          ] => "(, (f a $x) (g $x c c))"                                             | [intro_var];
      0 [r3 / [leaf_a, intro_var, intro_var]       ] => "(, (f a $x) (g $x $y $y))"                                           | [intro_var, intro_var];
      0 [r3 / [intro_var, intro_var, intro_var]    ] => "(, (f $x $y) (g $y $z $z))"                                          | [intro_var, intro_var, intro_var];
      0 [r3 / [leaf_a, Bxy, leaf_c]                ] => "(, (f a (B $x $y)) (g (B $x $y) c c))"                               | [intro_var, intro_var];
 
      0 [r3 / [intro_var, Bxy, intro_var]          ] => "(, (f $w (B $x $y)) (g (B $x $y) $z $z))"                            | [intro_var, intro_var, intro_var, intro_var];
      0 [r3 / [intro_var, Bxx, leaf_c]             ] => "(, (f $w (B $x $x)) (g (B $x $x) c c))"                              | [intro_var, intro_var];
      0 [r3 / [Axy, Bxx, leaf_c]                   ] => "(, (f (A $w $x) (B $y $y)) (g (B $y $y) c c))"                       | [intro_var, intro_var, intro_var];
      0 [r3 / [Axy, Bxyy, Cxx]                     ] => "(, (f (A $v $w) (B $x $y $y)) (g (B $x $y $y) (C $z $z) (C $z $z)))" | [intro_var, intro_var, intro_var, intro_var, intro_var];



      3 [d3_r1 / [axy]                                ] => "(f (a $x $y) (a $x $y))"                                             | [intro_var, intro_var];
      3 [d3_r2 / [axy, (LEAF ,&[atom(A)])]            ] => "(f (a $x $y) A (a $x $y))"                                           | [intro_var, intro_var];
      3 [d3_r2 / [axx, intro_var]                     ] => "(f (a $x $x) $ (a $x $x))"                                           | [intro_var, intro_var];
      3 [d3_r3 / [leaf_a, (LEAF, &[atom(b)]), leaf_c] ] => "(, (f a b) (g b c c))"                                               | [];
      3 [d3_r3 / [leaf_a, intro_var, leaf_c]          ] => "(, (f a $x) (g $x c c))"                                             | [intro_var];
      3 [d3_r3 / [leaf_a, intro_var, intro_var]       ] => "(, (f a $x) (g $x $y $y))"                                           | [intro_var, intro_var];
      3 [d3_r3 / [intro_var, intro_var, intro_var]    ] => "(, (f $x $y) (g $y $z $z))"                                          | [intro_var, intro_var, intro_var];
      3 [d3_r3 / [leaf_a, Bxy, leaf_c]                ] => "(, (f a (B $x $y)) (g (B $x $y) c c))"                               | [intro_var, intro_var];
      3 [d3_r3 / [intro_var, Bxy, intro_var]          ] => "(, (f $w (B $x $y)) (g (B $x $y) $z $z))"                            | [intro_var, intro_var, intro_var, intro_var];
      3 [d3_r3 / [intro_var, Bxx, leaf_c]             ] => "(, (f $w (B $x $x)) (g (B $x $x) c c))"                              | [intro_var, intro_var];
      3 [d3_r3 / [Axy, Bxx, leaf_c]                   ] => "(, (f (A $w $x) (B $y $y)) (g (B $y $y) c c))"                       | [intro_var, intro_var, intro_var];
      3 [d3_r3 / [Axy, Bxyy, Cxx]                     ] => "(, (f (A $v $w) (B $x $y $y)) (g (B $x $y $y) (C $z $z) (C $z $z)))" | [intro_var, intro_var, intro_var, intro_var, intro_var];
    }
  }

  // return;













  '_matches: {
    // shared/src/test/scala/ExprTest.scala
    // ```scala
    // test("matches") {
    //   /*
    //   for all matching lhs, rhs
    //   val Some((lhs_vars, rhs_vars)) = (lhs matches rhs)
    //   assert(lhs.substRel(lhs_vars) == rhs.substRel(rhs_vars))
    //   */
    //   assert((a matches a).contains((List(), List())))
    //   assert((a matches b).isEmpty)
    //   assert(($ matches $).contains((List($),List($))))
    //   assert((Expr(a, b) matches Expr(a, b)).contains((List(), List())))
    //   assert((Expr(a, b) matches Expr(a, c)).isEmpty)
    //   assert((Expr($, b) matches Expr(a, b)).contains((List(a),List())))
    //   assert((Expr(Expr($, a), Expr(_1, b)) matches Expr(Expr(c, a), Expr(c, b))).contains((List(c),List())))
    //   assert((Expr(Expr($, a), Expr(_1, b)) matches Expr(Expr(c, a), Expr(a, b))).isEmpty)
    //   assert((Expr(Expr($, a), Expr(_1, b)) matches Expr(Expr(a, $), Expr(a, _1))).isEmpty)
    //   assert((Expr(Expr($, a), Expr(_1, a)) matches Expr(Expr(b, $), Expr(b, _1))).contains((List(b), List(a))))
    //   // println(Expr(Expr($, a), Expr(_1, b)) matches Expr(Expr($, a), Expr(b, _1)))
    //   assert((Expr(Expr(a, $), Expr(_1, b)) matches Expr(Expr($, a), Expr(_1, b))).contains((List(a),List(a))))
    //   // println(Expr($, _1, a, _1) matches Expr($, _1, _1, a))
    //   assert((Expr($, _1, a, _1) matches Expr($, _1, _1, b)).isEmpty)
    //   assert((Expr($, _1, a, _1) matches Expr($, _1, _1, b)).isEmpty)
    //   assert((Expr($, a, _1) matches Expr(Expr(b, $), $, Expr(_2, _1))).isEmpty)
    //   // println(Expr($, a, _1) matches Expr(Expr(b, $), $, Expr($, _1)))
    // }
    // ```
    let r#ref = |n| SExpr::Var(DeBruijnLevel::Ref(NonZeroIsize::new(n).unwrap()));

    let a_ = (DyckWord::new_debug_checked(1), &[atom(a)][..]);
    let b_ = (DyckWord::new_debug_checked(1), &[atom(b)][..]);
    let c_ = (DyckWord::new_debug_checked(1), &[atom(c)][..]);
    let intro = SExpr::Var(DeBruijnLevel::Intro);
    let intro_ = (DyckWord::new_debug_checked(1), &[intro][..]);
    let ab_ = (DyckWord::new_debug_checked(0b_110), &[atom(a), atom(b)][..]);
    let ac_ = (DyckWord::new_debug_checked(0b_110), &[atom(a), atom(c)][..]);
    let xb_ = (DyckWord::new_debug_checked(0b_110), &[intro, atom(b)][..]);

    let xa_xb_ = (DyckWord::new_debug_checked(0b_110_110_0), &[intro, atom(a),r#ref(-1), atom(b)][..]);
    let ca_cb_ = (DyckWord::new_debug_checked(0b_110_110_0), &[atom(c), atom(a),atom(c), atom(b)][..]);
    let ca_ab_ = (DyckWord::new_debug_checked(0b_110_110_0), &[atom(c), atom(a),atom(a), atom(b)][..]);
    let ax_ax_ = (DyckWord::new_debug_checked(0b_110_110_0), &[atom(a), intro,atom(a), r#ref(-1)][..]);
    let xa_xa_ = (DyckWord::new_debug_checked(0b_110_110_0), &[ intro,atom(a), r#ref(-1),atom(a)][..]);
    let bx_bx_ = (DyckWord::new_debug_checked(0b_110_110_0), &[atom(b), intro,atom(b), r#ref(-1)][..]);
    let ax_xb_ = (DyckWord::new_debug_checked(0b_110_110_0), &[atom(a), intro, r#ref(-1),atom(b)][..]);
    
    let xxax_ = (DyckWord::new_debug_checked(0b_1101010), &[intro, r#ref(-1), atom(a), r#ref(-1)][..]);
    let xxxb_ = (DyckWord::new_debug_checked(0b_1101010), &[intro, r#ref(-1), r#ref(-1), atom(b)][..]);
    let xax_  = (DyckWord::new_debug_checked(0b_11010), &[intro, atom(a),r#ref(-1)][..]);
    let bx_y_zx_  = (DyckWord::new_debug_checked(0b_110_10_110_0), &[atom(b),intro,intro,intro,r#ref(-1)][..]);
    
    core::assert_eq! {expr_matches(a_, a_), Option::Some((Vec::new(), Vec::new()))}
    core::assert_eq! {expr_matches(a_, b_), Option::None}
    core::assert_eq! {expr_matches(intro_, intro_), Option::Some((Vec::from([intro_]), Vec::from([intro_])))}
    
    core::assert_eq! {expr_matches(ab_, ab_), Option::Some((Vec::new(), Vec::new()))}
    core::assert_eq! {expr_matches(ab_, ac_), Option::None}
    core::assert_eq! {expr_matches(xb_, ab_), Option::Some((Vec::from([a_]), Vec::new()))}
    
    core::assert_eq! {expr_matches(xa_xb_, ca_cb_), Option::Some((Vec::from([c_]), Vec::new()))}
    core::assert_eq! {expr_matches(xa_xb_, ca_ab_), Option::None}
    core::assert_eq! {expr_matches(xa_xb_, ax_ax_), Option::None}
    core::assert_eq! {expr_matches(xa_xa_, bx_bx_), Option::Some((Vec::from([b_]), Vec::from([a_])))}
    core::assert_eq! {expr_matches(ax_xb_, xa_xb_), Option::Some((Vec::from([a_]), Vec::from([a_])))}
    core::assert_eq! {expr_matches(xxax_, xxxb_), Option::None}
    core::assert_eq! {expr_matches(xax_, bx_y_zx_), Option::None}

  }


  // shared/src/test/scala/ExprTest.scala
  // ```scala
  // test("unifiable") {
  //   assert(a unifiable a)
  //   assert(!(a unifiable b))
  //   assert($ unifiable $)
  //   assert(Expr(a, b) unifiable Expr(a, b))
  //   assert(!(Expr(a, b) unifiable Expr(a, c)))
  //   assert(Expr($, b) unifiable Expr(a, b))
  //   assert(Expr(Expr($, a), Expr(_1, b)) unifiable Expr(Expr(c, a), Expr(c, b)))
  //   assert(!(Expr(Expr($, a), Expr(_1, b)) unifiable Expr(Expr(c, a), Expr(a, b))))
  //   assert(!(Expr(Expr($, a), Expr(_1, b)) unifiable Expr(Expr(a, $), Expr(a, _1))))
  //   assert(Expr(Expr($, a), Expr(_1, a)) unifiable Expr(Expr(b, $), Expr(b, _1)))
  //   assert(Expr(Expr($, a), Expr(_1, b)) unifiable Expr(Expr($, a), Expr(b, _1)))
  //   assert(Expr(Expr(a, $), Expr(_1, b)) unifiable Expr(Expr($, a), Expr(_1, b)))
  //   assert(Expr($, _1, a, _1) unifiable Expr($, _1, _1, a))
  //   assert(!(Expr($, _1, a, _1) unifiable Expr($, _1, _1, b)))
  //   assert(!(Expr($, _1, a, _1) unifiable Expr($, _1, _1, b)))
  //   assert(!(Expr($, a, _1) unifiable Expr(Expr(b, $), $, Expr(_2, _1))))
  //   assert(Expr($, a, _1) unifiable Expr(Expr(b, $), $, Expr($, _1)))
  // }
  // ```

  // shared/src/test/scala/ExprTest.scala
  // ```scala
  // test("unify bindings") {
  //   val $v = Var(-301)
  //   val $w = Var(-302)
  //   assert(Expr.unify(Expr(a, Expr(b, $x), Expr(f, $y, $x)),
  //     Expr(a, Expr(b, $z), Expr(f, $z, Expr(g, $v, $w)))) ==
  //   Map($x.leftMost -> App(App(g, $v), $w),
  //       $y.leftMost -> App(App(g, $v), $w),
  //       $z.leftMost -> App(App(g, $v), $w)))

  //   try
  //     Expr.unifyTo(Expr(`=`, App(App(App(f, $), _1), $), _2), Expr(`=`, App(App($, $), $), $))
  //     assert(false)
  //   catch case Solver.Cycle(r, d) => ()

  //   try
  //     Expr.unifyTo(Expr(`=`, App(App(App(f, $), _1), $), _2), Expr(`=`, App(App(f, $), App(App(_1, $), $)), $))
  //     assert(false)
  //   catch case Solver.Conflict(_, _) => ()
  // }
  // ```

  // shared/src/test/scala/ExprTest.scala
  // ```scala
  // test("unify multiple") {
  //   /*
  //   for all unifiable E1, E2, E3
  //   val m = Expr.unify(E1, E2, E3)
  //   E1.substAbs(m) == E2.substAbs(m) == E3.substAbs(m)
  //   */
  //   assert(Expr.unify(Expr($x, a, $x), $y, Expr(Expr(a, b), $z, Expr($z, b))) == Map(
  //     $x -> Expr(a, b),
  //     $y -> Expr(Expr(a, b), a, Expr(a, b)),
  //     $z -> a
  //   ).map{ case (Var(i), e) => i -> e })

  //   assert(Expr.unify(Expr(a, Expr(a, $x), Expr(a, $x, $y)), Expr($z, Expr($z, b), Expr($z, b, c))) == Map(
  //     $x -> b,
  //     $y -> c,
  //     $z -> a
  //   ).map{ case (Var(i), e) => i -> e })

  //   assert(Expr.unify(
  //     Expr(Expr(f, Var(-11)), Expr(Var(-12), Var(-13))),
  //     Expr(Expr(Var(-20), a), Expr(Var(-22), Var(-23))),
  //     Expr(Expr(Var(-30), Var(-31)), Expr(g, Var(-33))),
  //     Expr(Expr(Var(-40), Var(-41)), Expr(Var(-42), b))
  //   ) == Map(-22 -> g, -40 -> f, -11 -> a, -23 -> b, -30 -> f, -42 -> g, -20 -> f, -33 -> b, -31 -> a, -12 -> g, -13 -> b, -41 -> a))
  // }
  // ```

  '_transform : {
    // shared/src/test/scala/ExprTest.scala
    // ```scala
    // test("transform") {
    //   assert(Expr(A, a, b).transform(Expr(A, $, $), Expr(B, _2, _1)) == Expr(B, b, a))
  
    //   val pair = Var(1000)
    //   val rightItem = Var(1001)
    //   val list = Var(1002)
    //   val head = Var(1003)
    //   val last = Var(1004)
  
    //   {
    //     val data =    Expr(pair, a, b)
    //     val pattern = Expr(pair, a, $)
    //     val template = Expr(rightItem, _1)
    //     assert(data.transform(pattern, template) == Expr(rightItem, b))
    //   }
  
    //   {
    //     val listData = Expr(list, Expr(pair, a, b), Expr(pair, b, c), Expr(pair, A, A))
    //     val listOf3pattern = Expr(list, $, $, $)
    //     val headTemplate = Expr(head, _1)
    //     val lastTemplate = Expr(last, _3)
  
    //     val extremaTemplate = Expr(pair, _1, _3)
  
    //     assert(listData.transform(listOf3pattern, headTemplate) == Expr(head, Expr(pair, a, b)))
    //     assert(listData.transform(listOf3pattern, lastTemplate) == Expr(last, Expr(pair, A, A)))
    //     assert(listData.transform(listOf3pattern, extremaTemplate) == Expr(pair, Expr(pair, a, b), Expr(pair, A, A)))
    //   }
    // }
    // ```

    let new_ref = |r| SExpr::Var(DeBruijnLevel::Ref(NonZeroIsize::new(r).unwrap()));
    let pair       = new_ref(1000);
    let right_item = new_ref(1001);
    let list       = new_ref(1002);
    let head       = new_ref(1003);
    let last       = new_ref(1004);

    let intro = SExpr::Var(DeBruijnLevel::Intro);
    '_1 : {

      let data     = (DyckWord::new_debug_checked(0b_11010),  &[pair, atom(a), atom(b) ][..]);
      let pattern  = (DyckWord::new_debug_checked(0b_11010),  &[pair, atom(a), intro   ][..]);
      let template = (DyckWord::new_debug_checked(0b_110)  ,  &[right_item, new_ref(-1)][..]);
      
      let expected = (DyckWord::new_debug_checked(0b_110)  ,  &[right_item, atom(b)][..]);
      let t1_ret = transform_re_index_small(data, pattern, template).unwrap();
      let t1 = (t1_ret.word, &t1_ret.data[0..t1_ret.len]);
      core::assert_eq!(t1, expected);

    }

    '_2 : {
      let list_data = (
        DyckWord::new_debug_checked(0b_1_11010_0_11010_0_11010_0), 
        &[list, 
                /*(*/ pair, atom(a), atom(b) /*)*/, 
                /*(*/ pair, atom(b), atom(c) /*)*/, 
                /*(*/ pair, atom(A), atom(A) /*)*/, 
        ][..]
      );
      let list_of_3_pattern = (DyckWord::new_debug_checked(0b_1_10_10_10), &[list, intro, intro, intro][..]);

      let head_template     = (DyckWord::new_debug_checked(0b_110)       , &[head, new_ref(-1)        ][..]);
      let last_template     = (DyckWord::new_debug_checked(0b_110)       , &[last, new_ref(-3)        ][..]);
      let extrema_template  = (DyckWord::new_debug_checked(0b_11010)     , &[pair, new_ref(-1), new_ref(-3)][..]);


      macro_rules! template_expected {($($TEMPLATE:ident => ($WORD:literal, $LIST:expr); )+) => {$(
              
        let expected = (DyckWord::new_debug_checked($WORD), &($LIST)[..]);
        let ret = transform_re_index_small(list_data, list_of_3_pattern, $TEMPLATE).unwrap();
        let t = (ret.word, &ret.data[0..ret.len]);
        core::assert_eq!(t, expected);
      )+};}
      template_expected!{
        head_template    => (0b_1_11010_0        , [head, /*(*/ pair, atom(a), atom(b) /*)*/,  ]);
        last_template    => (0b_1_11010_0        , [last,                                     /*(*/ pair, atom(A), atom(A) /*)*/]);
        extrema_template => (0b_1_11010_0_11010_0, [pair, /*(*/ pair, atom(a), atom(b) /*)*/, /*(*/ pair, atom(A), atom(A) /*)*/]);
      }
    }
  }


  '_subst: {
    // shared/src/test/scala/ExprTest.scala
    // ```scala
    // test("subst") {
    //   assert(e1.substRel(Seq(b)) == Expr(f, b, a))
    //   assert(e2.substRel(Seq(a, b)) == Expr(f, a, b, b, a))
    //   assert(e3.substRel(Seq(a, b)) == Expr(f, a, Expr(g, a, b)))
    // }
    // ```

    type DSZU64 = DyckStructureZipperU64;
    let s1 = subst_rel_small((e1.0.current_substructure(), &e1.1, 0), &[(DyckWord::new_debug_checked(1), &[atom(b)][..])                                                  ][..],).unwrap();
    let s2 = subst_rel_small((e2.0.current_substructure(), &e2.1, 0), &[(DyckWord::new_debug_checked(1), &[atom(a)][..]), (DyckWord::new_debug_checked(1), &[atom(b)][..])][..],).unwrap();
    let s3 = subst_rel_small((e3.0.current_substructure(), &e3.1, 0), &[(DyckWord::new_debug_checked(1), &[atom(a)][..]), (DyckWord::new_debug_checked(1), &[atom(b)][..])][..],).unwrap();
    let expected1 = parse("(f b a)");
    let expected2 = parse("(f a b b a)");
    let expected3 = parse("(f a (g a b))");
    core::assert_eq! {(s1.word, &s1.data[0..s1.len]), (expected1.0.current_substructure(), &expected1.1[..])}
    core::assert_eq! {(s2.word, &s2.data[0..s2.len]), (expected2.0.current_substructure(), &expected2.1[..])}
    core::assert_eq! {(s3.word, &s3.data[0..s3.len]), (expected3.0.current_substructure(), &expected3.1[..])}

    // with offset

    macro_rules! make_offset_template {($($NAME:ident $SEXPR:literal $OFFSET:literal;)+) => {$(  
      let tmp_0 = parse($SEXPR);
      let mut tmp_1 = tmp_0.0.current_substructure().zipper();
      tmp_1.decend_right(); 
      let $NAME = (tmp_1.current_substructure(), &tmp_0.1  [$OFFSET..]);
    )+};}
    make_offset_template!{
      d3_fx   "($a $b $c   (f $x))"      3;
      d3_fxgx "($a $b $c   (f $x g $x))" 3;
      d3_fxgy "($a $b $c   (f $x g $y))" 3;
    }

    let s4 = subst_rel_small((d3_fx.0  , d3_fx.1  , 3), &[(DyckWord::new_debug_checked(1), &[atom(a)][..])                                                  ][..],).unwrap();
    let s5 = subst_rel_small((d3_fxgx.0, d3_fxgx.1, 3), &[(DyckWord::new_debug_checked(1), &[atom(a)][..])                                                  ][..],).unwrap();
    let s6 = subst_rel_small((d3_fxgy.0, d3_fxgy.1, 3), &[(DyckWord::new_debug_checked(1), &[atom(a)][..]), (DyckWord::new_debug_checked(1), &[atom(b)][..])][..],).unwrap();
    
    let expected4 = parse("(f a)");
    let expected5 = parse("(f a g a)");
    let expected6 = parse("(f a g b)");

    core::assert_eq! { (s4.word, &s4.data[0..s4.len]), (expected4.0.current_substructure(), &expected4.1[..])}
    core::assert_eq! { (s5.word, &s5.data[0..s5.len]), (expected5.0.current_substructure(), &expected5.1[..])}
    core::assert_eq! { (s6.word, &s6.data[0..s6.len]), (expected6.0.current_substructure(), &expected6.1[..])}
  }




  '_large_subst: {
    // shared/src/test/scala/ExprTest.scala
    // ```scala
    // test("large subst") {
    //   import Expr.*
    //   val `5` = Var(200)
    //   val Z = Var(201)
    //   assert(r1.substRel(Seq(`5`, App(g,App(g,Z)))) == App(App(`=`,App(f,App(App(`,`,`5`),App(g,App(g,App(g,App(g,Z))))))),App(App(h,App(App(`,`,`5`),App(g,a))),App(App(`,`,`5`),App(g,App(g,App(g,Z)))))))
    // }
    // ```

    /*
          [`=`,f,`,`,`5`,g,g,g,g,Z, h,`,`,`5`,g,a,`,`,`5`,g,g,g,Z] 11_110_111_110_000000___1_110_110_00_110_11_110_0000___0
    */

    let _5: SExpr = SExpr::Var(DeBruijnLevel::Ref(NonZeroIsize::new(200).unwrap()));
    let Z: SExpr = SExpr::Var(DeBruijnLevel::Ref(NonZeroIsize::new(201).unwrap()));

    let g = atom(g);
    let h = atom(h);
    let a = atom(a);
    let f = atom(f);

    let s = subst_rel_small((r1.0.current_substructure(), &r1.1, 0), &[(DyckWord::new_debug_checked(1), &[_5]), (DyckWord::new_debug_checked(0b_11100), &[g, g, Z]),]).unwrap();
    core::assert_eq!(
      (s.word, &s.data[0..s.len]),
      (
        DyckWord::new_debug_checked(0b___11_110_111_110_000000___1_110_110_00_110_11_110_0000___0),
        &[atom(sym("=")), f, atom(sym(",")), _5, g, g, g, g, Z, h, atom(sym(",")), _5, g, a, atom(sym(",")), _5, g, g, g, Z][..]
      )
    );
  }  
}







fn to_absolute_mut(data: &mut [SExpr], offset: usize) {
  if offset == 0 {
    return;
  }
  let mut intros = 0;
  for each in data {
    *each = match *each {
      SExpr::Var(DeBruijnLevel::Intro) => unsafe {
        // Safety : offset is !=0 because of if guard
        let tmp = SExpr::Var(DeBruijnLevel::Ref(NonZeroIsize::new_unchecked(-(intros + offset as isize))));
        intros += 1;
        tmp
      },
      SExpr::Var(DeBruijnLevel::Ref(r)) if r.is_negative() => unsafe { SExpr::Var(DeBruijnLevel::Ref(NonZeroIsize::new_unchecked(r.get() + 1 - offset as isize))) },
      a => a,
    }
  }
}
fn to_absolute(data: &[SExpr], offset: usize) -> Vec<SExpr> {
  let mut out = Vec::from(data);
  to_absolute_mut(&mut out, offset);
  out
}

fn to_relative_mut(data: &mut [SExpr]) {
  let mut offset = Option::None;
  let mut intros = 0;
  for each in data {
    *each = match *each {
      SExpr::Var(DeBruijnLevel::Intro) => core::panic!("was not absolute"),
      SExpr::Var(DeBruijnLevel::Ref(r)) if r.is_negative() => match offset {
        Option::None => {
          offset = Option::Some(!r.get());
          intros += 1;
          SExpr::Var(DeBruijnLevel::Intro)
        }
        Option::Some(offset_) => {
          let diff = !r.get() - offset_;
          core::debug_assert!(diff >= 0);
          if intros == diff {
            intros += 1;
            SExpr::Var(DeBruijnLevel::Intro)
          } else {
            // Safety : diff is nonnegative, `!nonnegative` < 0
            SExpr::Var(DeBruijnLevel::Ref(unsafe { NonZeroIsize::new_unchecked(!(diff)) }))
          }
        }
      },
      a => a,
    }
  }
}

fn to_relative(data: &[SExpr]) -> Vec<SExpr> {
  let mut out = Vec::from(data);
  to_relative_mut(&mut out);
  out
}


fn pretty_print(d: &DyckExprSubOutput) {
  std::println!("DyckExperSubOutput(");
  let data = match d {
    DyckExprSubOutput::SmallDyckExpr(SmallDyckExpr { word, len, data }) => {
      std::println!("\tword : {:?}\n\t// {:?}", word, Bits(word.word).dyck_word_app_sexpr_viewer());
      &data[0..*len]
    }
    DyckExprSubOutput::LargeDyckExpr(LargeDyckExpr { word, data }) => {
      std::println!("\tword : {word:#?}");
      &data[..]
    }
  };
  std::println!("\tdata : [");
  for each in data {
    use alloc::string::ToString;
    let (tag, val) = match each {
      SExpr::Var(DeBruijnLevel::Intro) => ("Var ", "$".to_string()),
      SExpr::Var(DeBruijnLevel::Ref(r)) => ("Var ", alloc::format!("$[{}]", r.get())),
      SExpr::Atom(a) => ("Atom", a.0.to_string()),
    };
    std::println!("\t\t{tag} {val}")
  }
  std::println!("]");
  std::println!(")\n");
}


/// This has a fixed capacity of DyckStructureZipperU64::MAX_LEAVES
///
/// any thing after the `len` should be considered junk, this is safe so long as SExpr::<Void> is Copy
#[derive(Debug)]
struct SmallDyckExpr {
  word: DyckWord,
  len : usize,
  data : [SExpr; DyckStructureZipperU64::MAX_LEAVES],
}
#[derive(Debug)]
struct LargeDyckExpr {
  word: Vec<Bits>,
  data: Vec<SExpr>,
}
#[derive(Debug)]
enum DyckExprSubOutput {
  SmallDyckExpr(SmallDyckExpr),
  LargeDyckExpr(LargeDyckExpr),
}


fn subst_re_index_with_pat_offset(pat: (DyckWord, &[SExpr], u8), subs: &[(DyckWord, &[SExpr])]) -> DyckExprSubOutput {
  subst_select::<true,true,false>(pat, (subs, 0), 0)
}

// this can be optimized by inlining the large version and specializing, but given that it would incur more checks, it might not be worth it. on the happy path, the performance is the same
fn subst_re_index_small(pat: (DyckWord, &[SExpr], u8), subs: &[(DyckWord, &[SExpr])]) -> Result<SmallDyckExpr, ()> {
  match subst_re_index_with_pat_offset(pat, subs) {
    DyckExprSubOutput::SmallDyckExpr(s) => Result::Ok(s),
    DyckExprSubOutput::LargeDyckExpr(_) => Result::Err(()),
  }
}




fn subst_select<const WITH_RE_INDEX:bool, const INPUT_OFFSETS : bool, const OUTPUT_OFFSET : bool>(
  (pat_structure, pat_data, pat_offset): (DyckWord, &[SExpr], u8), 
  // the assumption is that all subs come from a match so the offsets would all be the same
  (subs, subs_offset): (&[(DyckWord, &[SExpr])], u8),
  mut output_offset : u8
) -> DyckExprSubOutput {
  #![cfg_attr(rustfmt, rustfmt::skip)]

  if !OUTPUT_OFFSET {
    core::debug_assert_eq!(output_offset, 0);
    output_offset = 0;
  }

  const MAX_LEAVES: usize = DyckStructureZipperU64::MAX_LEAVES;
  core::debug_assert!(pat_data.len() < MAX_LEAVES);
  core::debug_assert!(subs.len() < MAX_LEAVES);
  for each in subs {
    core::debug_assert!(each.1.len() < MAX_LEAVES);
    core::debug_assert!(each.1.len() != 0);
  }


  const MAX_INTROS :usize = 63;
  const INDEX_LEN : usize = MAX_INTROS + 1;
  type Index = [u8; INDEX_LEN];
  const INDEX: Index = [0; INDEX_LEN];

  // stores the the number of consecutive 0 bits
  let mut trailing_pairs = [0u8;MAX_LEAVES];

  let mut pat = PatternData {
    pat_offset,
    pat_intros : pat_offset as u8,

  };

  let mut sub = SubsData { subs, subs_offset };

  let mut out = OutData { 
    dyck_words  : [0_u64; MAX_LEAVES], 
    out_depth   : INDEX,
    output_len  : 0, 
    output_data : [SExpr::Atom(Sym::EMPTY); MAX_LEAVES * MAX_LEAVES],
  };

  if WITH_RE_INDEX{ 
    for each in 1..=pat_offset {
      out.out_depth[each as usize] = each;
    }
  }

  let mut pat_structure_word = pat_structure.word;
  // add terminal 1 bit before shifting fully , avoids counting too many pairs
  pat_structure_word = ((pat_structure_word << 1) | 1) << pat_structure_word.leading_zeros() - 1;

  for each in 0..pat_data.len() {
    
    match pat_data[each] {
      SExpr::Var(DeBruijnLevel::Intro) => for_all_subs::<WITH_RE_INDEX, INPUT_OFFSETS, OUTPUT_OFFSET, false>(&mut pat, &mut sub, &mut out, NonZeroIsize::MAX /* unused */, each, output_offset),
      SExpr::Var(DeBruijnLevel::Ref(r)) if r.is_negative() => { if !INPUT_OFFSETS || (!r.get()) as u8 >= pat_offset {
          for_all_subs::<WITH_RE_INDEX, INPUT_OFFSETS, OUTPUT_OFFSET, true >(&mut pat, &mut sub, &mut out, r, each, output_offset)
        } else {
          core::debug_assert!(false, "There was nothing to substitute")
        }
      }
      val => {
        out.output_data[out.output_len] = val;
        out.dyck_words[each] = 1;
        out.output_len += 1;
      }
    }
    
    // shift off a leaf
    pat_structure_word <<= 1;
    let pairs = pat_structure_word.leading_zeros();
    trailing_pairs[each] = pairs as u8;
    // shift off consecutive pairs
    pat_structure_word <<= pairs;
  }

  return build_dyck_expr_from_subst(pat_data.len(), out.output_len, &out.output_data, &trailing_pairs, &out.dyck_words);


  // Where ...

  struct PatternData {
    pat_offset       : u8,
    pat_intros       : u8,
  }
  impl core::fmt::Debug for PatternData {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
      f.debug_struct("PatternData")
        .field("\n\tpat_offset      ", &self.pat_offset)
        .field("\n\tpat_intros      ", &self.pat_intros)
        .finish()
    }
  }
  struct SubsData<'a> {
    subs        : &'a [(DyckWord, &'a[SExpr])],
    subs_offset : u8
  }
  impl<'a> core::fmt::Debug for SubsData<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
      f.debug_struct("SubsData")
        .field("\n\tsubs            ", &self.subs)
        .field("\n\tsubs_offset     ", &self.subs_offset).finish()
    }
  }
  struct OutData {
    dyck_words : [u64; MAX_LEAVES], 
    out_depth  : Index, 
    output_len : usize, 
    output_data: [SExpr; 1024]
  }
  impl core::fmt::Debug for OutData {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
      f.debug_struct("OutData")
      .field("\n\tdyck_words      ", &self.dyck_words)
      .field("\n\tout_depth       ", &self.out_depth)
      .field("\n\toutput_len      ", &self.output_len)
      .field("\n\toutput_data     ", & unsafe {core::mem::transmute::<_,&[DbgSexpr]>( &self.output_data[0..self.output_len] )}).finish()
    }
  }
  fn for_all_subs<
    const WITH_RE_INDEX : bool, 
    const INPUT_OFFSETS : bool, 
    const OUTPUT_OFFSET : bool, 
    const REF_BRANCH    : bool
  >(
    PatternData { pat_offset, pat_intros } : &mut PatternData,
    SubsData { subs, subs_offset } : &mut SubsData,
    OutData { dyck_words, out_depth, output_len, output_data } : &mut OutData,

    // Ignored if !REF_BRANCH
    ref_value : NonZeroIsize,
    // pattern position/loop iteration
    each : usize,
    output_offset : u8
  ) {
    #![inline(always)]

    let idx = if REF_BRANCH {(!ref_value.get()) as usize} else {*pat_intros as usize};
    let (sub_struct, sub_data) = subs[idx - if INPUT_OFFSETS {*pat_offset as usize}else{0}];
    
    
    let depth_offset = out_depth[if WITH_RE_INDEX {idx } else {0}];

    
    // refs need to know how many intros they passed
    let mut intros_count = 0 as isize;

    let new_ref = |v : isize| 
              { let v_ = v + if INPUT_OFFSETS { *pat_offset as isize } else {0} - if OUTPUT_OFFSET {output_offset as isize} else {0};
                core::debug_assert!( v_ < 0);
                SExpr::Var(DeBruijnLevel::Ref(unsafe { NonZeroIsize::new_unchecked(v_) }))
              };
    for &sub_val in sub_data {
      output_data[*output_len] = if WITH_RE_INDEX {
        match sub_val {
          SExpr::Var(DeBruijnLevel::Ref(r)) if r.is_negative() => {
            let mut r_calc = r.get();
            if INPUT_OFFSETS { r_calc += *subs_offset as isize; }
            new_ref(r_calc - depth_offset as isize)
          },
          SExpr::Var(DeBruijnLevel::Intro) => {
            if REF_BRANCH {
              let val = !(intros_count + depth_offset as isize);
              intros_count += 1;
              
              new_ref(val)
            } else {
              out_depth[idx + 1] += 1;
              sub_val
            }
          }
          _ => sub_val,
        }
      } else {
        // reminder : !WITH_RE_INDEX
        sub_val
      };
      *output_len += 1;
    }
    dyck_words[each] = sub_struct.word;
    
    if !REF_BRANCH {
      out_depth[idx+1] += out_depth[idx];
      *pat_intros += 1;
    }
  }

  fn build_dyck_expr_from_subst(
    input_len: usize,
    output_len: usize,
    output_data: &[SExpr; MAX_LEAVES * MAX_LEAVES],
    trailing_pairs: &[u8; MAX_LEAVES],
    dyck_words: &[u64; MAX_LEAVES],
  ) -> DyckExprSubOutput {
    #![inline(always)]
  
    let mut output_word_len = 0;
    let [mut cur, mut next] = [0_u64; 2];
    let mut finished = Vec::new();
    let mut last_div = 0;
  
    for each in (0..input_len).rev() {
      output_word_len += trailing_pairs[each] as usize;
      let (cur_div, cur_mod) = (output_word_len / 64, output_word_len % 64);
    
      // check if we need to advance the "cursor"
      if last_div < cur_div {
        core::debug_assert!(output_len > DyckStructureZipperU64::MAX_LEAVES);
        if finished.len() == 0 {
          finished = Vec::with_capacity(DyckStructureZipperU64::MAX_LEAVES);
        }
        finished.push(cur);
        (cur, next) = (next, 0);
      }
    
      let cur_word = dyck_words[each];
    
      [cur, next] = [cur | cur_word << cur_mod, if cur_mod == 0 { 0 } else { next | cur_word >> u64::BITS - cur_mod as u32 }];
      output_word_len += (u64::BITS - cur_word.leading_zeros()) as usize;
      last_div = cur_div;
    }
  
    let data = Vec::from(&output_data[0..output_len]);
  
    if next == 0 && finished.len() == 0 {
      let mut data = [SExpr::Var(DeBruijnLevel::Intro); 32];
      for each in 0..output_len {
        data[each] = output_data[each];
      }
    
      DyckExprSubOutput::SmallDyckExpr(SmallDyckExpr { word: DyckWord::new_debug_checked(cur), data , len : output_len})
    } else {
      let data = Vec::from(&output_data[0..output_len]);
    
      finished.push(cur);
      if next != 0 || cur.leading_zeros() == 0 {
        finished.push(next);
      }
      finished.reverse();
    
      DyckExprSubOutput::LargeDyckExpr(LargeDyckExpr { word: unsafe { core::mem::transmute(finished) }, data })
    }
  }
  // end of subst_select
}

fn expr_matches<'a>((lhs_structure, lhs_data): (DyckWord, &'a [SExpr]), (rhs_structure, rhs_data): (DyckWord, &'a [SExpr])) -> Option<(Vec<(DyckWord, &'a [SExpr])>, Vec<(DyckWord, &'a [SExpr])>)> {
  return expr_matches_select::<false>((lhs_structure, lhs_data, 0), (rhs_structure, rhs_data, 0));
}

fn expr_matches_with_offsets<'a>((lhs_structure, lhs_data, lhs_offset): (DyckWord, &'a [SExpr], u8), (rhs_structure, rhs_data, rhs_offset): (DyckWord, &'a [SExpr], u8)) -> Option<(Vec<(DyckWord, &'a [SExpr])>, Vec<(DyckWord, &'a [SExpr])>)> {
  return expr_matches_select::<false>((lhs_structure, lhs_data, lhs_offset), (rhs_structure, rhs_data, rhs_offset));
}

/// this will return the substitutions when they match, but the offsets are still "baked" into the result.
fn expr_matches_select<'a, const WITH_OFFSET : bool>((lhs_structure, lhs_data, mut lhs_offset): (DyckWord, &'a [SExpr], u8), (rhs_structure, rhs_data, mut rhs_offset): (DyckWord, &'a [SExpr], u8)) -> Option<(Vec<(DyckWord, &'a [SExpr])>, Vec<(DyckWord, &'a [SExpr])>)> {
  #![cfg_attr(rustfmt, rustfmt::skip)]
  const MAX_LEAVES: usize = DyckStructureZipperU64::MAX_LEAVES;

  if !WITH_OFFSET {
    core::debug_assert_eq!(lhs_offset,0);
    core::debug_assert_eq!(rhs_offset,0);
    lhs_offset = 0;
    rhs_offset = 0;
  }

  core::debug_assert! {lhs_data.len() <= MAX_LEAVES}
  core::debug_assert! {rhs_data.len() <= MAX_LEAVES}

  let mut l_struct = lhs_structure.zipper();
  let mut r_struct = rhs_structure.zipper();

  let mut lvars = Vec::new();
  let mut rvars = Vec::new();

  'match_or_decend_left: loop {
    
    use DeBruijnLevel::*;
    use SExpr::*;

    let append_l = |l : &mut Vec<_>| l.push((r_struct.current_substructure(), &rhs_data[r_struct.current_leaf_store_index_range()]));
    let append_r = |r : &mut Vec<_>| r.push((l_struct.current_substructure(), &lhs_data[l_struct.current_leaf_store_index_range()]));
    let matching =  match [
      (l_struct.current_is_leaf(), lhs_data[l_struct.current_first_leaf_store_index()]),
      (r_struct.current_is_leaf(), rhs_data[r_struct.current_first_leaf_store_index()]),
    ] {
      // /////////
      // Intros //
      // /////////
      [(true, Var(Intro)), (true, Var(Intro))] => { append_l(&mut lvars); append_r(&mut rvars); true } 
      [(true, Var(Intro)), _]                  => { append_l(&mut lvars);                       true }
      [_, (true, Var(Intro))]                  => {                       append_r(&mut rvars); true }

      // ////////
      // Atoms //
      // ////////
      [(true, Atom(l)), (true, Atom(r))]                            => l == r,
      [(false, _), (true, Atom(_))] | [(true, Atom(_)), (false, _)] => false,

      [(true, Var(Ref(v))), (true, a @ Atom(_))] => { let idx_l = (!v.get()) as usize; !v.is_positive() &&  (!WITH_OFFSET || idx_l >= lhs_offset as usize) && lvars[idx_l - lhs_offset as usize].1 == &[a] } 
      [(true, a @ Atom(_)), (true, Var(Ref(v)))] => { let idx_r = (!v.get()) as usize; !v.is_positive() &&  (!WITH_OFFSET || idx_r >= rhs_offset as usize) && rvars[idx_r - rhs_offset as usize].1 == &[a] } 
      

      // ///////
      // Refs //
      // ///////
      [(true, l @ Var(Ref(lv_r))), (true, r @ Var(Ref(rv_r)))] => match [lv_r.is_positive(), rv_r.is_positive()] {
        [false, false] => matching_refs_offset_rel_rel::<WITH_OFFSET>([(lv_r, lhs_offset as usize, &lvars), (rv_r, rhs_offset as usize, &rvars)]),
        [true , true ] => lv_r == rv_r,
        [true , false] => { let idx = (!rv_r.get()) as usize; (!WITH_OFFSET || idx >= rhs_offset as usize) && rvars[idx - rhs_offset as usize].1 == &[l] }
        [false, true ] => { let idx = (!lv_r.get()) as usize; (!WITH_OFFSET || idx >= lhs_offset as usize) && lvars[idx - lhs_offset as usize].1 == &[r] }
      },
      [(false, _), (true, Var(Ref(_)))] | [(true, Var(Ref(_))), (false, _)] => false,

      // /////////
      // Decend //
      // /////////
      [(false, _), (false, _)] => {
        core::assert!(l_struct.decend_left() && r_struct.decend_left());
        continue 'match_or_decend_left;
      },
    };

    if !matching {
      return Option::None;
    }

    if let std::ops::ControlFlow::Break(matching) = go_right_or_accend_together(&mut l_struct, &mut r_struct) {
      return matching.then_some((lvars, rvars))
    }
  };
  
  // Where ...

  fn go_right_or_accend_together<'a>(l_struct: &mut DyckStructureZipperU64, r_struct: &mut DyckStructureZipperU64)->core::ops::ControlFlow<bool, ()>{
    use core::ops::ControlFlow as CF;
    loop {
      match [l_struct.left_to_right(), r_struct.left_to_right()] {
        [true, true] => return CF::Continue(()),
        [true, false] | [false, true] => return CF::Break(false),
        [false, false] => {
          let l_up = l_struct.accend();
          let r_up = r_struct.accend();
          if !l_up {
            core::debug_assert!(!r_up);
            return CF::Break(true);
          }
        }
      }
    }
  }

  fn matching_refs_offset_rel_rel<const WITH_OFFSET : bool>([(lv_r, mut lhs_offset, lvars), (rv_r, mut rhs_offset, rvars)]: [(std::num::NonZero<isize>, usize, &[(DyckWord, &[SExpr])]);2])->bool{
    if !WITH_OFFSET {
      core::debug_assert_eq!(lhs_offset,0);
      core::debug_assert_eq!(rhs_offset,0);
      lhs_offset = 0;
      rhs_offset = 0;
    }
    let idx_l = (!lv_r.get()) as usize;
    let idx_r = (!rv_r.get()) as usize;

    if WITH_OFFSET && (idx_l < lhs_offset || idx_r < rhs_offset) {
      return false;
    }

    let left = lvars[idx_l - lhs_offset];
    let right = rvars[idx_r - rhs_offset];
    
    // trivial case
    if lhs_offset == rhs_offset
    {
      return left == right 
    }
    
    // non-trivial case
    if left.0 != right.0 {
      return false;
    }
    for each in left.1.iter().zip(right.1.iter()) {
      use DeBruijnLevel::*;
      use SExpr::*;
      let matching = match each {
        (Atom(l), Atom(r)) => l == r,
        (Var(Intro), Var(Intro)) => true,
        (Var(Ref(l)), Var(Ref(r))) => 
          if !WITH_OFFSET || l.is_positive() && r.is_positive() { 
            l == r 
          } else {
            (!l.get()) as usize - lhs_offset == (!r.get()) as usize - rhs_offset 
          }
        _ => false
      };
      if !matching {
        return false;
      }
    }
    true
  }
}



fn transform_re_index(
  arg: (DyckWord, &[SExpr]),
  pat: (DyckWord, &[SExpr]),
  template: (DyckWord, &[SExpr])
)-> Option<DyckExprSubOutput>{
  let arg = (arg.0, arg.1, 0);
  let pat = (pat.0, pat.1, 0);
  let template = (template.0, template.1, 0);
  transform_select::<true, false, false>(arg, pat, template,0)
}
  fn transform_re_index_small(
  arg: (DyckWord, &[SExpr]),
  pat: (DyckWord, &[SExpr]),
  template: (DyckWord, &[SExpr])
)-> Option<SmallDyckExpr>{
  if let Option::Some(DyckExprSubOutput::SmallDyckExpr(s)) = transform_re_index(arg, pat, template)
  {
    Option::Some(s) 
  } else {
    Option::None
  }
}

fn transform_select<const WITH_RE_INDEX : bool, const SUBS_OFFSET : bool, const OUTPUT_OFFSET : bool>(
  args          : (DyckWord, &[SExpr], u8),
  pat           : (DyckWord, &[SExpr], u8),
  template      : (DyckWord, &[SExpr], u8),
  output_offset : u8,
)-> Option<DyckExprSubOutput>{
  let subs = expr_matches_select::<SUBS_OFFSET>(args, pat)?;
  Option::Some(subst_select::<WITH_RE_INDEX, SUBS_OFFSET, OUTPUT_OFFSET>(template, (&subs.1, pat.2), output_offset))
}


fn subst_rel(pat: (DyckWord, &[SExpr], u8), subs: &[(DyckWord, &[SExpr])]) -> DyckExprSubOutput {
  subst_select::<false, true, false>(pat, (subs, 0), 0)
}

// this can be optimized by inlining the large version and specializing, but given that it would incur more checks, it might not be worth it. on the happy path, the performance is the same
fn subst_rel_small(pat: (DyckWord, &[SExpr], u8), subs: &[(DyckWord, &[SExpr])]) -> Result<SmallDyckExpr, ()> {
  match subst_rel(pat, subs) {
    DyckExprSubOutput::SmallDyckExpr(s) => Result::Ok(s),
    DyckExprSubOutput::LargeDyckExpr(_) => Result::Err(()),
  }
}




