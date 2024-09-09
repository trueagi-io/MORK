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
};
use num_bigint::BigUint;
use std::{
  ascii,
  env::var,
  fmt::{Debug, Display},
  num::{NonZeroIsize, NonZeroUsize},
  ops::Neg,
  process::Output,
  usize,
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
    Self { structure: 1, current_depth: 0, stack  }
  };

  /// Creates a Zipper for the Dyck Path, if the tree is empty (Dyck path of all 0s), it will return [`Option::None`]; this avoids uneeded checks when traversing.
  /// A valid Zipper is therefore always on a non-empty tree.
  /// Validating the structure of a Zipper is costly, so it is only checked in debug builds (TODO: is there a fast algorithm for doing the check using bit shifts and masks?).
  pub const fn new(structure: u64) -> Option<Self> {
    if let 0 = structure {
      return Option::None;
    }

    #[cfg(debug_assertions)]
    '_validate_structure: {
      let trailing = structure.leading_zeros();
      core::debug_assert!(trailing != 0);

      let mut cursor = 1 << u64::BITS - trailing - 1;
      let mut sum: i32 = 0;

      // a valid structure must have enough children to pair up before constructing a branch
      loop {
        core::debug_assert!(!sum.is_negative());
        if cursor == 0 {
          core::debug_assert!(1== sum);
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
      unsafe { self.left_to_right_unchecked() };
      true
    } else {
      false
    }
  }

  /// Switch from a left branch to the sibling right branch. Invariants are enfored in debug builds.
  pub unsafe fn left_to_right_unchecked(&mut self) {
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
  pub fn left_to_right(&mut self) -> bool {
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

    unsafe { self.left_to_right_unchecked() }

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
  pub unsafe fn right_to_left_unchecked(&mut self) {
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
  pub fn right_to_left(&mut self) -> bool {
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

    unsafe { self.right_to_left_unchecked() };

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
  pub fn at_root(&self) -> bool {
    self.current_depth == 0
  }
  // This moves in a cycle. so if you return to the root and make this call, it will start the iteration again
  pub fn next_depth_first_left_to_right_action(&self) -> DFSLeftToRightAction {
    core::todo!("ADD TESTS");

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
    core::todo!("ADD TESTS");

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

    core::todo!("ADD TESTS");

    // the iterator state
    let mut tmp = self.clone();
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
  pub fn current_substructure(&self) -> u64 {
    let SubtreeSlice { terminal, head } = self.stack[self.current_depth as usize];
    ((1 << terminal) - 1 & self.structure) >> head
  }

  // /// Match the self argument with the pattern. As Zippers must have at least one element, an empty template should have [`Option::None`] as the template argument with the template data being `&[]`
  // pub fn match_template_at_current<E: MatchElement>(
  //   self: &Self,
  //   self_data: &[E::Element],
  //   pattern: &Self,
  //   pattern_data: &[E::Element],
  //   template: Option<&Self>,
  //   template_data: &[E::Element],
  //   var_table: &E::VarTable,
  // ) -> Option<(Vec<LeafBranch>, Vec<E::Element>)>
  // where
  //   E::Element: Clone,
  // {
  //   core::debug_assert_eq!(self.structure.count_ones() as usize, self_data.len());
  //   core::debug_assert_eq!(pattern.structure.count_ones() as usize, pattern_data.len());

  //   #[track_caller]
  //   fn get_binding_index<E: MatchElement>(var_table: &<E as MatchElement>::VarTable, v: &E::Var) -> usize {
  //     let DebruijnLevel::Ref(l) = E::var_de_bruin_level(var_table, v) else {
  //       core::panic!("The variables should have been in the table already! {:?}", core::panic::Location::caller())
  //     };
  //     (!l.get()) as usize
  //   };

  //   // initialize zippers
  //   type DZ = DyckStructureZipperU64;
  //   const NULL_ZIPPER: DZ = DZ { structure: 0, current_depth: 0, stack: [SubtreeSlice::zeroes(); DZ::MAX_LEAVES] };
  //   fn init_sub_zipper(z: &DZ) -> DZ {
  //     let mut z1 = DZ { structure: z.structure, ..NULL_ZIPPER };
  //     z1.stack[0] = z.stack[z.current_depth as usize];
  //     z1
  //   }

  //   let maybe_template_z = if let Option::Some(t) = template {
  //     core::debug_assert_eq!(t.structure.count_ones() as usize, template_data.len());
  //     Option::Some(init_sub_zipper(t))
  //   } else {
  //     core::debug_assert_eq!(0, template_data.len());
  //     Option::None
  //   };
  //   let [mut self_z, mut pattern_z] = [self, pattern].map(init_sub_zipper);

  //   // initialize substitution table
  //   let mut de_bruin_level_offset: Option<usize> = Option::None;
  //   let mut de_bruin_offset_bindings_to_self = [Option::None; Self::MAX_LEAVES];

  //   // dfs the pattern and follow along with the argument
  //   'matching: loop {
  //     if pattern_z.current_is_leaf() {
  //       match E::element_type(&pattern_data[pattern_z.current_first_leaf_store_index()]) {
  //         ElementType::Atom(pat_atom) => {
  //           if !self_z.current_is_leaf() {
  //             return Option::None;
  //           }
  //           match E::element_type(&self_data[self_z.current_first_leaf_store_index()]) {
  //             ElementType::Atom(self_atom) => {
  //               if !E::atom_eq(self_atom, pat_atom) {
  //                 return Option::None;
  //               }
  //             }
  //             ElementType::Var(_) => core::unimplemented!("This matching algoritm does not do unification!"),
  //           }
  //         }
  //         ElementType::Var(v) => {
  //           let level = get_binding_index::<E>(var_table, v);

  //           match de_bruin_level_offset {
  //             Option::None => de_bruin_level_offset = Option::Some(level),

  //             Option::Some(offset) => core::debug_assert!(offset <= level),
  //           }
  //           let idx = level - de_bruin_level_offset.unwrap_or(0);
  //           de_bruin_offset_bindings_to_self[idx] = Option::Some(self_z.stack[self_z.current_depth as usize]);
  //         }
  //       }

  //       '_pop: {
  //         while !pattern_z.current_is_left_branch() {
  //           if pattern_z.accend() {
  //             self_z.accend();
  //           } else {
  //             break 'matching;
  //           }
  //         }

  //         // Safety: the reaching the end of the while loop
  //         //   guarantees that we are on a left branch, so there must be a right branch
  //         unsafe {
  //           pattern_z.left_to_right_unchecked();
  //           self_z.left_to_right_unchecked();
  //         };
  //       }
  //     } else {
  //       // current is a branch
  //       let both_left = self_z.decend_left() && pattern_z.decend_left();
  //       if !both_left {
  //         return Option::None;
  //       }
  //     }
  //   }

  //   let Option::Some(mut template_z) = maybe_template_z else {
  //     return Option::Some((Vec::new(), Vec::new()));
  //   };

  //   // construct from the template
  //   let mut structure = Vec::with_capacity(32);
  //   let mut values = Vec::with_capacity(32);

  //   self_z.accend_to_root();

  //   let out = 'templating: loop {
  //     if template_z.decend_left() {
  //       continue 'templating;
  //     }

  //     let e = &template_data[template_z.current_first_leaf_store_index()];
  //     match E::element_type(e) {
  //       ElementType::Atom(_) => '_push_atom: {
  //         values.push(e.clone());
  //         structure.push(LeafBranch::L)
  //       }
  //       ElementType::Var(v) => '_push_binding: {
  //         let level = get_binding_index::<E>(var_table, v);
  //         let Option::Some(offset) = de_bruin_level_offset else { core::panic!() };
  //         let Option::Some(binding) = de_bruin_offset_bindings_to_self[level - offset] else { core::panic!() };

  //         self_z.stack[0] = binding;

  //         let indices = self_z.current_leaf_store_index_range();
  //         values.extend_from_slice(&self_data[indices]);

  //         let sub_structure = self_z.structure >> binding.head;
  //         let mut bit_ptr = 1_u64 << binding.terminal - binding.head - 1;

  //         '_convert_subtree_structure: while bit_ptr != 0 {
  //           structure.push(if bit_ptr & sub_structure == 0 { LeafBranch::B } else { LeafBranch::L });
  //           bit_ptr >>= 1;
  //         }
  //       }
  //     }

  //     '_pop: while !template_z.left_to_right() {
  //       if !template_z.accend() {
  //         core::debug_assert_eq!(structure.iter().filter(|s| **s == LeafBranch::L).count(), values.len());
  //         break 'templating Option::Some((structure, values));
  //       }
  //       structure.push(LeafBranch::B);
  //     }
  //   };

  //   out
  // }
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
  fn var_de_bruin_level(table: &Self::VarTable, var: &Self::Var) -> DebruijnLevel;
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
    core::assert!(!tree_0b_1.right_to_left());
    core::assert!(!tree_0b_1.left_to_right());
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
    core::assert!(!tree_0b_110.right_to_left());
    core::assert!(!tree_0b_110.left_to_right());
    core::assert_eq!(tree_0b_110.current_first_leaf_store_index(), 0);
    core::assert_eq!(tree_0b_110.current_leaf_store_index_range(), 0..count);
    core::assert!(!tree_0b_110.accend());

    // cycle counterclockwise
    core::assert!(tree_0b_110.decend_left());
    core::assert_eq!(tree_0b_110.current_first_leaf_store_index(), 0);
    core::assert_eq!(tree_0b_110.current_leaf_store_index_range(), 0..1);
    core::assert!(tree_0b_110.left_to_right());
    core::assert_eq!(tree_0b_110.current_first_leaf_store_index(), 1);
    core::assert_eq!(tree_0b_110.current_leaf_store_index_range(), 1..count);
    core::assert!(tree_0b_110.accend());

    // back to root
    core::assert_eq!(tree_0b_110.current_leaf_store_index_range(), 0..count);

    // cycle clockwise
    core::assert!(tree_0b_110.decend_right());
    core::assert_eq!(tree_0b_110.current_first_leaf_store_index(), 1);
    core::assert_eq!(tree_0b_110.current_leaf_store_index_range(), 1..count);
    core::assert!(tree_0b_110.right_to_left());
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
    core::assert!(!tree_0b_11010.right_to_left());
    core::assert!(!tree_0b_11010.left_to_right());
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

    core::assert!(tree_0b_11010.right_to_left());
    std::println!("{:#?}", tree_0b_11010);

    core::assert!(tree_0b_11010.decend_right());
    std::println!("{:#?}", tree_0b_11010);
    core::assert!(!tree_0b_11010.decend_left());
    core::assert_eq!(tree_0b_11010.current_first_leaf_store_index(), 1);
    core::assert_eq!(tree_0b_11010.current_leaf_store_index_range(), 1..2);
    core::assert!(!tree_0b_11010.decend_right());

    core::assert!(tree_0b_11010.right_to_left());
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

// #[cfg_attr(rustfmt, rustfmt::skip)]
// #[test]
// fn test_naive_matching() {

//   fn test_matcher(src: &str) {
//     let mut parser = DyckParser::new(src);
//     parser.thread_variables(Option::Some(Variables::new()));
//     let mut next = || parser.next().unwrap().unwrap();
//     let (   input_zipper,    input_data, _) = next();
//     let ( pattern_zipper,  pattern_data, _) = next();
//     let (template_zipper, template_data, _) = next();
//     let (expected_zipper, expected_data, _) = next();
//     let vars = parser.thread_variables(Option::None).unwrap();

//     let structure = expected_zipper.structure;

//     let expected_structure = '_convert_dyck_word : {
//       let mut structure_vec = Vec::new();
//       let mut cursor = 1 << (u64::BITS - structure.leading_zeros() - 1);
//       core::debug_assert_ne!(cursor & structure, 0);
//       while cursor !=0 {
//         structure_vec.push(if cursor & structure == 0 { LeafBranch::B } else { LeafBranch::L });
//         cursor >>= 1;
//       }
//       structure_vec
//     };

//     let result = DyckStructureZipperU64::match_template_at_current::<TestExpr>(
//       &input_zipper,
//       &input_data,
//       &pattern_zipper,
//       &pattern_data,
//       Option::Some(&template_zipper),
//       &template_data,
//       &vars
//     ).unwrap();

//     core::assert_eq!(&result.0[..], &expected_structure[..]);
//     core::assert_eq!(&result.1[..], &expected_data[..]);
//   }

//   let src1 = "
//     (a $X (b c)) ;; input
//     (a $  $Y)    ;; pattern
//     (x $Y)       ;; template
//     (x (b c))    ;; expected
//     ";
//   test_matcher(src1);

//   let src2 ="
//     (Point2d (X 15.4) (Y -34.9)) ;; input
//     (Point2d (X   $X) (Y    $Y)) ;; pattern

//     (Sqrt (+ (*    $X    $X)
//              (*    $Y    $Y)))   ;; template
//     (Sqrt (+ (*  15.4  15.4)
//              (* -34.9 -34.9)))   ;; expected
//   ";
//   test_matcher(src2);

//   let src3 = "
//     (Point2d (X (+ 3.0 2.2)) (Y -34.9))     ;; input
//     (Point2d (X          $X) (Y    $Y))     ;; pattern

//     (Sqrt (+ (*           $X          $X)
//              (*           $Y          $Y))) ;; template
//     (Sqrt (+ (*  (+ 3.0 2.2)  (+ 3.0 2.2))
//              (*        -34.9       -34.9))) ;; expected
//   ";
//   test_matcher(src3);
// }

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DebruijnLevel {
  Intro,
  Ref(core::num::NonZeroIsize),
}
impl DebruijnLevel {
  fn as_index(self) -> usize {
    match self {
      DebruijnLevel::Intro => 0,
      DebruijnLevel::Ref(nzu) => (!nzu.get()) as usize,
    }
  }
}
#[derive(Debug, Clone, PartialEq)]
pub struct Variables {
  /// de bruin levels, but the indexing for the first variable starts at 1 instead of 0, 0 represents the introduction of a variable
  store: Vec<(usize, Sym)>,
  absolute: Option<usize>,
}
impl Variables {
  fn new() -> Variables {
    Variables { store: Vec::new(), absolute: Option::None }
  }
  fn aquire_de_bruin(&mut self, pos: usize, sym: Sym) -> DebruijnLevel {
    if let level @ DebruijnLevel::Ref(_) = self.lookup(sym) {
      return level;
    }
    self.store.push((pos, sym));
    if let Option::Some(v) = self.absolute {
      //Safety: We just pushed to the vec, so len > 0
      return DebruijnLevel::Ref(unsafe { core::num::NonZeroIsize::new_unchecked(!((self.store.len() + v) as isize - 1)) });
    }
    DebruijnLevel::Intro
  }

  fn clear(&mut self) {
    self.store.clear();
  }

  /// returns DebruijnLevel::Intro if the value is not yet in the table
  fn lookup(&self, sym: Sym) -> DebruijnLevel {
    let offset = self.absolute.unwrap_or(0);
    let mut idx = self.store.len();
    while idx != 0 {
      idx -= 1;
      if self.store[idx].1 == sym {
        // Safety: `idx` never enters the loop if it is equal to `0`
        return DebruijnLevel::Ref(unsafe { core::num::NonZeroIsize::new_unchecked(!((idx + offset) as isize)) });
      }
    }
    DebruijnLevel::Intro
  }

  fn to_relative(&mut self) {
    self.absolute = Option::None
  }
  fn to_absolute(&mut self, offset: usize) {
    self.absolute = Option::Some(offset)
  }
}

// if string interning is slow, it could be split into buckets, and use a ReadWrite lock, perhaps even Semaphores. but for testing this should be enough
static INTERNED_STR: std::sync::Mutex<alloc::collections::BTreeSet<&'static str>> = std::sync::Mutex::new(alloc::collections::BTreeSet::new());

// Sym is valid if it has an empty str, or if it holds and interned str.
#[derive(Debug, Clone, Copy, PartialOrd, Ord, Eq)]
pub struct Sym(&'static str);
impl Sym {
  const EMPTY : Self = Sym("");
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

/// An empty enum to make recursive cases not constructable
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Void {}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SExpr<A = Void> {
  Var(DebruijnLevel),
  Atom(Sym),
  App(App<A>),
}

// enum TestExpr {}
// #[cfg_attr(rustfmt, rustfmt::skip)]
// impl MatchElement for TestExpr {
//   type Element = Sexpr;
//   type Atom    = Sym;
//   type Var     = (DebruijnLevel, Sym);
//   type VarTable = Variables;

//   fn element_type(e: &Self::Element) -> ElementType<Self::Atom, Self::Var> {
//     match e {
//       SExpr::<Void>::Atom(a) => ElementType::Atom(a),
//       SExpr::<Void>::Var(v) => ElementType::Var(v),
//       SExpr::<Void>::App(_)=> core::unreachable!(),
//     }
//   }

//   fn atom_eq(left: &Self::Atom, right: &Self::Atom) -> bool { left == right }

//   fn var_de_bruin_level(table: &Variables,var: &Self::Var) -> DebruijnLevel {
//     let DebruijnLevel::Ref(_) =  var.0 else {return table.lookup(var.1) };
//     var.0.clone()
//   }
// }

struct DbgSexpr<'a, A>(&'a SExpr<A>);
impl<'a, A: Debug> core::fmt::Debug for DbgSexpr<'a, A> {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    #[cfg_attr(rustfmt, rustfmt::skip)]
      match &self.0 {
        SExpr::Var(DebruijnLevel::Intro)  => core::write!(f,"$"),
        SExpr::Var(DebruijnLevel::Ref(i)) => core::write!(f,"$[{i}]"),
        SExpr::Atom(Sym(sym))            => core::write!(f,"{sym}"),
        SExpr::App(App(l,r))             => core::write!(f,"({l:?} {r:?})"),
      }
  }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct App<A>(A, A);

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

/// The Dyck Parser can either make applicative or list Sexprs into Zippers. The difference is very slight, so the implementation of each looks similar, but they are marked with !!! to show th differences
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
  fn thread_variables(&mut self, mut vars: Option<Variables>) -> Option<Variables> {
    core::mem::swap(&mut vars, &mut self.threaded_variables);
    vars
  }
  /// the applicative representation
  #[cfg_attr(rustfmt, rustfmt::skip)]
  pub fn parse_first_sexrs_to_dyck_app_repr(&mut self) -> Option<Result<(DyckStructureZipperU64, Vec<SExpr>, Variables), ParseErr>> {
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
                                           // !!!
                                           state.dyck_word<<=1;
                                         }
                                         _ => {}
                                       }
                                       if !state.pop() { break 'build_sexpr; }
                                       // !!!
                                       if state.list_length > 1 { state.dyck_word<<=1 }
                                     },
            TokenType::Var(sym)  => { if let Result::Err(e) = state.make_var(sym)  { return err(e) }
                                      // !!!
                                      if state.list_length > 1 { state.dyck_word<<=1 }
                                    }
            TokenType::Atom(sym) => { if let Result::Err(e) = state.make_atom(sym) { return err(e) }
                                      // !!!
                                      if state.list_length > 1 { state.dyck_word<<=1 }
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

  /// the list representation
  #[cfg_attr(rustfmt, rustfmt::skip)]
  pub fn parse_first_sexrs_to_dyck_list_repr(&mut self) -> Option<Result<(DyckStructureZipperU64, Vec<SExpr>, Variables), ParseErr>> {
    let err = |e| Option::Some(Result::Err(e));

    let mut state = match DyckParserIterState::init(self) {
        Result::Ok(s) => s?,
        Result::Err(e) => return err(e),
    };

    'build_sexpr : while let Option::Some(result) = state.next_token() {
      match result {
        Result::Err(e)                  => return err(e),
        Result::Ok(Token { r#type,.. }) =>
          match r#type {
            TokenType::LPar      => if let Result::Err(e) = state.push() { return err(e); },
            TokenType::RPar      => { match state.list_length {
                                        0 => state.make_empty(),
                                        1 => state.make_singleton(),
                                        _ => {}
                                      }
                                      // !!!
                                      for _ in 0..state.list_length-1 { state.dyck_word<<=1 }

                                      if !state.pop() { break 'build_sexpr; }
                                    },
            TokenType::Var(sym)  => if let Result::Err(e) = state.make_var(sym)  { return err(e) },
            TokenType::Atom(sym) => if let Result::Err(e) = state.make_atom(sym) { return err(e) },
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
      // continue;
      #[allow(unreachable_code)]
      match _each {
        Result::Ok((zip, store, vars)) => {
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
        Result::Err(e) => std::println!("{e:?}"),
      }
    }
  }
  let end = start.elapsed().as_millis();
  std::println!("count : {count}\ntime : {end}")
}

#[cfg_attr(rustfmt, rustfmt::skip)]
#[allow(non_snake_case)]
#[test]
fn test_examples(){
  let sym = |c| Sym::new(c); 
  let [f,g,h] = ["f", "g", "h"].map(sym); 
  let [a,b,c] = ["a", "b", "c"].map(sym); 
  let [A,B,C] = ["A", "B", "C"].map(sym);
  let S = sym("S");
  let [eq,comma,colon,arrow,star,plus] = ["=", ",", ":", "-->", "*", "+"].map(sym);

  let parse = |src| DyckParser::new(src).next().unwrap().unwrap();
  type ParserOutput = (DyckStructureZipperU64, Vec<SExpr>, Variables);
  let [e1,e2,e3,r1] = [
    "(f $x a)",
    "(f $x $y $y $x)",
    "(f $y (g $y $x))",
    "(= (nTimes (, $x (S (S $n)))) (Plus (, $x (S Z)) (, $x (S $n))))",
  ].map(parse);
  
  fn atom(a : Sym)->SExpr {SExpr::Atom(a)}
  fn atoms<const L : usize>(a : [Sym; L])->[SExpr;L] {a.map(SExpr::Atom)}
  
  '_foldMap_size_fvars :{
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
    let size = |&(DyckStructureZipperU64 { structure, ..},_,_) : &ParserOutput| u64::BITS - structure.leading_zeros();
    let fvars = |(_,data,_) : &ParserOutput| data.iter().copied().filter(|e| match e {
      SExpr::Atom(_) => true,
      _ => false,
    }).collect::<Vec<_>>();
    
    core::assert_eq!(size(&e1), 5);
    core::assert_eq!(&fvars(&e1), &atoms([f,a]));
    
    core::assert_eq!(size(&e2), 9);
    core::assert_eq!(&fvars(&e2), &atoms([f]));
    
    core::assert_eq!(size(&e3), 9);
    core::assert_eq!(&fvars(&e3), &atoms([f,g]));
    
    core::assert_eq!(size(&r1), 31);
    core::assert_eq!(&fvars(&r1), &atoms([eq, sym("nTimes"), comma, S, S, sym("Plus"), comma, S, sym("Z"), comma, S]));
  }

  '_toAbsolute_toRelative : {
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
  
    // `toAbsolute` variables are "classical", Introductions are removed, an offset is added
    // `toRelative` variables use Debruijn Levels, Introductions are given a different value
    
    // the current form is making use of the fact that it remembers what symbols were used to generated the expr,
    // !TODO consider creating an anonymization technique of the variables

  //   let to_absolute = |p : &ParserOutput, offset : usize| {
  //     let mut p1 = p.clone();
  //     let (_,p_data,p_vars) = &mut p1;
  //     p_vars.to_absolute(offset);
  //     for each in p_data.iter_mut() { if let SExpr::Var((_, s)) = each { *each=SExpr::Var((p_vars.lookup(*s),*s)) };}
  //     p1
  //   };
  //   let to_relative = |p : &ParserOutput| {
  //     let mut p1 = p.clone();
  //     let (_,p_data,p_vars) = &mut p1;
  //     p_vars.clear();
  //     p_vars.to_relative();
  //     for each in p_data.iter_mut() { if let SExpr::Var((_,s)) = each { *each = SExpr::Var((p_vars.aquire_de_bruin(*s),*s)); }; }
  //     p1
  //   };
    
  //   let abs_var = |val : usize, offset :usize, s : &'static str| SExpr::Var((DebruijnLevel::Ref(unsafe{NonZeroIsize::new_unchecked(!(val+offset) as isize)}), sym(s)));
    
  //   let mut e1a = e1.clone();
  //   e1a.2.to_absolute(100);
  //   let x = abs_var(0,100, "$x");
  //   e1a.1= alloc::vec![atom(f), x, atom(a)];

  //   let mut e2a = e2.clone();
  //   e2a.2.to_absolute(100);
  //   let x = abs_var(0,100, "$x");
  //   let y = abs_var(0,101, "$y");
  //   e2a.1= alloc::vec![atom(f), x, y, y, x];
    

  //   let mut e3a = e3.clone();
  //   e3a.2.to_absolute(100);
  //   let y = abs_var(0,100, "$y");
  //   let x = abs_var(0,101, "$x");
  //   e3a.1= alloc::vec![atom(f), y, atom(g), y, x];

  //   core::assert_eq!(to_absolute(&e1, 100), e1a);
  //   core::assert_eq!(to_absolute(&e2, 100), e2a);
  //   core::assert_eq!(to_absolute(&e3, 100), e3a);

  //   core::assert_eq!(e1, to_relative(&e1a));
  //   core::assert_eq!(e2, to_relative(&e2a));
  //   core::assert_eq!(e3, to_relative(&e3a));

  //   core::assert_eq!(to_relative(&to_absolute(&r1,100)), r1);
  //   core::assert_eq!(to_absolute(&to_relative(&to_absolute(&r1,100)),200), to_absolute(&r1, 200));
  }



  '_substReIndex : {
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

    let pretty_print = |d : &DyckExprSubOutput| {
      std::println!("DyckExperSubOutput(");
      let data = match d {
        DyckExprSubOutput::SmallDyckExpr(SmallDyckExpr { word, data }) => {
          std::println!("\tword : {word:?}");
          data
        }
        DyckExprSubOutput::LargeDyckExpr(LargeDyckExpr { word, data }) => {
          std::println!("\tword : {word:#?}");
          data
        },
      };
      std::println!("\tdata : [");
      for each in data {
        use alloc::string::ToString;
        let (tag, val) = match each {
            SExpr::Var(DebruijnLevel::Intro)  => ("Var ", "$".to_string()),
            SExpr::Var(DebruijnLevel::Ref(r)) => ("Var ", alloc::format!("$[{}]", r.get() )),
            SExpr::Atom(a)                    => ("Atom", a.0.to_string()),
            _ => core::unreachable!(),
        };
        std::println!("\t\t{tag} {val}")
      }
      std::println!("]");
      std::println!(")\n");
    };

    let intro_var = (&DyckStructureZipperU64::new(1).unwrap(),&[SExpr::Var::<Void>(DebruijnLevel::Intro)][..]);
    let get_word = |expr : &DyckExprSubOutput| match expr {
        DyckExprSubOutput::SmallDyckExpr(SmallDyckExpr { word,.. }) => *word,
        DyckExprSubOutput::LargeDyckExpr(LargeDyckExpr { word,.. }) => word[0],
    };
    let get_data : fn(&_)->&_ = |expr : &DyckExprSubOutput|match expr {
        DyckExprSubOutput::SmallDyckExpr(SmallDyckExpr { data,.. }) |
        DyckExprSubOutput::LargeDyckExpr(LargeDyckExpr { data,.. }) => data,
    };
    let sub_re_index_input : fn(&(DyckStructureZipperU64, Vec<SExpr>, Variables))->(&_,&_)= |x| (&x.0,&x.1[..]);

    const LEAF : DyckStructureZipperU64 = DyckStructureZipperU64::LEAF;

    macro_rules! templates {($($ID:ident $SRC:literal)+) => {$(
      let _tmp = parse($SRC);
      let $ID  = sub_re_index_input(&_tmp);
    )+};}

    templates!{
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
    }

    let s1 = subst_re_index(r1, &[intro_var]);
    core::assert_eq!{r1.0.current_substructure(), get_word(&s1).0 }
    core::assert_eq!{r1.1,&get_data(&s1)[..]}

        macro_rules! substitutions {($([$PAT:ident / [$($SUB:expr),*]] => $EXPECTED:literal | $INTROS:tt;)+) => {$(
      let s = subst_re_index($PAT, &[$($SUB),*]);
      let expected_ = parse($EXPECTED);
      let expected  = subst_re_index(sub_re_index_input(&expected_), &$INTROS); 
      core::assert_eq!(get_word(&s).0, get_word(&expected).0);
      core::assert_eq!(get_data(&s), get_data(&expected));
    )+};}

    let leaf_a = (&LEAF, &[atom(a)][..]);
    let leaf_c = (&LEAF, &[atom(c)][..]);
    substitutions!{
      // [r1 / [axy]                                ] => "(f (a $x $y) (a $x $y))"                                             | [intro_var, intro_var]; 
      // [r2 / [axy, (&LEAF ,&[atom(A)])]           ] => "(f (a $x $y) A (a $x $y))"                                           | [intro_var, intro_var];
      // [r2 / [axx, intro_var]                     ] => "(f (a $x $x) $ (a $x $x))"                                           | [intro_var, intro_var];
      // [r3 / [leaf_a, (&LEAF, &[atom(b)]), leaf_c]] => "(, (f a b) (g b c c))"                                               | []; 
      // [r3 / [leaf_a, intro_var, leaf_c]          ] => "(, (f a $x) (g $x c c))"                                             | [intro_var]; 
      // [r3 / [leaf_a, intro_var, intro_var]       ] => "(, (f a $x) (g $x $y $y))"                                           | [intro_var, intro_var];
      // [r3 / [intro_var, intro_var, intro_var]    ] => "(, (f $x $y) (g $y $z $z))"                                          | [intro_var, intro_var, intro_var];
      // [r3 / [leaf_a, Bxy, leaf_c]                ] => "(, (f a (B $x $y)) (g (B $x $y) c c))"                               | [intro_var, intro_var];
      
      // [r3 / [intro_var, Bxy, intro_var]          ] => "(, (f $w (B $x $y)) (g (B $x $y) $z $z))"                            | [intro_var, intro_var, intro_var, intro_var];
      // [r3 / [intro_var, Bxx, leaf_c]             ] => "(, (f $w (B $x $x)) (g (B $x $x) c c))"                              | [intro_var, intro_var];
      // [r3 / [Axy, Bxx, leaf_c]                   ] => "(, (f (A $w $x) (B $y $y)) (g (B $y $y) c c))"                       | [intro_var, intro_var, intro_var];
      [r3 / [Axy, Bxyy, Cxx]                     ] => "(, (f (A $v $w) (B $x $y $y)) (g (B $x $y $y) (C $z $z) (C $z $z)))" | [intro_var, intro_var, intro_var, intro_var, intro_var];
    }
    
    // let s2 = subst_re_index(r1, &[axy]);
    // let expected2_ = parse("(f (a $x $y) (a $x $y))");
    // let expected2  = subst_re_index(sub_re_index_input(&expected2_), &[intro_var, intro_var]); 
    // core::assert_eq!(get_word(&s2).0, get_word(&expected2).0);
    // core::assert_eq!(get_data(&s2), get_data(&expected2));
    
    // let s3 = subst_re_index(r2, &[axy, (&LEAF ,&[atom(A)])]);
    // let expected3_ = parse("(f (a $x $y) A (a $x $y))");
    // let expected3  = subst_re_index(sub_re_index_input(&expected3_), &[intro_var, intro_var]); 
    // core::assert_eq!(get_word(&s3).0, get_word(&expected3).0);
    // core::assert_eq!(get_data(&s3), get_data(&expected3));

    // let s4 = subst_re_index(r2, &[axx, intro_var]);
    // let expected4_ = parse("(f (a $x $x) $ (a $x $x))");
    // let expected4  = subst_re_index(sub_re_index_input(&expected4_), &[intro_var, intro_var]); 
    // core::assert_eq!(get_word(&s4).0, get_word(&expected4).0);
    // core::assert_eq!(get_data(&s4), get_data(&expected4));


    // let s5 = subst_re_index(r3, &[(&LEAF, &[atom(a)]), (&LEAF, &[atom(b)]), (&LEAF, &[atom(c)])]);
    // let expected5_ = parse("(, (f a b) (g b c c))");
    // let expected5  = subst_re_index(sub_re_index_input(&expected5_), &[]); 
    // core::assert_eq!(get_word(&s5).0, get_word(&expected5).0);
    // core::assert_eq!(get_data(&s5), get_data(&expected5));

    // let s6 = subst_re_index(r3, &[(&LEAF, &[atom(a)]), intro_var, (&LEAF, &[atom(c)])]);
    // let expected6_ = parse("(, (f a $x) (g $x c c))");
    // let expected6  = subst_re_index(sub_re_index_input(&expected6_), &[intro_var]); 
    // core::assert_eq!(get_word(&s6).0, get_word(&expected6).0);
    // core::assert_eq!(get_data(&s6), get_data(&expected6));
    
    // let s7 = subst_re_index(r3, &[(&LEAF, &[atom(a)]), intro_var, intro_var]);
    // let expected7_ = parse("(, (f a $x) (g $x $y $y))");
    // let expected7  = subst_re_index(sub_re_index_input(&expected7_), &[intro_var, intro_var]); 
    // core::assert_eq!(get_word(&s7).0, get_word(&expected7).0);
    // core::assert_eq!(get_data(&s7), get_data(&expected7));

    // let s8 = subst_re_index(r3, &[intro_var, intro_var, intro_var]);
    // let expected8_ = parse("(, (f $x $y) (g $y $z $z))");
    // let expected8  = subst_re_index(sub_re_index_input(&expected8_), &[intro_var, intro_var, intro_var]); 
    // core::assert_eq!(get_word(&s8).0, get_word(&expected8).0);
    // core::assert_eq!(get_data(&s8), get_data(&expected8));


    // pretty_print(&sub_self);
    // std::println!("{sub_self:?}");
    return;


   // (f $ $ _1)   \  { (a $ $) , A }
   // (f (a $ $) A (a _1 _2))

   /*
    N (f $ $ _1)   1101010

    [(0 L f), (1 $ 0), (2 $ 1), (3 V 0)]
    [(0 1), (1 2)]

    N (a $ $)  11010

    [(0 L a), (1 $ 0), (2 $ 1)]
    [(0 1), (1 2)]

    L A     1

     1  (11010)0  10 (11010)0    # 111010010110100
    (f  (a $ $)   A  (a _1 _2) )
    
    [f a $ $ A a _1 _2]
    



    (, (f $ $) (g _2 $ _3))  \ { (A $ $), (B $ $ _2), (C $ _1) }

    (, (f $ $) (g _2 $ _3))  1(11010)0(1101010)0
    [(0 L ,) (1 L f) (2 $ 0) (3 $ 1) (4 L g) (5 V _2) (6 $ 2) (7 V _3)]
    [(0 2) (1 3) (2 6)]

    (A $ $)  11010
    [(0 L A), (1 $ 0), (2 $ 1)]
    [(0 1), (1 2)]

    (B $ $ _2) 1101010
    [(0 L B), (1 $ 0), (2 $ 1) (3 V _2)]
    [(0 1), (1 2)]
     
    (C $ _1) 11010
    [(0 L C), (1 $ 0), (2 V _1)]
    [(0 1)]

    
    
    [, f (A $ $) (B $ $ _2) g ] 

  
    */


    #[repr(transparent)]
    #[derive(Clone, Copy)]
    struct Bits(pub u64);
    impl core::fmt::Debug for Bits {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        core::write!(f, "{:#066b}", self.0)
    }
    }
    #[derive(Debug)]
    struct SmallDyckExpr {word : Bits, data : Vec<SExpr>}
    #[derive(Debug)]
    struct LargeDyckExpr {word : Vec<Bits>, data : Vec<SExpr>}
    #[derive(Debug)]
    enum DyckExprSubOutput {
      SmallDyckExpr(SmallDyckExpr),
      LargeDyckExpr(LargeDyckExpr),
    }

    #[cfg_attr(rustfmt, rustfmt::skip)]
    fn subst_re_index((pat_structure, pat_data) : (&DyckStructureZipperU64, &[SExpr]), subs : &[(&DyckStructureZipperU64,&[SExpr])]) -> DyckExprSubOutput{
      const MAX_LEAVES : usize = DyckStructureZipperU64::MAX_LEAVES;

      core::debug_assert_eq!(pat_data.into_iter().filter(|x| core::matches!(x, SExpr::Var(DebruijnLevel::Intro))).count(), subs.len());

      core::debug_assert!(pat_data.len() < MAX_LEAVES);
      core::debug_assert!(subs.len() < MAX_LEAVES);
      for each in subs {
        core::debug_assert!(each.1.len() < MAX_LEAVES);
        core::debug_assert!(each.1.len() != 0);
      }

      #[derive(Clone, Copy)]
      struct LevelIndex(u8);      

      type LevelIndicies = [LevelIndex; MAX_LEAVES];
      const LEVEL_INDEX  : LevelIndicies = [LevelIndex(0); MAX_LEAVES];

      type LookupStore = [u8;MAX_LEAVES];
      const LOOKUP_INDEX : LookupStore = [0_u8; MAX_LEAVES];
      
      let mut pat_meta_index   = LEVEL_INDEX;
      let mut pat_intro_lookup = LOOKUP_INDEX;
      let mut pat_intros       = 0;

      let mut subs_meta_index_matrix   = [LEVEL_INDEX; MAX_LEAVES];
      let mut subs_intro_lookup_matrix = [LOOKUP_INDEX; MAX_LEAVES];
      let mut subs_intros_list         = [0_u8; MAX_LEAVES];
      
      
      struct IndexGenArg<'a> {structure : &'a DyckStructureZipperU64, data : &'a [SExpr], m_idx :&'a mut LevelIndicies, var_lookup : &'a mut LookupStore, intros : &'a mut u8}
      fn generate_index(IndexGenArg { structure, data, m_idx, var_lookup , intros}: IndexGenArg<'_>) {
        let range      = structure.current_leaf_store_index_range();
        let data_slice = &data[range];

        for (i, each) in data_slice.into_iter().enumerate() {
          if let SExpr::Var(DebruijnLevel::Intro) = each {
            m_idx[i] = LevelIndex(*intros);
            var_lookup[*intros as usize] = i as u8;
            *intros +=1;
          }
        }
      }
      
      generate_index(IndexGenArg {structure : pat_structure, data : pat_data, m_idx : &mut pat_meta_index, var_lookup : &mut pat_intro_lookup, intros : &mut pat_intros});
      
      // this could be done lazily, but then we would have to constantly do checks
      for (i,&(structure, data)) in subs.into_iter().enumerate() {
        generate_index(IndexGenArg {structure, data, m_idx: &mut subs_meta_index_matrix[i] , var_lookup: &mut subs_intro_lookup_matrix[i] , intros : &mut subs_intros_list[i]});
        if i > 1 {
          subs_intros_list[i]+=subs_intros_list[i-1]; // running totals
        } 
      }
      
      let mut dyck_words     = [0_u64; MAX_LEAVES];
      // stores the the number of consecutive 0 bits 
      let mut trailing_pairs = [0_u8; MAX_LEAVES]; 
      
      let mut pat_structure_word = pat_structure.current_substructure();
      // add terminal 1 bit before shifting fully , avoids counting too many pairs
      pat_structure_word = ((pat_structure_word << 1) | 1 ) << pat_structure_word.leading_zeros()-1;
      
      let pat_data_slice = &pat_data[pat_structure.current_leaf_store_index_range()];

      let mut output_data = [SExpr::<Void>::Atom(Sym::EMPTY); MAX_LEAVES*MAX_LEAVES];
      let mut output_len  = 0;

      for each in 0..pat_data_slice.len() {
        let mut substitute = |intro_idx : usize, is_from_ref : bool| {

          let idx          = pat_meta_index[intro_idx].0 as usize;
          
          core::debug_assert!((idx as usize) < subs.len());
          let (sub_struct, sub_data) = subs[idx as usize];
          let depth_offset = if idx == 0 { 0 } else { subs_intros_list[idx-1] };

          let sub_data_slice         = &sub_data[sub_struct.current_leaf_store_index_range()];
          
          // refs need to know how many intros they passed
          let mut intros_count = 0;
          
          for slice_idx in 0..sub_data_slice.len(){
            output_data[output_len] = match sub_data_slice[slice_idx] {
              SExpr::Var(DebruijnLevel::Ref(r)) if r.is_negative() => unsafe {
                // Safety : the negative value will only become more negative
                SExpr::Var(DebruijnLevel::Ref(NonZeroIsize::new_unchecked(r.get()-depth_offset as isize)))
              },
              SExpr::Var(DebruijnLevel::Intro) if is_from_ref => {
                let val = !((intros_count + depth_offset) as isize);
                intros_count+=1;
                // Safety : values > 0 that are negagted are always non-zero
                SExpr::Var(DebruijnLevel::Ref(unsafe {NonZeroIsize::new_unchecked(val as isize) }))
              }
              val => val,
            };
          
            output_len += 1;
          }
          dyck_words[each] = sub_struct.current_substructure();
        };

        match pat_data_slice[each] {
          SExpr::Var(DebruijnLevel::Intro) => {
            substitute(each,false);
          },
          SExpr::Var(DebruijnLevel::Ref(r)) if r.is_negative() => {
              let rel_ref   = (!r.get()) as usize;
              let intro_idx = pat_intro_lookup[rel_ref] as usize;
              substitute(intro_idx,true);
          },
          val  => {
            output_data[output_len] = val;
            dyck_words[each] = 1;
            output_len +=1;
          }
        }
        // shift off a leaf
        pat_structure_word <<= 1;
        let pairs = pat_structure_word.leading_zeros();
        trailing_pairs[each] = pairs as u8;
        // shift off consecutive pairs
        pat_structure_word <<= pairs;
      }
      // the output Vec is now ready for allocating

      // Build the Large Dyck Word
      let mut output_word_len = 0;
      let [mut cur, mut next] = [0_u64;2];
      let mut finished        = Vec::new();
      let mut last_div        = 0;

      for each in (0..pat_data.len()).rev() {
        output_word_len += trailing_pairs[each] as usize;
        let (cur_div, cur_mod) = (output_word_len/64, output_word_len%64);

        // check if we need to advance the "cursor"
        if last_div < cur_div {
          if finished.len() == 0 {
            finished = Vec::with_capacity(MAX_LEAVES);
          }
          finished.push(cur);
          (cur,next) = (next, 0);
        }

        let cur_word = dyck_words[each];

        [cur,next] = [
          cur  | cur_word << cur_mod, 
          if cur_mod == 0 {0} else { next | cur_word >> u64::BITS - cur_mod as u32} 
        ];
        output_word_len += (u64::BITS-cur_word.leading_zeros()) as usize;
        last_div = cur_div;
      }

      let data = Vec::from(&output_data[0..output_len]);

      if next == 0 && finished.len() == 0 {
        DyckExprSubOutput::SmallDyckExpr(SmallDyckExpr { word: Bits(cur), data })
      } else {
     
        finished.push(cur);
        if next != 0 || cur.leading_zeros() == 0 { finished.push(next);}
        finished.reverse();

        DyckExprSubOutput::LargeDyckExpr(LargeDyckExpr { word: unsafe { core::mem::transmute(finished)}, data })
      }
    }



    // I'm confident that  I can do this with just numbers and it would be much much faster.

    // fn anonymize(mut d : ParserOutput)->(DyckStructureZipperU64,Vec<Sexpr>) {
    //   for each in &mut d.1 {
    //     match each {
    //         SExpr::Var((_,s)) => *s = Sym::EMPTY,
    //         _ => {},
    //     }
    //   }
    //   (d.0,d.1)
    // }

    fn level_sym(d : DebruijnLevel)->Sym {
      let n = match d {
        DebruijnLevel::Intro => return Sym::new("$0"),
        DebruijnLevel::Ref(r) => r.get(),
      };
      let mut arr = *b"$-0x0000000000000000";
      
      let mut n = n.abs() as usize;
      let l = isize::BITS - n.leading_zeros();
      let max_idx =  l/4 + l%4 + 3;
      let mut idx = max_idx;
      while n != 0 {
        const BOT_MASK : usize = (1 << 4)-1;
        let bot = (n&BOT_MASK) as u8;
        arr[idx as usize] = match bot {
          0..=9   => { bot + b'0' }
          10..=15 => { bot + b'a' - 10 }
          _=>{ core::unreachable!() }
        };
        (idx, n) = (idx - 1, n>>4);
      }
      Sym::new(unsafe{core::str::from_utf8_unchecked(&arr[0..=max_idx as usize])})
    }

    let r1 = parse("(f $x $x)");
    // let r1 = parse("
    //   ( f
    //     $a $b $c $d $e $f $g $h $i $j $k $l $m $n $o $p $q $r $s $t $u $v $w $x $y $z
    //     $m $a $z
    //   )
    // ");
    std::println!("{:?}", r1);
    let r1_anon = 
    // anonymize(r1) 
      r1
    ;
    std::println!("{:?}", r1_anon);

    // let mut vars = Variables::new();
    // let mut idx = 0;
    // for each in &r1_anon.1 {
    //   vars.aquire_de_bruin(match each {
    //     SExpr::Var((DebruijnLevel::Intro,_)) => {
    //       let s = level_sym(DebruijnLevel::Ref(unsafe {NonZeroIsize::new_unchecked(!idx)})); idx+=1; 
    //       s
    //     },
    //     SExpr::Var((d,_)) => level_sym(*d),
    //       _=>continue
    //   });
    // }
    // std::println!("{vars:?}")

    
  }

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


  // shared/src/test/scala/ExprTest.scala
  // ```scala
  // test("subst") {
  //   assert(e1.substRel(Seq(b)) == Expr(f, b, a))
  //   assert(e2.substRel(Seq(a, b)) == Expr(f, a, b, b, a))
  //   assert(e3.substRel(Seq(a, b)) == Expr(f, a, Expr(g, a, b)))
  // }
  // ```


  // shared/src/test/scala/ExprTest.scala
  // ```scala
  // test("large subst") {
  //   import Expr.*
  //   val `5` = Var(200)
  //   val Z = Var(201)
  //   assert(r1.substRel(Seq(`5`, App(g,App(g,Z)))) == App(App(`=`,App(f,App(App(`,`,`5`),App(g,App(g,App(g,App(g,Z))))))),App(App(h,App(App(`,`,`5`),App(g,a))),App(App(`,`,`5`),App(g,App(g,App(g,Z)))))))
  // }
  // ```


  // shared/src/test/scala/ExprTest.scala
  // ```scala
  // test("show pretty") {
  //   assert(e1.show == "Expr(Var(1), Var(0), Var(10))")
  //   assert(e2.show == "Expr(Var(1), Var(0), Var(0), Var(-2), Var(-1))")
  //   assert(e3.show == "Expr(Var(1), Var(0), Expr(Var(2), Var(-1), Var(0)))")
  //   assert(e1.pretty(false) == "(1 ◆ 10)")
  //   assert(e2.pretty(false) == "(1 ◆ ◆ ⏴₂ ⏴₁)")
  //   assert(e3.pretty(false) == "(1 ◆ (2 ⏴₁ ◆))")
  // }
  // ```
}
