use crate::*;

#[derive(Clone, PartialEq)]
pub struct DyckStructureZipperU64 {
  pub(crate) structure: u64,
  pub(crate) current_depth: u8,
  pub(crate) stack: [SubtreeSlice; DyckStructureZipperU64::MAX_LEAVES],
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
  pub const MAX_LEAVES: usize = u64::BITS as usize / 2;
  pub const LEAF: Self = {
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
