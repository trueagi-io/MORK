use crate::*;

// this uses a "module" type, so `Self`` here is just a type level namespace
trait FiniteBinaryTree {
  type BinaryTree<T>: Default;

  fn empty<T>() -> Self::BinaryTree<T> {
    <Self::BinaryTree<T> as Default>::default()
  }
  fn leaf<T>(value: T) -> Self::BinaryTree<T>;
  /// a finite tree may fail to grow bigger as it holds a finite number of elements, in which case, the arguments are returned
  fn try_branch<T>(left: Self::BinaryTree<T>, right: Self::BinaryTree<T>) -> Result<Self::BinaryTree<T>, (Self::BinaryTree<T>, Self::BinaryTree<T>)>;

  /// this should behave like an `&Self::BinaryTree`
  type SubTree<'tree, T: 'tree>: core::marker::Copy;
  /// this should behave like an `&mut Self::BinaryTree`
  type SubTreeMut<'mut_refer, T: 'mut_refer>;

  fn clone_sub_tree<'tree, T>(sub_tree: Self::SubTree<'tree, T>) -> Self::BinaryTree<T>
  where
    T: Clone;

  fn as_sub_tree<'tree, T>(binary_tree: &'tree Self::BinaryTree<T>) -> Self::SubTree<'tree, T>;
  fn as_sub_tree_mut<'tree, T>(binary_tree: &'tree mut Self::BinaryTree<T>) -> Self::SubTreeMut<'tree, T>;

  type Path;
  fn sub_tree_index<'tree, T>(sub_tree: Self::SubTree<'tree, T>, path: &Self::Path) -> Option<Self::SubTree<'tree, T>>;
  fn sub_tree_mut_index<'tree, T>(sub_tree: &mut Self::SubTreeMut<'tree, T>, path: &Self::Path) -> Option<Self::SubTreeMut<'tree, T>>;

  /// a finite tree may fail to grow bigger as it holds a finite number of elements, in which case, the arguments are returned
  /// This function always succeeds when the swapped in element is of the same size, or smaller.
  fn try_swap<T>(tree: Self::BinaryTree<T>, path: &Self::Path, branch: Self::BinaryTree<T>) -> Result<Self::BinaryTree<T>, (Self::BinaryTree<T>, Self::BinaryTree<T>)>;

  /// removes the element fount at Path location, collapsing the parent branch
  fn remove<T>(tree: Self::BinaryTree<T>, path: &Self::Path) -> (Self::BinaryTree<T>, Option<Self::BinaryTree<T>>);

  fn remove_where<'tree, T, F>(tree: Self::BinaryTree<T>, filter: F) -> Self::BinaryTree<T>
  where
    F: core::ops::FnMut(Self::SubTree<'tree, T>) -> bool,
    T: 'tree;

  /// Swaps two branhces in an a tree in-place
  /// If the `Self::Path`s are out of bounds, the tree is returned unchanged
  fn swap_branches<T>(tree: Self::BinaryTree<T>, path_1: &Self::Path, path_2: &Self::Path) -> Result<Self::BinaryTree<T>, Self::BinaryTree<T>>;

  /// The const generic `LEFT` choses to branch left if true, and right if false
  fn try_branch_at<T, const LEFT: bool>(tree: Self::BinaryTree<T>, path: &Self::Path, branch: Self::BinaryTree<T>) -> Result<Self::BinaryTree<T>, (Self::BinaryTree<T>, Self::BinaryTree<T>)>;

  // ref traverse

  type DfsRef<'tree, T: 'tree>: Iterator<Item = &'tree T> + Clone;
  fn depth_first_traverse_ref<'tree, T: 'tree>(sexpr: Self::SubTree<'tree, T>) -> Self::DfsRef<'tree, T>;

  type BfsRef<'tree, T: 'tree>: Iterator<Item = &'tree T> + Clone;
  fn breath_first_traverse_ref<'tree, T: 'tree>(sexpr: Self::SubTree<'tree, T>) -> Self::BfsRef<'tree, T>;

  // mut traverse

  type DfsMut<'tree, T: 'tree>: Iterator<Item = &'tree mut T> + From<Self::SubTreeMut<'tree, T>>;
  fn depth_first_traverse_mut<'tree, T>(sexpr: &mut Self::SubTreeMut<'tree, T>) -> Self::DfsMut<'tree, T>;

  type BfsMut<'tree, T: 'tree>: Iterator<Item = &'tree mut T> + From<Self::SubTreeMut<'tree, T>>;
  fn breath_first_traverse_mut<'sub_tree, T>(sexpr: &mut Self::SubTreeMut<'sub_tree, T>) -> Self::BfsMut<'sub_tree, T>;

  // move traverse

  type Dfs<T>: Iterator<Item = T> + From<Self::BinaryTree<T>>;
  fn depth_first_traverse<T>(sexpr: Self::BinaryTree<T>) -> Self::Dfs<T>;

  type Bfs<T>: Iterator<Item = T> + From<Self::BinaryTree<T>>;
  fn breath_first_traverse<T>(sexpr: Self::BinaryTree<T>) -> Self::Bfs<T>;
}

enum Term {
  Atom(alloc::sync::Arc<str>),
  Var(alloc::sync::Arc<str>),
}
impl Term {
  fn atom(s: &str) -> Term {
    Term::Atom(alloc::sync::Arc::<str>::from(s))
  }
  fn var(s: &str) -> Term {
    Term::Var(alloc::sync::Arc::<str>::from(s))
  }
}
impl core::fmt::Display for Term {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    match self {
      Term::Atom(atom) => core::write!(f, "{}", atom),
      Term::Var(var) => core::write!(f, "${}", var),
    }
  }
}

pub(crate) fn main() {
  /*

  .
  0  /   \
  / \ 1   \
  0  / 0 / \     \ 1
  /    .    \ 1   \
  /  0 /   \ 1  \     \
  ((= ((parent $y) Bob)) $rhs)


  */
  type T = Term;
  let d = DykeTree {
    // shape: (0b00100111_1_u64<<u64::BITS-9).reverse_bits(),
    shape: (0b_1_11010_010_u64).reverse_bits(),
    data: alloc::vec![T::atom("="), T::atom("parent"), T::var("y"), T::atom("Bob"), T::var("rhs")],
  };
  // std::println!("{d}");
}

// // this assumes the tree is in reverse, the representation has changed
// impl<T : core::fmt::Display> core::fmt::Display for Dyke<T> {
//     fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
//         let mut shift = 0;
//         let mut pos = 0;
//         let mut open_stack = 1_u64;

//         while open_stack != 0 {
//             let is_node = (self.shape & (1 << shift)) == 0;
//             if is_node {
//                 core::write!(f, "(")?;
//                 open_stack = (open_stack << 1) | 1;
//             } else {
//                 core::write!(f, "{}", self.data[pos])?;
//                 pos += 1;
//                 let zeros = open_stack.trailing_zeros();
//                 open_stack = (open_stack >> zeros) - 1;
//                 if zeros > 0 {
//                     core::write!(f, "{:)<zeros$}", "", zeros=zeros as usize)?;
//                 }
//                 if open_stack != 0 {
//                     core::write!(f, " ")?;
//                 }
//             }
//             shift += 1;
//         }
//         Result::Ok(())
//     }
// }

struct DykeTree<T> {
  /// the shape of the tree is in postfix order,
  /// and can be mentally though of as a stack machine's instruction ordering
  /// - 0b0     -> [] -> nil
  /// - 0b1     -> [leaf] -> leaf
  /// - 0b110   -> [0_leaf 1_leaf branch] -> (0_leaf . 1_leaf)
  /// - 0b11010 -> [0_leaf 1_leaf branch 2_leaf branch] -> ((0_leaf . 1_leaf) . 2_leaf)
  ///
  /// any tree of size grater than 1, must have 1 more leaf than branches to be a valid tree,
  /// so the top bit is free
  ///
  /// the maximum nnumber of elements is `u64::BITS/2` or 32
  shape: u64,
  data: Vec<T>,
}
impl<T> DykeTree<T> {
  const MAX_ELEMENTS: usize = u64::BITS as usize / 2;
}
impl<T> Default for DykeTree<T> {
  fn default() -> Self {
    Self { shape: Default::default(), data: Default::default() }
  }
}

struct DyckSubTree<'tree, T> {
  shape: u64,
  data: &'tree [T],
}

impl<'tree, T> Clone for DyckSubTree<'tree, T> {
  fn clone(&self) -> Self {
    let &Self { shape, data } = self;
    Self { shape, data }
  }
}
// #[derive(Clone,Copy)] can have limitations
impl<'tree, T> core::marker::Copy for DyckSubTree<'tree, T> {}

struct DyckSubTreeMut<'tree, T> {
  shape: u64,
  data: &'tree mut [T],
}
impl<'sub_tree: 'tree, 'tree, T> core::convert::From<&'sub_tree DyckSubTreeMut<'tree, T>> for DyckSubTree<'tree, T> {
  fn from(DyckSubTreeMut { shape, data }: &'sub_tree DyckSubTreeMut<'tree, T>) -> DyckSubTree<'tree, T> {
    DyckSubTree { shape: *shape, data: &*data }
  }
}

#[repr(u16)]
pub enum BranchSide {
  Left = 0,
  Right = 1,
}
#[derive(Clone, Copy)]
struct DykeTreePath {
  remaining: u8,
  path: u16,
}
impl core::default::Default for DykeTreePath {
  fn default() -> Self {
    DykeTreePath { remaining: 0, path: !0 }
  }
}

#[derive(Debug)]
pub struct StackOverflow;
impl DykeTreePath {
  fn push(&self, side: BranchSide, times: u8) -> Result<Self, StackOverflow> {
    let stack = *self;
    let remaining = stack.remaining.saturating_add(times);
    if remaining > u16::BITS as u8 {
      return Result::Err(StackOverflow);
    }
    let mask = !(!1 >> times as u32);
    let path = stack.path >> times as u32 | mask & side as u16;

    Result::Ok(Self { remaining, path })
  }

  fn pop_one(&self) -> Option<(Self, BranchSide)> {
    let stack = *self;
    if stack.remaining == 0 {
      return Option::None;
    }

    let remaining = stack.remaining - 1;
    let mut path = stack.path.rotate_left(1);
    let side = if 1 & path == 0 { BranchSide::Left } else { BranchSide::Right };
    path |= 1;

    Option::Some((Self { remaining, path }, side))
  }

  fn pop_contiguous(&self) -> Option<(Self, BranchSide, u8)> {
    let stack = *self;
    if stack.remaining == 0 {
      return Option::None;
    }

    let left_is_zero = !(stack.path.rotate_left(1) & 1).wrapping_sub(1);
    let count = (left_is_zero ^ stack.path).leading_zeros();
    let side = if left_is_zero == 0 { BranchSide::Left } else { BranchSide::Right };
    let path = stack.path << count | !(!0 << count);
    let remaining = stack.remaining - count as u8;

    Option::Some((Self { remaining, path }, side, count as u8))
  }
}

#[derive(Debug)]
enum FiniteBinaryTreeError {
  InvalidPath,
}

/*
            struct DykeImpl;
            impl FiniteBinaryTree for DykeImpl {
              type BinaryTree<T> = DykeTree<T>;

              fn leaf<T>(value : T)->Self::BinaryTree<T> {
                let mut data = Vec::with_capacity(DykeTree::<T>::MAX_ELEMENTS);
                data.push(value);
                DykeTree { shape : 0b1, data }
              }

              fn try_branch<T>(
                left : Self::BinaryTree<T>,
                right : Self::BinaryTree<T>
              )->Result<Self::BinaryTree<T>, (Self::BinaryTree<T>, Self::BinaryTree<T>)> {
                if left.data.len() + right.data.len() > DykeTree::<T>::MAX_ELEMENTS { return Result::Err((left,right)); }

                let shape = ((left.shape << u64::BITS - right.shape.leading_zeros())|right.shape)<<1;
                let mut data = left.data;
                data.extend(right.data.into_iter());

                Result::Ok(DykeTree { shape, data })
              }

              type SubTree<'tree, T:'tree> = DyckSubTree<'tree, T>;

              type SubTreeMut<'tree, T : 'tree> = DyckSubTreeMut<'tree, T>;

              fn clone_sub_tree<'tree, T>(
    sub_tree : Self::SubTree<'tree, T>
  )-> Self::BinaryTree<T> where T:Clone {
    let DyckSubTree { shape, data } = sub_tree;
    DykeTree { shape, data: data.iter().cloned().collect() }
  }

  fn as_sub_tree<'tree, T>(
    binary_tree : &'tree Self::BinaryTree<T>
  )->Self::SubTree<'tree, T> {
    let DykeTree { shape, data } = binary_tree;
    DyckSubTree { shape : *shape, data }
  }

  fn as_sub_tree_mut<'tree, T>(
    binary_tree : &'tree mut Self::BinaryTree<T>
  )->Self::SubTreeMut<'tree, T> {
    let DykeTree { shape, data } = binary_tree;
    DyckSubTreeMut { shape : *shape, data }
  }

  type Path = DykeTreePath;

  fn sub_tree_index<'tree, T>(
    sub_tree : Self::SubTree<'tree, T>,
    path : &Self::Path
  )->Option<Self::SubTree<'tree, T>> {
    if path.remaining as u32 > sub_tree.shape.count_ones() {return Option::None;}
    let DyckSubTree { shape, data } = sub_tree;

    let mut element_count = shape.count_ones();
    let mut shape = sub_tree.shape;
    let mut stack = *path;
    loop {
      let Option::Some((s,b,mut c)) = stack.pop_contiguous() else { return Option::None; };

      let mut left_is_zero = !(b as u16 as u64-1);
      loop {

        let rotate = (left_is_zero^shape).trailing_zeros();
        if rotate == 0 { return Option::None; }
        shape >>= rotate;

        if shape.count_ones() == 0 { return Option::None; }
        if  rotate as u8 > c { return  Option::None;}
        c -= rotate as u8;
        if c == 0 { break; }
      }


      stack=s;
    }

    core::todo!()
  }

  fn sub_tree_mut_index<'tree, T>(
    sub_tree : &mut Self::SubTreeMut<'tree, T>,
    path : &Self::Path
  )->Option<Self::SubTreeMut<'tree, T>> {
    core::todo!()
  }

  fn try_swap<T>(
    tree   : Self::BinaryTree<T>,
    path   : &Self::Path,
    branch : Self::BinaryTree<T>,
  )->Result<Self::BinaryTree<T>, (Self::BinaryTree<T>, Self::BinaryTree<T>)> {
    core::todo!()
  }

  fn remove<T>(
    tree : Self::BinaryTree<T>,
    path : &Self::Path,
  )->(Self::BinaryTree<T>, Option<Self::BinaryTree<T>>) {
    core::todo!()
  }

  fn remove_where<'tree, T, F>(
    tree : Self::BinaryTree<T>,
    filter : F
  ) -> Self::BinaryTree<T>
  where F : core::ops::FnMut(Self::SubTree<'tree, T>)->bool , T:'tree {
    core::todo!()
  }

  fn swap_branches<T>(
    tree : Self::BinaryTree<T>,
    path_1 : &Self::Path,
    path_2 : &Self::Path,
  )->Result<Self::BinaryTree<T>, Self::BinaryTree<T>> {
    core::todo!()
  }

  fn try_branch_at<T, const LEFT : bool>(
    tree : Self::BinaryTree<T>,
    path : &Self::Path,
    branch : Self::BinaryTree<T>,
  )->Result<Self::BinaryTree<T>, (Self::BinaryTree<T>, Self::BinaryTree<T>)> {
    core::todo!()
  }

  type DfsRef<'tree, T : 'tree> ;

  fn depth_first_traverse_ref<'tree, T:'tree>(
    sexpr : Self::SubTree<'tree, T>
  )->Self::DfsRef<'tree, T> {
    core::todo!()
  }

  type BfsRef<'tree, T : 'tree> ;

  fn breath_first_traverse_ref<'tree, T:'tree>(
    sexpr : Self::SubTree<'tree, T>
  )->Self::BfsRef<'tree, T> {
    core::todo!()
  }

  type DfsMut<'tree, T : 'tree> ;

  fn depth_first_traverse_mut<'tree, T>(
    sexpr : &mut Self::SubTreeMut<'tree, T>
  )->Self::DfsMut<'tree, T> {
    core::todo!()
  }

  type BfsMut<'tree, T : 'tree> ;

  fn breath_first_traverse_mut<'sub_tree, T>(
    sexpr : &mut Self::SubTreeMut<'sub_tree, T>
  )->Self::BfsMut<'sub_tree, T> {
    core::todo!()
  }

  type Dfs<T> ;

  fn depth_first_traverse<T>(
    sexpr : Self::BinaryTree<T>
  )->Self::Dfs<T> {
    core::todo!()
  }

  type Bfs<T> ;

  fn breath_first_traverse<T>(
    sexpr : Self::BinaryTree<T>
  )->Self::Bfs<T> {
    core::todo!()
  }






}

 */
