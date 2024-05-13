#![no_implicit_prelude]

extern crate alloc;
extern crate core;
extern crate std;
use alloc::vec::Vec;
use core::{clone::Clone, convert::From, iter::Iterator, option::Option, result::Result};
use std::default;



enum Term {
  Atom(alloc::sync::Arc<str>),
  Var(alloc::sync::Arc<str>)
}
impl Term {
  fn atom(s : &str)->Term {
    Term::Atom(alloc::sync::Arc::<str>::from(s))
  }
  fn var(s : &str)->Term {
    Term::Var(alloc::sync::Arc::<str>::from(s))
  }
}
impl core::fmt::Display for Term {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    match self {
      Term::Atom(atom) => core::write!(f,"{}",atom),
      Term::Var(var) => core::write!(f,"${}",var),
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
    let d = Dyke {
        shape: (0b00100111_1_u64<<u64::BITS-9).reverse_bits(),
        data: alloc::vec![T::atom("="), T::atom("parent"), T::var("y"), T::atom("Bob"), T::var("rhs")],
    };
    std::println!("{d}");
}


struct Dyke<T> {
    shape: u64, // we could use u128
    data: Vec<T>,
}

impl<T : core::fmt::Display> core::fmt::Display for Dyke<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        let mut shift = 0;
        let mut pos = 0;
        let mut open_stack = 1_u64;

        while open_stack != 0 {
            let is_node = (self.shape & (1 << shift)) == 0;
            if is_node {
                core::write!(f, "(")?;
                open_stack = (open_stack << 1) | 1;
            } else {
                core::write!(f, "{}", self.data[pos])?;
                pos += 1;
                let zeros = open_stack.trailing_zeros();
                open_stack = (open_stack >> zeros) - 1;
                if zeros > 0 {
                    core::write!(f, "{:)<zeros$}", "", zeros=zeros as usize)?;
                }
                if open_stack != 0 {
                    core::write!(f, " ")?;
                }
            }
            shift += 1;
        }
        Result::Ok(())
    }
}


// this uses a "module" type, so `Self`` here is just a type level namespace
trait FiniteBinaryTree {
  type BinaryTree<T> : core::default::Default;

  fn empty<T>() -> Self::BinaryTree<T> {<Self::BinaryTree<T> as core::default::Default>::default()}
  fn leaf<T>(value : T)->Self::BinaryTree<T>;
  /// a finite tree may fail to grow bigger as it holds a finite number of elements, in which case, the arguments are returned
  fn try_branch<T>(
    left : Self::BinaryTree<T>,
    right : Self::BinaryTree<T>
  )->Result<Self::BinaryTree<T>, (Self::BinaryTree<T>, Self::BinaryTree<T>)>;

  /// this should behave like an `&Self::BinaryTree`
  type SubTree<'refer, 't, T : 't> : core::marker::Copy + for<'a> From<&'a Self::SubTreeMut<'refer, 't, T>>;
  /// this should behave like an `&mut Self::BinaryTree`
  type SubTreeMut<'mut_refer, 't, T : 't>;

  fn clone_sub_tree<'sub_tree,'t, T>(
    sub_tree : Self::SubTree<'sub_tree,'t, T>
  )-> Self::BinaryTree<T> where T:Clone;

  fn sub_tree<'refer,'t, T>(
    binary_tree : &Self::BinaryTree<T>
  )->Self::SubTree<'refer, 't, T>;
  fn sub_tree_mut<'mut_refer,'t, T>(
    binary_tree : &'mut_refer mut Self::BinaryTree<T>
  )->Self::SubTree<'mut_refer, 't, T>;

  type Path : core::marker::Copy;
  fn sub_tree_index<'sub_tree,'t, T>(
    sub_tree : Self::SubTree<'sub_tree,'t, T>,
    path : Self::Path
  )->Option<Self::SubTree<'sub_tree, 't, T>>;
  fn sub_tree_mut_index<'sub_tree,'t, T>(
    sub_tree : &mut Self::SubTreeMut<'sub_tree,'t, T>,
    path : Self::Path
  )->Option<Self::SubTreeMut<'sub_tree, 't, T>>;
  
  /// a finite tree may fail to grow bigger as it holds a finite number of elements, in which case, the arguments are returned
  /// This function always succeeds when the swapped in element is of the same size, or smaller.
  fn try_swap<T>(
    tree   : Self::BinaryTree<T>, 
    path   : Self::Path, 
    branch : Self::BinaryTree<T>,
  )->Result<Self::BinaryTree<T>, (Self::BinaryTree<T>, Self::BinaryTree<T>)>;

  /// removes the element fount at Path location, collapsing the parent branch
  fn remove<T>(
    tree : Self::BinaryTree<T>, 
    path : Self::Path,
  )->(Self::BinaryTree<T>, Option<Self::BinaryTree<T>>);

  fn remove_where<T, F>(
    tree : Self::BinaryTree<T>,
    filter : F
  ) -> Self::BinaryTree<T>
    where F : for<'sub_tree, 't> core::ops::FnMut(Self::SubTree<'sub_tree, 't, T>)->bool;

  /// Swaps two branhces in an a tree in-place
  /// If the `Self::Path`s are out of bounds, the tree is returned unchanged
  fn swap_branches<T>(
    tree : Self::BinaryTree<T>, 
    path_1 : Self::Path,
    path_2 : Self::Path,
  )->Result<Self::BinaryTree<T>, Self::BinaryTree<T>>;

  /// The const generic `LEFT` choses to branch left if true, and right if false
  fn try_branch_at<T, const LEFT : bool>(
    tree : Self::BinaryTree<T>, 
    path : Self::Path,
    branch : Self::BinaryTree<T>,
  )->Result<Self::BinaryTree<T>, (Self::BinaryTree<T>, Self::BinaryTree<T>)>;

  // ref traverse  

  type DfsRef<'sub_tree,'t, T : 't> : Iterator<Item = &'t T> + Clone;
  fn depth_first_traverse_ref<'sub_tree,'t, T:'t>(
    sexpr : Self::SubTree<'sub_tree, 't, T>
  )->Self::DfsRef<'sub_tree,'t, T>;

  type BfsRef<'sub_tree, 't, T : 't> : Iterator<Item = &'t T> + Clone;
  fn breath_first_traverse_ref<'sub_tree, 't, T:'t>(
    sexpr : Self::SubTree<'sub_tree, 't, T>
  )->Self::BfsRef<'sub_tree, 't, T>;

  // mut traverse

  type DfsMut<'sub_tree, 't, T : 't> : Iterator<Item = &'t mut T> + From<Self::SubTreeMut<'sub_tree,'t, T>>;
  fn depth_first_traverse_mut<'sub_tree,'t, T>(
    sexpr : &mut Self::SubTreeMut<'sub_tree,'t,T>
  )->Self::DfsMut<'sub_tree,'t, T>;

  type BfsMut<'sub_tree, 't, T : 't> : Iterator<Item = &'t mut T> + From<Self::SubTreeMut<'sub_tree,'t, T>>;
  fn breath_first_traverse_mut<'sub_tree,'t, T>(
    sexpr : &mut Self::SubTreeMut<'sub_tree,'t,T>
  )->Self::BfsMut<'sub_tree,'t, T>;

  // move traverse

  type Dfs<T> : Iterator<Item = T> + From<Self::BinaryTree<T>>;
  fn depth_first_traverse<T>(
    sexpr : Self::BinaryTree<T>
  )->Self::Dfs<T>;
  
  type Bfs<T> : Iterator<Item = T> + From<Self::BinaryTree<T>>;
  fn breath_first_traverse<T>(
    sexpr : Self::BinaryTree<T>
  )->Self::Bfs<T>;

}
