#![no_implicit_prelude]

extern crate alloc;
extern crate core;
extern crate std;
use alloc::vec::Vec;
use core::convert::From;

struct Dyke<T> {
    shape: u128,
    data: Vec<T>,
}

impl<T : core::fmt::Display> core::fmt::Display for Dyke<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        let mut shift = 0;
        let mut pos = 0;
        let mut open_stack = 1_u128;

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
        core::result::Result::Ok(())
    }
}

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
        shape: (0b00100111_1_u128<<u128::BITS-9).reverse_bits(),
        data: alloc::vec![T::atom("="), T::atom("parent"), T::var("y"), T::atom("Bob"), T::var("rhs")],
    };
    std::println!("{d}");
}


