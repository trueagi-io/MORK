#![no_implicit_prelude]

extern crate alloc;
extern crate core;
extern crate std;

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
use num_bigint::BigUint;
use std::default;

mod finite;

type Shared<T> = Arc<T>;
type PathInt = u64;

pub struct BoundedDyck<L> {
  path: PathInt,
  path_offset: usize,
  leaves: Arc<[L]>,
}

pub struct UnboundedDyck<L> {
  path: BigUint,
  path_offset: usize,
  leaves: Arc<[L]>,
}

pub enum Dyck<L> {
  Bounded(BoundedDyck<L>),
  UnboundedDyck(UnboundedDyck<L>),
}

impl<L> BoundedDyck<L> {
  fn zero() -> Self {
    Self { path: 0, path_offset: 0, leaves: Shared::from([]) }
  }
  unsafe fn new_unchecked(path: PathInt, leaves: Arc<[L]>) -> Self {
    Self { path, path_offset: 0, leaves }
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
    Self { path: BigUint::ZERO, path_offset: 0, leaves: Shared::from([]) }
  }
  unsafe fn new_unchecked(path: BigUint, leaves: Shared<[L]>) -> Self {
    Self { path, path_offset: 0, leaves }
  }
  fn new(path: BigUint, leaves: Shared<[L]>) -> Option<Self> {
    if path.count_ones() as usize > leaves.len() {
      return Option::None;
    }
    unsafe { Option::Some(Self::new_unchecked(path, leaves)) }
  }
}

impl<L> Dyck<L> {
  fn new_unchecked(path : &[u32], leaves : Shared<[L]>)->Self {
    if path.len()*u32::BITS as usize > PathInt::BITS as usize {
      let mut v : Vec<u32> = path.into_iter().rev().copied().collect();
      let path_bui = BigUint::new(v);
      unsafe { Dyck::UnboundedDyck( UnboundedDyck::new_unchecked(path_bui, leaves) ) }
    } else {
      let mut path_i = 0;
      for each in path {
        path_i <<= 1;
        path_i |= *each as u64;
      }
      unsafe { Dyck::Bounded( BoundedDyck::new_unchecked(path_i, leaves) ) }
    }
  }

    fn new(path : &[u32], leaves : Shared<[L]>)->Option<Self> {
    if path.len()*u32::BITS as usize > PathInt::BITS as usize {
      let mut v : Vec<u32> = path.into_iter().rev().copied().collect();
      let path_bui = BigUint::new(v);
      UnboundedDyck::new(path_bui, leaves).map(Dyck::UnboundedDyck)
    } else {
      let mut path_i = 0;
      for each in path {
        path_i <<= 1;
        path_i |= *each as u64;
      }
      BoundedDyck::new(path_i, leaves).map( Dyck::Bounded) 
    }
  }
}


struct DyckView<'a, L> {
  path_offset: usize,
  view_of: &'a Dyck<L>,
}

#[cfg(test)]
mod test {
  use crate::*;
  #[test]
  fn test_bed(){
    let bui = BigUint::from( u64::MAX as u128 + 1  );
    for n in bui.iter_u64_digits() {
      std::println!("{}",n)
    }
  }
}