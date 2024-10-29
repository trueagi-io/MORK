#![cfg(test)]

use crate::*;



#[test]
fn test_for_u64() {
  let trees = all_trees();
  std::println!("count : {}", all_trees().len());
  let now = std::time::Instant::now();
  for each in trees {
    // std::print!("{each:032b}\t{:016b}\n",
    core::hint::black_box(crate::left_branch_impl::u64::left_branch(each as u64))
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
    core::hint::black_box(crate::left_branch_impl::big_uint::left_branch(BigUint::from(each)))
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
    core::hint::black_box(crate::left_branch_impl::u512::left_branch(bnum::types::U512::from_digit(each as u64)))
    // )
    ;
  }
  std::println!("time : {} micros", now.elapsed().as_micros())
}
