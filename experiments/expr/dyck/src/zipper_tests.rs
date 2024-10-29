#![cfg(test)]
extern crate core;
extern crate alloc;
extern crate std;

use {
  core::{option::Option, iter::{Iterator, IntoIterator, Extend}, cmp::Ord},
  alloc::vec::Vec,
  crate::{
    DyckStructureZipperU64, Val, test_parser,
    all_trees,
    solving::{DyckExprRef, transform::transform_re_index_small}
  }
};

#[test]
fn test_zipper_basics() {
  #![cfg_attr(rustfmt, rustfmt::skip)]

  type DSZ = DyckStructureZipperU64;

  '_0b0 :{
    // std::println!("\n# 0b_0\nNone");
    core::assert!(core::matches!(DSZ::new(0b_0), Option::None));
  }

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
    // std::println!("\n# 0b_11010\n");
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
    let mut parser = test_parser::DyckParser::new(src);
    parser.clear_variables();
    let mut next = || {
      let e = parser.next().unwrap().unwrap();
      parser.clear_variables();
      e
    };
    let (       input_zipper,    input_data, _) = next();
    let (     pattern_zipper,  pattern_data, _) = next();
    let (mut template_zipper, template_data, _) = next();
    let (    expected_zipper, expected_data, _) = next();

    fn prep<'a>(z : &DyckStructureZipperU64, d : &'a [Val])-> DyckExprRef<'a> {
      DyckExprRef::new_debug_checked( z.current_substructure(), d)
    }

    template_zipper.decend_right();
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
