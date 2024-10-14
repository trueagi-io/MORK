#![allow(unused)]

extern crate alloc;
extern crate core;

use {
  core::{option::Option, iter::Iterator},
  alloc::vec::Vec,
  crate::{solving::DyckExprRef, DyckStructureZipperU64, ValPattern, Val}
};

/// matches two expression that have have no offset (relative)
pub(crate) fn expr_matches<'a,'b>(lhs: DyckExprRef<'a>, rhs: DyckExprRef<'b>) -> Option<(Vec<DyckExprRef<'b>>, Vec<DyckExprRef<'a>>)> {
  return expr_matches_select::<false>((lhs, 0), (rhs, 0));
}

/// matches two expressions that have offsets (absolute)
pub(crate) fn expr_matches_with_offsets<'a, 'b>(lhs: (DyckExprRef<'a>, u8), rhs: (DyckExprRef<'b>, u8)) -> Option<(Vec<DyckExprRef<'b>>, Vec<DyckExprRef<'a>>)> {
  return expr_matches_select::<true>(lhs, rhs);
}

macro_rules! when {($LHS:expr => $RHS:expr) => { !$LHS || $RHS };}

/// this will return the substitutions when they match, but the offsets are still "baked" into the result.
pub(crate) fn expr_matches_select<'a,'b, const WITH_OFFSET : bool>(
  (DyckExprRef { word:lhs_structure, data: lhs_data}, mut lhs_offset): (DyckExprRef<'a>, u8), 
  (DyckExprRef { word:rhs_structure, data: rhs_data}, mut rhs_offset): (DyckExprRef<'b>, u8)
) -> Option<(Vec<DyckExprRef<'b>>, Vec<DyckExprRef<'a>>)> {
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
    
    use ValPattern::*;

    let append_l = |l : &mut Vec<_>| l.push(DyckExprRef::new_debug_checked(r_struct.current_substructure(), &rhs_data[r_struct.current_leaf_store_index_range()]));
    let append_r = |r : &mut Vec<_>| r.push(DyckExprRef::new_debug_checked(l_struct.current_substructure(), &lhs_data[l_struct.current_leaf_store_index_range()]));
    let matching =  match [
      (l_struct.current_is_leaf(), lhs_data[l_struct.current_first_leaf_store_index()].decode_val()),
      (r_struct.current_is_leaf(), rhs_data[r_struct.current_first_leaf_store_index()].decode_val()),
    ] {
      // /////////
      // Intros //
      // /////////
      [(true, Intro), (true, Intro)] => { append_l(&mut lvars); append_r(&mut rvars); true } 
      [(true, Intro), _]             => { append_l(&mut lvars);                       true }
      [_, (true, Intro)]             => {                       append_r(&mut rvars); true }

      // ////////
      // Atoms //
      // ////////
      [(true, Atom(l)), (true, Atom(r))]                            => l == r,
      [(false, _), (true, Atom(_))] | [(true, Atom(_)), (false, _)] => false,      
      [(true, Ref(v)), (true, a @ Atom(_))] => { let idx_l = (!v) as usize; when!(WITH_OFFSET => idx_l >= lhs_offset as usize) && lvars[idx_l - lhs_offset as usize].data == &[a.encode()] } 
      [(true, a @ Atom(_)), (true, Ref(v))] => { let idx_r = (!v) as usize; when!(WITH_OFFSET => idx_r >= rhs_offset as usize) && rvars[idx_r - rhs_offset as usize].data == &[a.encode()] } 

      // ///////
      // Refs //
      // ///////
      [(true, Ref(lv_r)), (true, Ref(rv_r))] => matching_refs_offset_rel_rel::<WITH_OFFSET>([(lv_r, lhs_offset as usize, &lvars), (rv_r, rhs_offset as usize, &rvars)]),
      [(false, _), (true, Ref(_))] | [(true, Ref(_)), (false, _)] => false,

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

    if let core::ops::ControlFlow::Break(matching) = go_right_or_accend_together(&mut l_struct, &mut r_struct) {
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

  fn matching_refs_offset_rel_rel<const WITH_OFFSET : bool>([(lv_r, mut lhs_offset, lvars), (rv_r, mut rhs_offset, rvars)]: [(isize, usize, &[DyckExprRef]);2])->bool{
    if !WITH_OFFSET {
      core::debug_assert_eq!(lhs_offset,0);
      core::debug_assert_eq!(rhs_offset,0);
      lhs_offset = 0;
      rhs_offset = 0;
    }
    let idx_l = (!lv_r) as usize;
    let idx_r = (!rv_r) as usize;

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
    if left.word != right.word {
      return false;
    }
    macro_rules! decoded {($S:ident) => { $S.data.iter().copied().map(Val::decode_val) };}
    for each in decoded!(left).zip(decoded!(right)) {
      use ValPattern::*;
      let matching = match each {
        (Atom(l), Atom(r)) => l == r,
        (Intro, Intro) => true,
        (Ref(l), Ref(r)) => 
          if when!(WITH_OFFSET => l.is_positive() && r.is_positive()) { 
            l == r 
          } else {
            (!l) as usize - lhs_offset == (!r) as usize - rhs_offset 
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




