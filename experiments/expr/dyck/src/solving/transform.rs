#![allow(unused)]
#[cfg_attr(rustfmt, rustfmt::skip)]
extern crate core;

use {
  core::option::Option,
  crate::solving::{DyckExprRef, SmallDyckExpr, DyckExprSubOutput} 
};

pub(crate) fn transform_re_index(
  arg     : DyckExprRef,
  pat     : DyckExprRef,
  template: DyckExprRef
)-> Option<DyckExprSubOutput>{
  transform_select::<true, false, false>((arg, 0), (pat, 0), (template, 0),0)
}
pub(crate)  fn transform_re_index_small(
  arg     : DyckExprRef,
  pat     : DyckExprRef,
  template: DyckExprRef
)-> Option<SmallDyckExpr>{
  if let Option::Some(DyckExprSubOutput::SmallDyckExpr(s)) = transform_re_index(arg, pat, template)
  {
    Option::Some(s) 
  } else {
    Option::None
  }
}

fn transform_select<const WITH_RE_INDEX : bool, const SUBS_OFFSET : bool, const OUTPUT_OFFSET : bool>(
  args          : (DyckExprRef, u8),
  pat           : (DyckExprRef, u8),
  template      : (DyckExprRef, u8),
  output_offset : u8,
)-> Option<DyckExprSubOutput>{
  let subs = crate::solving::matching::expr_matches_select::<SUBS_OFFSET>(args, pat)?;
  Option::Some(crate::solving::substitution::subst_select::<WITH_RE_INDEX, SUBS_OFFSET, OUTPUT_OFFSET>(template, (&subs.1, pat.1), output_offset))
}