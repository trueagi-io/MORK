#![allow(unused)]

extern crate core;
extern crate alloc;
#[cfg(debug_assertions)]
extern crate std;

use {
  core::{result::Result, iter::Iterator, convert::From}, 
  alloc::vec::Vec,
  crate::{
    DyckStructureZipperU64, Val, Sym, ValPattern, DyckWord, Bits,
    solving::{DyckExprRef, DyckExprSubOutput, SmallDyckExpr, LargeDyckExpr}
  }
};

macro_rules! when {($LHS:expr => $RHS:expr) => { !$LHS || $RHS };}

pub(crate) fn subst_re_index_with_pat_offset(pat: (DyckExprRef, u8), subs: &[DyckExprRef]) -> DyckExprSubOutput {
  subst_select::<true,true,false>(pat, (subs, 0), 0)
}

// this can be optimized by inlining the large version and specializing, but given that it would incur more checks, it might not be worth it. on the happy path, the performance is the same
pub(crate) fn subst_re_index_small(pat: (DyckExprRef, u8), subs: &[DyckExprRef]) -> Result<SmallDyckExpr, ()> {
  match subst_re_index_with_pat_offset(pat, subs) {
    DyckExprSubOutput::SmallDyckExpr(s) => Result::Ok(s),
    DyckExprSubOutput::LargeDyckExpr(_) => Result::Err(()),
  }
}


pub(crate) fn subst_rel(pat: (DyckExprRef, u8), subs: &[DyckExprRef]) -> DyckExprSubOutput {
  subst_select::<false, true, false>(pat, (subs, 0), 0)
}

// this can be optimized by inlining the large version and specializing, but given that it would incur more checks, it might not be worth it. on the happy path, the performance is the same
pub(crate) fn subst_rel_small(pat: (DyckExprRef, u8), subs: &[DyckExprRef]) -> Result<SmallDyckExpr, ()> {
  match subst_rel(pat, subs) {
    DyckExprSubOutput::SmallDyckExpr(s) => Result::Ok(s),
    DyckExprSubOutput::LargeDyckExpr(_) => Result::Err(()),
  }
}


pub(crate) fn subst_select<const WITH_RE_INDEX:bool, const INPUT_OFFSETS : bool, const OUTPUT_OFFSET : bool>(
  (DyckExprRef { word : pat_structure, data: pat_data }, pat_offset): (DyckExprRef, u8), 
  // the assumption is that all subs come from a match so the offsets would all be the same
  (subs, subs_offset): (&[DyckExprRef], u8),
  mut output_offset : u8
) -> DyckExprSubOutput {
  #![cfg_attr(rustfmt, rustfmt::skip)]

  if !OUTPUT_OFFSET {
    core::debug_assert_eq!(output_offset, 0);
    output_offset = 0;
  }

  const MAX_LEAVES: usize = DyckStructureZipperU64::MAX_LEAVES;
  core::debug_assert!(pat_data.len() < MAX_LEAVES);
  core::debug_assert!(subs.len() < MAX_LEAVES);
  for each in subs {
    core::debug_assert!(each.data.len() < MAX_LEAVES);
    core::debug_assert!(each.data.len() != 0);
  }
  core::debug_assert!{pat_data.iter().all(|v| if let ValPattern::Ref(r) = v.decode_val() { subs.len() as isize >= !r - pat_offset as isize  }else{true})}


  const MAX_INTROS :usize = 63;
  const INDEX_LEN : usize = MAX_INTROS + 1;
  type Index = [u8; INDEX_LEN];
  const INDEX: Index = [0; INDEX_LEN];

  // stores the the number of consecutive 0 bits
  let mut trailing_pairs = [0u8;MAX_LEAVES];

  let mut pat = PatternData {
    pat_offset,
    pat_intros : pat_offset as u8,

  };

  let mut sub = SubsData { subs, subs_offset };

  let mut out = OutData { 
    dyck_words  : [0_u64; MAX_LEAVES], 
    out_depth   : INDEX,
    output_len  : 0, 
    output_data : [Val::atom(Sym::new("")); MAX_LEAVES * MAX_LEAVES],
  };

  if WITH_RE_INDEX{ 
    for each in 1..=pat_offset {
      out.out_depth[each as usize] = each;
    }
  }

  let mut pat_structure_word = pat_structure.word;
  // add terminal 1 bit before shifting fully , avoids counting too many pairs
  pat_structure_word = ((pat_structure_word << 1) | 1) << pat_structure_word.leading_zeros() - 1;

  for each in 0..pat_data.len() {
    
    match pat_data[each].decode_val() {
      ValPattern::Intro => for_all_subs::<WITH_RE_INDEX, INPUT_OFFSETS, OUTPUT_OFFSET, false>(&mut pat, &mut sub, &mut out, isize::MAX /* unused */, each, output_offset),
      ValPattern::Ref(r) => { if when!(INPUT_OFFSETS => (!r) as u8 >= pat_offset) {
          for_all_subs::<WITH_RE_INDEX, INPUT_OFFSETS, OUTPUT_OFFSET, true >(&mut pat, &mut sub, &mut out, r, each, output_offset)
        } else {
          core::debug_assert!(false, "There was nothing to substitute")
        }
      }
      val => {
        out.output_data[out.output_len] = val.encode();
        out.dyck_words[each] = 1;
        out.output_len += 1;
      }
    }
    
    // shift off a leaf
    pat_structure_word <<= 1;
    let pairs = pat_structure_word.leading_zeros();
    trailing_pairs[each] = pairs as u8;
    // shift off consecutive pairs
    pat_structure_word <<= pairs;
  }

  return build_dyck_expr_from_subst(pat_data.len(), out.output_len, &out.output_data, &trailing_pairs, &out.dyck_words);


  // Where ...

  #[derive(Debug)]
  struct PatternData {
    pat_offset       : u8,
    pat_intros       : u8,
  }
  #[derive(Debug)]
  struct SubsData<'a> {
    subs        : &'a [DyckExprRef<'a>],
    subs_offset : u8
  }
  struct OutData {
    dyck_words : [u64; MAX_LEAVES], 
    out_depth  : Index, 
    output_len : usize, 
    output_data: [Val; 1024]
  }
  impl core::fmt::Debug for OutData {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
      f.debug_struct("OutData")
      .field("\n\tdyck_words      ", &self.dyck_words)
      .field("\n\tout_depth       ", &self.out_depth)
      .field("\n\toutput_len      ", &self.output_len)
      .field("\n\toutput_data     ", &Val::dbg_val( &self.output_data[0..self.output_len] )).finish()
    }
  }
  fn for_all_subs<
    const WITH_RE_INDEX : bool, 
    const INPUT_OFFSETS : bool, 
    const OUTPUT_OFFSET : bool, 
    const REF_BRANCH    : bool
  >(
    PatternData { pat_offset, pat_intros } : &mut PatternData,
    SubsData { subs, subs_offset } : &mut SubsData,
    OutData { dyck_words, out_depth, output_len, output_data } : &mut OutData,

    // Ignored if !REF_BRANCH
    ref_value : isize,
    // pattern position/loop iteration
    each : usize,
    output_offset : u8
  ) {
    #![inline(always)]

    let idx = if REF_BRANCH {(!ref_value) as usize} else {*pat_intros as usize};
    let DyckExprRef{ word : sub_struct, data: sub_data } = subs[idx - if INPUT_OFFSETS {*pat_offset as usize}else{0}];
    
    
    let depth_offset = out_depth[if WITH_RE_INDEX {idx } else {0}];

    
    // refs need to know how many intros they passed
    let mut intros_count = 0 as isize;

    let new_ref = |v : isize| 
              { let v_ = v + if INPUT_OFFSETS { *pat_offset as isize } else {0} - if OUTPUT_OFFSET {output_offset as isize} else {0};
                core::debug_assert!( v_ < 0);
                Val(v_)
              };
    for &sub_val in sub_data {
      output_data[*output_len] = if WITH_RE_INDEX {
        match sub_val.decode_val() {
          ValPattern::Ref(r) => {
            let mut r_calc = r;
            if INPUT_OFFSETS { r_calc += *subs_offset as isize; }
            new_ref(r_calc - depth_offset as isize)
          },
          ValPattern::Intro => {
            if REF_BRANCH {
              let val = !(intros_count + depth_offset as isize);
              intros_count += 1;
              
              new_ref(val)
            } else {
              out_depth[idx + 1] += 1;
              sub_val
            }
          }
          _ => sub_val,
        }
      } else {
        // reminder : !WITH_RE_INDEX
        sub_val
      };
      *output_len += 1;
    }
    dyck_words[each] = sub_struct.word;
    
    if !REF_BRANCH {
      out_depth[idx+1] += out_depth[idx];
      *pat_intros += 1;
    }
  }

  fn build_dyck_expr_from_subst(
    input_len      : usize,
    output_len     : usize,
    output_data    : &[Val; MAX_LEAVES * MAX_LEAVES],
    trailing_pairs : &[u8; MAX_LEAVES],
    dyck_words     : &[u64; MAX_LEAVES],
  ) -> DyckExprSubOutput {
    #![inline(always)]
  
    let mut output_word_len = 0;
    let [mut cur, mut next] = [0_u64; 2];
    let mut finished = Vec::new();
    let mut last_div = 0;
  
    for each in (0..input_len).rev() {
      output_word_len += trailing_pairs[each] as usize;
      let (cur_div, cur_mod) = (output_word_len / 64, output_word_len % 64);
    
      // check if we need to advance the "cursor"
      if last_div < cur_div {
        core::debug_assert!(output_len > DyckStructureZipperU64::MAX_LEAVES);
        if finished.len() == 0 {
          finished = Vec::with_capacity(DyckStructureZipperU64::MAX_LEAVES);
        }
        finished.push(cur);
        (cur, next) = (next, 0);
      }
    
      let cur_word = dyck_words[each];
    
      [cur, next] = [cur | cur_word << cur_mod, if cur_mod == 0 { 0 } else { next | cur_word >> u64::BITS - cur_mod as u32 }];
      output_word_len += (u64::BITS - cur_word.leading_zeros()) as usize;
      last_div = cur_div;
    }

  
    if next == 0 && finished.len() == 0 {
      let mut data = [Val::INTRO; 32];
      for each in 0..output_len {
        data[each] = output_data[each];
      }
    
      DyckExprSubOutput::SmallDyckExpr(SmallDyckExpr { word: DyckWord::new_debug_checked(cur), data , len : output_len})
    } else {
      let data = Vec::from(&output_data[0..output_len]);
    
      finished.push(cur);
      if next != 0 || cur.leading_zeros() == 0 {
        finished.push(next);
      }
      finished.reverse();
    
      DyckExprSubOutput::LargeDyckExpr(LargeDyckExpr { word: /* Safety: repr transparent */ unsafe { core::mem::transmute::<_,Vec<Bits>>(finished) }, data })
    }
  }
  // end of subst_select
}

