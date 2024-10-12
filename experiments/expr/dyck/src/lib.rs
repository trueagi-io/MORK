#![no_implicit_prelude]
#![allow(unused_imports, unused_variables, dead_code)]

extern crate alloc;
extern crate core;
extern crate std;

extern crate bnum;
extern crate num_bigint;

use alloc::{boxed::Box, collections::BTreeMap, vec::Vec};
use core::iter::Extend;
use core::{
  clone::Clone,
  cmp::Ord,
  convert::From,
  default::Default,
  iter::{IntoIterator, Iterator},
  ops::FnMut,
  option::Option,
  result::Result,
  str,
  marker::PhantomData, 
  num::NonZeroIsize, 
  sync::atomic::AtomicUsize
};
use num_bigint::BigUint;


pub mod test_parser;
mod cz2_unit_tests;
pub(crate) mod left_branch_impl;

mod dyck_zipper;
pub(crate) use dyck_zipper::*;


mod zipper_tests;

/// It should be noted that the terminal is _NEVER_ equal to the head.
/// In the case of a leaf, the head is at the leaf position, and the terminal is one after it.
/// In other words, if t is the terminal, and h is the head, then
/// for a tree `0...001` we have `0..0th` (_t_=1, _h_=0),
///
/// example
/// - `0..0t____h` (_t_=5, _h_=0) tree `0..0011010`
/// - `0..0t__h__` (_t_=5, _h_=2) the left sub tree
/// - `0..0___th_` (_t_=2, _h_=1) the right sub tree (a leaf)
#[derive(Clone, Copy, PartialEq)]
pub struct SubtreeSlice {
  /// the position right after the last leaf of a subtree.
  pub(crate) terminal: u8,
  /// the position of the subtree (the root is a subtree of itself)
  pub(crate) head: u8,
}
/// this is used exclusively for initializing data.
impl SubtreeSlice {
  const fn zeroes() -> Self {
    Self { terminal: 0, head: 0 }
  }
  fn is_leaf(&self) -> bool {
    1 == self.terminal - self.head
  }
  fn left_subtree_head(self, structure: u64) -> u64 {
    let slice = (structure & (0b_10_u64 << self.terminal - 1).wrapping_sub(1)) >> self.head;

    left_branch_impl::u64::left_branch(slice) << self.head
  }
}

/// importantly, the leading zeros are relevant!
#[repr(transparent)]
#[derive(Clone, Copy)]
struct Bits(pub u64);
impl core::fmt::Debug for Bits {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    core::write!(f, "{:#066b}", self.0)
  }
}


/// Represents the structure of a binary tree.  
/// 
/// for the sake of simplifying the implementation of other parts a [`DyckWord`] is defined to be non-empty
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct DyckWord {
  word: u64,
}
impl DyckWord {
  const LEAF : Self = DyckWord {word : 1};
  const fn new(word: u64) -> Option<Self> {
    if DyckWord::valid_non_empty(word) {
     Option::Some( DyckWord { word } )      
    } else {
      Option::None
    }
  }
  const fn new_debug_checked(word: u64) -> Self {
    core::debug_assert!{DyckWord::valid_non_empty(word)}
    DyckWord { word }
  }
  const fn zipper(self) -> DyckStructureZipperU64 {
    let mut stack = [SubtreeSlice::zeroes(); DyckStructureZipperU64::MAX_LEAVES];
    stack[0].terminal = (u64::BITS).wrapping_sub(self.word.leading_zeros()) as u8;

    DyckStructureZipperU64 { structure: self.word, current_depth: 0, stack }
  }
  const fn valid_non_empty(word: u64)->bool {
    let leading = word.leading_zeros();
    if leading == 0 {return false;}
    
    let mut cursor = 1 << u64::BITS - leading - 1;
    let mut sum: i32 = 0;
    
    // a valid structure must have enough children to pair up before constructing a branch
    loop {
      if sum.is_negative() { return false; }
      if cursor == 0       { return sum == 1 }
    
      sum += if (cursor & word) == 0 { -1 } else { 1 };
      cursor >>= 1;
    }
  }  
  fn applicative_sexpr_viewer(self) -> Result<alloc::string::String, (SexprViewerError, Bits)> {
    use alloc::collections::VecDeque;
    use core::convert::From;
    use SexprViewerError as SVE;
    let mut stack = Vec::new();
    let word = self.word;
    if word == 0 {
      return Result::Err((SVE::Empty, Bits(0)));
    }
    if (word & (1 << u64::BITS - 1)) != 0 {
      return Result::Err((SVE::TopBitNonZero, Bits(1 << u64::BITS - 1)));
    }
    enum S {
      One,
      Nested(VecDeque<u8>),
    }

    let mut cursor = 1 << u64::BITS - word.leading_zeros() - 1;

    while cursor != 0 {
      let bit = cursor & word;
      cursor >>= 1;

      if bit != 0 {
        stack.push(S::One);
        continue;
      }
      let Option::Some(r) = stack.pop() else {
        return Result::Err((SVE::TooManyPairs, Bits(cursor)));
      };
      let Option::Some(l) = stack.pop() else {
        return Result::Err((SVE::TooManyPairs, Bits(cursor)));
      };

      stack.push(match (l, r) {
        (S::One, S::One) => S::Nested(VecDeque::from(Vec::from(b"1 1"))),
        (S::One, S::Nested(mut n)) => {
          n.push_back(b')');
          for &each in b"1 (".into_iter().rev() {
            n.push_front(each)
          }
          S::Nested(n)
        }
        (S::Nested(mut n), S::One) => {
          n.push_back(b' ');
          n.push_back(b'1');
          S::Nested(n)
        }
        (S::Nested(mut n1), S::Nested(mut n2)) => {
          n2.push_front(b'(');
          n2.push_back(b')');

          n1.push_back(b' ');
          n1.extend(n2);
          S::Nested(n1)
        }
      })
    }
    if stack.len() != 1 {
      return Result::Err((SVE::TooFewPairs, Bits(0)));
    }
    let top = stack.pop().unwrap();
    Result::Ok(match top {
      S::One => alloc::string::String::from("1"),
      S::Nested(mut n) => {
        n.push_front(b'(');
        n.push_back(b')');
        // Safety: only contains ascii values b'1', b' ', b'(', and b')'
        alloc::string::String::from(unsafe { str::from_utf8_unchecked(n.make_contiguous()) })
      }
    })
  }
}
#[derive(Debug)]
enum SexprViewerError {
  Empty,
  TopBitNonZero,
  TooManyPairs,
  TooFewPairs,
}
impl core::fmt::Debug for DyckWord {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
      core::write!(f, "0b_{:b}", self.word)
  }
}




#[allow(unused)]
type Int = u32;

// only run this test if `Int`` is u8, u16, or u32
#[allow(unused)]
fn all_trees() -> Vec<Int> {
  let max_leaves = Int::BITS / 2;

  use alloc::collections::BTreeMap;
  use alloc::collections::BTreeSet;
  use core::iter::Iterator;

  type Leaves = u32;
  let mut trees = BTreeMap::<Leaves, BTreeSet<Int>>::new();
  trees.insert(0, BTreeSet::from([0]));
  trees.insert(1, BTreeSet::from([1]));

  for each in 2..=max_leaves {
    let mut s = BTreeSet::<Int>::new();
    for left in 1..each {
      let right = each - left;

      for l in &trees[&left] {
        for r in &trees[&right] {
          let val = (*l << right * 2 - 1 | *r) << 1;
          s.insert(val);
        }
      }
    }
    trees.insert(each, s);
  }
  trees.into_iter().flat_map(|(_, v)| v).collect::<Vec<_>>()
}






#[allow(non_snake_case)]
struct SymStatics {
  INTERNED_STR_NUM     : &'static std::sync::RwLock<alloc::collections::BTreeMap<&'static str, usize>>,
  INTERNED_NUM_STR     : &'static std::sync::RwLock<alloc::collections::BTreeMap<usize, &'static str>>,
  INTERNED_STR_COUNTER : &'static AtomicUsize,
}

// Sym is valid if it has an empty str, or if it holds and interned str.
// the Ord in a Sym has no relation to what it represents, only in that it can be used in a datastructure and that it represents a unique value
#[derive(Clone, Copy,PartialOrd, Ord, PartialEq, Eq)]
pub struct Sym(usize);
impl Sym {
  
  fn sym_statics()-> SymStatics {
    // if string interning is slow, it could be split into buckets, perhaps even Semaphores. but for testing this should be enough
    static INTERNED_STR_NUM: std::sync::RwLock<alloc::collections::BTreeMap<&'static str, usize>> = std::sync::RwLock::new(alloc::collections::BTreeMap::new());
    static INTERNED_NUM_STR: std::sync::RwLock<alloc::collections::BTreeMap<usize, &'static str>> = std::sync::RwLock::new(alloc::collections::BTreeMap::new());
    static INTERNED_STR_COUNTER : AtomicUsize = AtomicUsize::new(1 /* Non-zero */);

    SymStatics { INTERNED_STR_NUM: &INTERNED_STR_NUM, INTERNED_NUM_STR: &INTERNED_NUM_STR, INTERNED_STR_COUNTER: &INTERNED_STR_COUNTER }
  }

  fn try_read(handle : usize) -> &'static str {
    Sym::sym_statics().INTERNED_NUM_STR.read().unwrap().get(&handle).map(|v|*v).unwrap_or("?UNREGISTERED?")
  }
  fn new(s: &str) -> Sym {
    let SymStatics { INTERNED_STR_NUM, INTERNED_NUM_STR, INTERNED_STR_COUNTER } = Self::sym_statics();
    '_lock_scope: {
      let s_n = INTERNED_STR_NUM.read().unwrap();
      if let Option::Some(interned) = s_n.get(s) {
        return Sym(*interned);
      }
    }
    '_lock_scope : {
      let mut s_n = INTERNED_STR_NUM.write().unwrap();
      let mut n_s = INTERNED_NUM_STR.write().unwrap();
    
      let key = INTERNED_STR_COUNTER.fetch_add(1, core::sync::atomic::Ordering::Relaxed);
      let s_static = <str as alloc::borrow::ToOwned>::to_owned(s).leak();
    
      n_s.insert(key,s_static);
      s_n.insert(s_static, key);
      Sym(key)
    }
  }
}

impl core::fmt::Debug for Sym {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
      let SymStatics { INTERNED_NUM_STR , ..} = Self::sym_statics();
      let s = *'_lock_scope : {INTERNED_NUM_STR.read().unwrap().get(&self.0).unwrap()};
        core::write!(f, "({}->{:?})", self.0, s)
    }
}

impl core::fmt::Display for Sym {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
      let SymStatics { INTERNED_NUM_STR , ..} = Self::sym_statics();
      let s = *'_lock_scope : {INTERNED_NUM_STR.read().unwrap().get(&self.0).unwrap()};
      core::write!(f, "{}", s)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Val(isize);

impl Val {
  const INTRO: Val = Val(0);
  const fn atom(sym:Sym)->Val { 
    core::debug_assert!(sym.0 > 0);
    Val(sym.0 as isize)
  }
  const fn decode_val(self)->ValPattern {
    match self.0 {
      0                    => ValPattern::Intro,
      r if r.is_negative() => ValPattern::Ref(r),
      a                    => ValPattern::Atom(a)
    }
  }
  
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ValPattern {
  Intro,       // zero
  Ref(isize),  // always negative
  Atom(isize), // always positive
}
impl ValPattern {
  const fn encode(self)->Val {match self {
    ValPattern::Intro => Val::INTRO,
    ValPattern::Ref(v) | ValPattern::Atom(v) => Val(v),
  }}
}

#[repr(transparent)]
struct DbgVal(Val);
impl core::fmt::Debug for DbgVal {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    #[cfg_attr(rustfmt, rustfmt::skip)]
    match self.0.decode_val() {
      ValPattern::Intro      => core::write!(f,"$"),
      ValPattern::Ref(i)     => core::write!(f,"$[{i}]"),
      ValPattern::Atom(atom) => core::write!(f,"{}", Sym::try_read(atom as usize)),
    }
  }
}

fn to_absolute_mut(data: &mut [Val], offset: usize) {
  if offset == 0 {
    return;
  }
  let mut intros = 0;
  for each in data {
    *each = match each.decode_val() {
      ValPattern::Intro => {
        // Safety : offset is !=0 because of if guard
        let tmp = Val(-(intros + offset as isize));
        intros += 1;
        tmp
      },
      ValPattern::Ref(r) => Val(r + 1 - offset as isize),
      ValPattern::Atom(a) => Val(a),
    }
  }
}
fn to_absolute(data: &[Val], offset: usize) -> Vec<Val> {
  let mut out = Vec::from(data);
  to_absolute_mut(&mut out, offset);
  out
}

fn to_relative_mut(data: &mut [Val]) {
  let mut offset = Option::None;
  let mut intros = 0;
  for each in data {
    *each = match each.decode_val() {
      ValPattern::Intro => core::panic!("was not absolute"),
      ValPattern::Ref(r) => match offset {
        Option::None => {
          offset = Option::Some(!r);
          intros += 1;
          Val::INTRO
        }
        Option::Some(offset_) => {
          let diff = !r - offset_;
          core::debug_assert!(diff >= 0);
          if intros == diff {
            intros += 1;
            Val::INTRO
          } else {
            // Safety : diff is nonnegative, `!nonnegative` < 0
            Val(!diff)
          }
        }
      },
      ValPattern::Atom(a) => Val(a),
    }
  }
}

fn to_relative(data: &[Val]) -> Vec<Val> {
  let mut out = Vec::from(data);
  to_relative_mut(&mut out);
  out
}


/// This has a fixed capacity of DyckStructureZipperU64::MAX_LEAVES
///
/// any thing after the `len` should be considered junk, this is safe so long as Val::<Void> is Copy
#[derive(Debug)]
struct SmallDyckExpr {
  word: DyckWord,
  len : usize,
  data : [Val; DyckStructureZipperU64::MAX_LEAVES],
}
#[derive(Debug)]
struct LargeDyckExpr {
  word: Vec<Bits>,
  data: Vec<Val>,
}
#[derive(Debug)]
enum DyckExprSubOutput {
  SmallDyckExpr(SmallDyckExpr),
  LargeDyckExpr(LargeDyckExpr),
}

impl DyckExprSubOutput {
  fn pretty_print(&self) {
    std::println!("DyckExperSubOutput(");
    let data = match self {
      DyckExprSubOutput::SmallDyckExpr(SmallDyckExpr { word, len, data }) => {
        std::println!("\tword : {:?}\n\t// {:?}", word, word.applicative_sexpr_viewer());
        &data[0..*len]
      }
      DyckExprSubOutput::LargeDyckExpr(LargeDyckExpr { word, data }) => {
        std::println!("\tword : {word:#?}");
        &data[..]
      }
    };
    std::println!("\tdata : [");
    for each in data {
      use alloc::string::ToString;
      let (tag, val) = match each.decode_val() {
        ValPattern::Intro => ("Var ", "$".to_string()),
        ValPattern::Ref(r) => ("Var ", alloc::format!("$[{}]", r)),
        ValPattern::Atom(a) => ("Atom", Sym::try_read(a as usize).to_string()),
      };
      std::println!("\t\t{tag} {val}")
    }
    std::println!("]");
    std::println!(")\n");
  }
}



#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct DyckExprRef<'a>{ word : DyckWord, data : &'a [Val]}

impl<'a> DyckExprRef<'a> {
  pub fn new(word : DyckWord, data : &'a [Val]) -> Option<Self> {
    Self::valid(word, data).then_some(DyckExprRef { word, data })
  }
  fn new_debug_checked(word : DyckWord, data : &'a [Val]) -> Self {
    core::assert!{Self::valid(word, data)} 
    DyckExprRef { word, data }
  }
  fn valid(word : DyckWord, data : &'a [Val]) -> bool {
    word.word.count_ones() as usize <= data.len()
  }
  pub fn extract(self)->(DyckWord, &'a [Val]) {(self.word, self.data)}
}


fn subst_re_index_with_pat_offset(pat: (DyckExprRef, u8), subs: &[DyckExprRef]) -> DyckExprSubOutput {
  subst_select::<true,true,false>(pat, (subs, 0), 0)
}

// this can be optimized by inlining the large version and specializing, but given that it would incur more checks, it might not be worth it. on the happy path, the performance is the same
fn subst_re_index_small(pat: (DyckExprRef, u8), subs: &[DyckExprRef]) -> Result<SmallDyckExpr, ()> {
  match subst_re_index_with_pat_offset(pat, subs) {
    DyckExprSubOutput::SmallDyckExpr(s) => Result::Ok(s),
    DyckExprSubOutput::LargeDyckExpr(_) => Result::Err(()),
  }
}


fn subst_select<const WITH_RE_INDEX:bool, const INPUT_OFFSETS : bool, const OUTPUT_OFFSET : bool>(
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
      ValPattern::Ref(r) => { if !INPUT_OFFSETS || (!r) as u8 >= pat_offset {
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
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
      f.debug_struct("OutData")
      .field("\n\tdyck_words      ", &self.dyck_words)
      .field("\n\tout_depth       ", &self.out_depth)
      .field("\n\toutput_len      ", &self.output_len)
      .field("\n\toutput_data     ", & unsafe {core::mem::transmute::<_,&[DbgVal]>( &self.output_data[0..self.output_len] )}).finish()
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
    input_len: usize,
    output_len: usize,
    output_data: &[Val; MAX_LEAVES * MAX_LEAVES],
    trailing_pairs: &[u8; MAX_LEAVES],
    dyck_words: &[u64; MAX_LEAVES],
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
  
    let data = Vec::from(&output_data[0..output_len]);
  
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

fn expr_matches<'a,'b>(lhs: DyckExprRef<'a>, rhs: DyckExprRef<'b>) -> Option<(Vec<DyckExprRef<'b>>, Vec<DyckExprRef<'a>>)> {
  return expr_matches_select::<false>((lhs, 0), (rhs, 0));
}

fn expr_matches_with_offsets<'a, 'b>(lhs: (DyckExprRef<'a>, u8), rhs: (DyckExprRef<'b>, u8)) -> Option<(Vec<DyckExprRef<'b>>, Vec<DyckExprRef<'a>>)> {
  return expr_matches_select::<false>(lhs, rhs);
}

/// this will return the substitutions when they match, but the offsets are still "baked" into the result.
fn expr_matches_select<'a,'b, const WITH_OFFSET : bool>(
  (DyckExprRef { word:lhs_structure, data: lhs_data}  , mut lhs_offset): (DyckExprRef<'a>, u8), 
  (DyckExprRef { word:rhs_structure, data: rhs_data}  , mut rhs_offset): (DyckExprRef<'b>, u8)
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
      [(true, Ref(v)), (true, a @ Atom(_))] => { let idx_l = (!v) as usize; (!WITH_OFFSET || idx_l >= lhs_offset as usize) && lvars[idx_l - lhs_offset as usize].data == &[a.encode()] } 
      [(true, a @ Atom(_)), (true, Ref(v))] => { let idx_r = (!v) as usize; (!WITH_OFFSET || idx_r >= rhs_offset as usize) && rvars[idx_r - rhs_offset as usize].data == &[a.encode()] } 

      // ///////
      // Refs //
      // ///////
      [(true, l @ Ref(lv_r)), (true, r @ Ref(rv_r))] => matching_refs_offset_rel_rel::<WITH_OFFSET>([(lv_r, lhs_offset as usize, &lvars), (rv_r, rhs_offset as usize, &rvars)]),
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

    if let std::ops::ControlFlow::Break(matching) = go_right_or_accend_together(&mut l_struct, &mut r_struct) {
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
          if !WITH_OFFSET || l.is_positive() && r.is_positive() { 
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



fn transform_re_index(
  arg     : DyckExprRef,
  pat     : DyckExprRef,
  template: DyckExprRef
)-> Option<DyckExprSubOutput>{
  transform_select::<true, false, false>((arg, 0), (pat, 0), (template, 0),0)
}
  fn transform_re_index_small(
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
  let subs = expr_matches_select::<SUBS_OFFSET>(args, pat)?;
  Option::Some(subst_select::<WITH_RE_INDEX, SUBS_OFFSET, OUTPUT_OFFSET>(template, (&subs.1, pat.1), output_offset))
}


fn subst_rel(pat: (DyckExprRef, u8), subs: &[DyckExprRef]) -> DyckExprSubOutput {
  subst_select::<false, true, false>(pat, (subs, 0), 0)
}

// this can be optimized by inlining the large version and specializing, but given that it would incur more checks, it might not be worth it. on the happy path, the performance is the same
fn subst_rel_small(pat: (DyckExprRef, u8), subs: &[DyckExprRef]) -> Result<SmallDyckExpr, ()> {
  match subst_rel(pat, subs) {
    DyckExprSubOutput::SmallDyckExpr(s) => Result::Ok(s),
    DyckExprSubOutput::LargeDyckExpr(_) => Result::Err(()),
  }
}




