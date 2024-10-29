extern crate core;
extern crate alloc;

use {
  core::{option::Option, convert::From}, 
  alloc::vec::Vec,
  crate::{DyckWord, Sym, Val, DyckStructureZipperU64, Bits, ValPattern}
};

pub(crate) mod substitution;
pub(crate) mod matching;
pub(crate) mod transform;


/// [`DyckExprRef`] is the argument type for doing "solving"
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DyckExprRef<'a>{ pub(crate) word : DyckWord, pub(crate) data : &'a [Val]}

#[allow(unused)]
impl<'a> DyckExprRef<'a> {
  pub fn new(word : DyckWord, data : &'a [Val]) -> Option<Self> {
    Self::valid(word, data).then_some(DyckExprRef { word, data })
  }

  /// there may be performance cases where a check can be elided, this is still checked when debugging.
  pub(crate) fn new_debug_checked(word : DyckWord, data : &'a [Val]) -> Self {
    core::assert!{Self::valid(word, data)} 
    DyckExprRef { word, data }
  }

  /// A slice is considered valid if the length less than the [`DyckWord`]'s number of leaves, 
  /// this assumes that the &\[[`Val`]\] has valid ordering with respect to expressions.
  pub fn valid(word : DyckWord, data : &'a [Val]) -> bool {
    word.word.count_ones() as usize <= data.len()
  }

  // extracts the inner data, removing the validity guarantee
  pub fn extract(self)->(DyckWord, &'a [Val]) {(self.word, self.data)}
}




/// This has a fixed capacity of DyckStructureZipperU64::MAX_LEAVES
///
/// any thing after the `len` should be considered junk, this is safe so long as Val::<Void> is Copy
#[derive(Debug)]
pub struct SmallDyckExpr {
  pub(crate) word: DyckWord,
  pub(crate) len : usize,
  pub(crate) data : [Val; DyckStructureZipperU64::MAX_LEAVES],
}
#[derive(Debug)]
pub struct LargeDyckExpr {
  pub(crate) word: Vec<Bits>,
  pub(crate) data: Vec<Val>,
}
#[allow(unused)]
#[derive(Debug)]
pub enum DyckExprSubOutput {
  SmallDyckExpr(SmallDyckExpr),
  LargeDyckExpr(LargeDyckExpr),
}


impl DyckExprSubOutput {
  #[allow(unused)]
  /// Debugging with the default debug output can sometimes get get hairy, this helps for very large values
  pub fn pretty_print(&self)->alloc::string::String {
    use core::fmt::Write;
    let mut out = alloc::string::String::from("\nDyckExperSubOutput(\n");

    let data = match self {
      DyckExprSubOutput::SmallDyckExpr(SmallDyckExpr { word, len, data }) => {
        let _ = core::writeln!(out, "\tword : {:?}\n\t// {:?}", word, word.applicative_sexpr_viewer());
        &data[0..*len]
      }
      DyckExprSubOutput::LargeDyckExpr(LargeDyckExpr { word, data }) => {
        let _ = core::writeln!(out, "\tword : {word:#?}");
        &data[..]
      }
    };
    let _ = core::writeln!(out, "\tdata : [");
    
    for each in data {
      let _ = match each.decode_val() {
        ValPattern::Intro   => core::writeln!(out, "\t\tVar  $"),
        ValPattern::Ref(r)  => core::writeln!(out, "\t\tVar  $[{}]", r),
        ValPattern::Atom(a) => core::writeln!(out, "\t\tAtom {}", Sym::try_read(a as usize)),
      };
    }
    let _ = core::writeln!(out, "]\n)\n");
    out
  }
}
