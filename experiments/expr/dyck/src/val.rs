extern crate core;
extern crate alloc;
use {
  core::{option::Option, convert::From},
  alloc::vec::Vec,
  crate::Sym
};


/// The value in an expression, encoded
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Val(pub(crate) isize);

impl Val {
  pub const INTRO: Val = Val(0);
  /// Atoms are bindings to the symbol table
  pub const fn atom(sym:Sym)->Val { 
    core::debug_assert!(sym.0 > 0);
    Val(sym.0 as isize)
  }
  /// the method used for doing patern matching
  pub const fn decode_val(self)->ValPattern {
    match self.0 {
      0                    => ValPattern::Intro,
      r if r.is_negative() => ValPattern::Ref(r),
      a                    => ValPattern::Atom(a)
    }
  }

  /// an alternate representation for debugging
  pub const fn dbg_val<'a>(slice : &'a[Self])-> &'a[Val] {
    // Safety : #[repr(transparent)]
    unsafe { core::mem::transmute(slice) }
  }

  /// modifes the slice in place, adding an offset to __all__ intros and references
  pub fn to_absolute_mut(data: &mut [Val], offset: usize) {
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
  /// like [`Self::to_absolute_mut`], but it creates a new value befor modifying .
  pub fn to_absolute(data: &[Val], offset: usize) -> Vec<Val> {
    let mut out = Vec::from(data);
    Val::to_absolute_mut(&mut out, offset);
    out
  }
  
  /// the inverse of [`Self::to_absolute_mut`]
  pub fn to_relative_mut(data: &mut [Val]) {
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
  
  /// the inverse of [`Self::to_absolute`]
  pub fn to_relative(data: &[Val]) -> Vec<Val> {
    let mut out = Vec::from(data);
    Val::to_relative_mut(&mut out);
    out
  }
}

/// the type used to safely determine the encoded Val's interpretation
#[cfg_attr(rustfmt, rustfmt::skip)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ValPattern {
  /** zero */            Intro,
  /** always negative */ Ref(isize),
  /** always positive */ Atom(isize), 
}
impl ValPattern {
  /// 
  pub const fn encode(self)->Val {match self {
    ValPattern::Intro => Val::INTRO,
    ValPattern::Ref(v) | ValPattern::Atom(v) => Val(v),
  }}
}

/// this struct exist purely as an alternative way to display a slice of [`Val`]s
#[repr(transparent)]
pub struct DbgVal(pub(crate) Val);
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


