extern crate core;
  extern crate alloc;
  extern crate std;

  use core::{
  sync::atomic::AtomicUsize, 
  option::Option
};

/// The global symbol table
#[allow(non_snake_case)]
struct SymStatics {
  INTERNED_STR_NUM     : std::sync::RwLock<alloc::collections::BTreeMap<&'static str, usize>>,
  INTERNED_NUM_STR     : std::sync::RwLock<alloc::collections::BTreeMap<usize, &'static str>>,
  INTERNED_STR_COUNTER : AtomicUsize,
}
  
  // Sym is valid if it has an empty str, or if it holds and interned str.
  // the Ord in a Sym has no relation to what it represents, only in that it can be used in a datastructure and that it represents a unique value
  #[derive(Clone, Copy,PartialOrd, Ord, PartialEq, Eq)]
  pub struct Sym(pub(crate) usize);
impl Sym {

  fn sym_statics()-> &'static SymStatics {
    // if string interning is slow, it could be split into buckets, perhaps even Semaphores. but for testing this should be enough
    static SYM_STATICS : SymStatics = SymStatics { 
      INTERNED_STR_NUM: std::sync::RwLock::new(alloc::collections::BTreeMap::new()), 
      INTERNED_NUM_STR: std::sync::RwLock::new(alloc::collections::BTreeMap::new()), 
      INTERNED_STR_COUNTER: AtomicUsize::new(1 /* Non-zero */)
    };
    &SYM_STATICS
  }

  /// Despite the name, this function does not return a result, instead unregisterd symbols are simply marked as "?UNREGISTERED?".
  pub fn try_read(handle : usize) -> &'static str {
    Sym::sym_statics().INTERNED_NUM_STR.read().unwrap().get(&handle).map(|v|*v).unwrap_or("?UNREGISTERED?")
  }

  /// Looks into the gobal symbol table for a [`Sym`], if it cannot find one it will create one
  pub fn new(s: &str) -> Sym {
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
