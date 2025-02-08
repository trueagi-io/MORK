use core::hash;
use std::{cell::RefCell, hash::Hasher, marker::PhantomData};


use pathmap::{morphisms::Catamorphism, trie_map::BytesTrieMap};
extern crate alloc;
use alloc::collections::BTreeMap;
use gxhash::{self, GxHasher};


type HashU128 = u128;
type SerializedHash = [u8; 16];



type PathHash  = SerializedHash;
type ValueHash = SerializedHash;
type FixHash   = SerializedHash;
type ChildMask = [u8; 8];

enum ParseAction {
  
}



trait ZipperValue : Clone + Send + Sync + Unpin {}
impl<T> ZipperValue for T where T : Clone + Send + Sync + Unpin {}


fn define<V : ZipperValue>(
    trie : BytesTrieMap<V>,
    serialize_value : impl Fn(&V) -> impl IntoIterator<Item = u8>
) {
    #[repr(C)] 
    struct Header {
        title  : [u8; 256],        
        offset : [u8; 8],
    }

    struct Definitions<V>{
      value_count       : usize,
      values            : BTreeMap<HashU128, usize>,
      inhabited_nodes   : BTreeMap<HashU128, usize>,

    
      // write a header, 
      // after first newline write a slot for a byte offset,
      // serialize the values,
      // finally write a values table at the end of the file then slot the byte offset.
      serialized_values : Vec<u8>,
      values_offsets    : Vec<usize>,
    
      _boo        : PhantomData<V>,
    }
  // not cryptographic
  let mut defs = RefCell::new(Definitions {
    inhabited_nodes   : BTreeMap::new(),

    value_count       : 0,
    values            : BTreeMap::new(),
    values_offsets    : Vec::from([core::mem::size_of::<Header>()]),
    serialized_values : Vec::with_capacity(4096),
    _boo              : PhantomData,
  });

  let hash_bytes = |i|{
    let mut h = GxHasher::with_seed(0);
    let defs_m = defs.borrow_mut();
    for b in iter { 
      defs_m.push(b);
      h.write_u8(b);
    }
    h.finish_u128();
  };

  let add_value_hash = |v| {
    let iter  = serialize_value(v);
    let hash  = hash_bytes(iter);

    let def_m = defs.borrow_mut();

    if defs_m.values.contains_key(*hash) {
      defs_m.serialized_values.truncate(current_len);
    } else {
      let current_len = defs_m.serialized_values.len();
      defs_m.values_offsets.push(current_len);
    }

    hash
  };

  let d = trie.into_cata_jumping_side_effect::<_, _,_,_>(
    |v,_| add_value_hash(v),
    |v,w,_| {
      let next_hash = add_value_hash(v);
      let bytes     = next_hash.to_be_bytes();
      let hash      = hash_bytes(&mut bytes);

      let def_m     = defs.borrow_mut();

    },
    alg_f,
    jump_f,
  );

  panic!();
}