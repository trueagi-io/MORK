//! Bucket map attemps to tackle the symbol mapping problem by spreading the load to as many buckets
//! as possible with a simple and efficient method to spit the keys
//!
//! # Algorithm Overview
//!
//! The [`SharedMapping`] contains [`MAX_WRITER_THREADS`] append-only linked lists of [`Slab`] objects, where
//! each `Slab` is a contiguous block of memory containing the symbol.  The `Slab` lists start are at [SharedMapping::permissions].
//!
//! The [`Symbol`] type is a fixed-size (8-Bytes) reference to a symbol in the symbol table.
//!
//! The [SharedMapping::to_bytes] contains maps (PathMaps) to map from [`Symbol`] to a byte pointer in the [Slab]s
//! ([ThinBytes] type).  The symbol's `permission_idx` selects which PathMap to perform the lookup in.
//!
//! The [SharedMapping::to_symbol] contains maps (PathMaps) to map from raw symbol bytes to a [`Symbol`] handle.
//! The `MAX_WRITER_THREADS` pathmaps use a Pearson hash on the first 8 Bytes of the symbol to reduce contention
//! over the `PathMaps`  TODO: We may want to revisit the first 8-Byte behavior if we end up with symbols that
//! all contain the same prefix, e.g. a namespace.
//!

extern crate alloc;

use core::{marker::PhantomData, mem::MaybeUninit, sync::atomic::{self, AtomicPtr, AtomicU64}};
use pathmap::PathMap;

mod handle;
use handle::*;
pub use handle::SharedMappingHandle;
pub use handle::WritePermit;

mod symbol_backing;
use symbol_backing::*;

#[cfg(feature = "debug_api")]
pub use symbol_backing::ThinBytes;

mod serialization;

#[cfg(feature = "debug_api")]
pub use serialization::Tables;

const U64_BYTES : usize = u64::BITS as usize / 8;

/// Uniquely identifies a symbol in the table
///
/// [0, 1]: unused
/// [2]: permission_idx.  Identifies which list in [SharedMapping::permissions] contains the symbol
/// [3..=7]: unique symbol id within slab list.  Corresponds to insertion order in list
///
type Symbol = [u8;SYM_LEN];
#[doc(hidden)]
pub const SYM_LEN : usize = 8;

/// it's important that the top bit is NOT set, as that would suggest it is a De Bruijn Level reference
const MAX_WRITER_THREAD_INDEX : usize = i8::MAX as usize;
#[doc(hidden)]
pub const MAX_WRITER_THREADS : usize = MAX_WRITER_THREAD_INDEX+1;
const SYMBOL_THREAD_PERMIT_BYTE_POS : usize = 2;

/// We don't want locks to implicitly cause chache misses because they are too close together.
#[repr(align(64 /* bytes; cache line */))]
pub(crate) struct AlignCache<T>(pub(crate) T);
type AlignArray<T> = [AlignCache<T>; MAX_WRITER_THREADS];


#[repr(u64)]
enum SharedMappingFlags {
  KeepSlabsAlive = 1 << 0,
  HeapAllocated   = 1 << 1,
}
pub(crate) const PEARSON_BOUND : usize = 8;

/// The [`SharedMapping`] is the datatype that holds buckets to split the maps that hold the symbols to reduce contention bewteen multiple threads.
/// There can be a maximum of 128 threads that can write.

pub struct SharedMapping {
  pub(crate) count             : AtomicU64,
  pub(crate) flags             : AtomicU64,
  pub(crate) permissions       : AlignArray<ThreadPermission>,
  pub(crate) to_symbol         : AlignArray<std::sync::RwLock<PathMap<Symbol>>>,
  /// the path is a Symbol as __big endian bytes__.
  pub(crate) to_bytes          : AlignArray<std::sync::RwLock<PathMap<ThinBytes>>>,
}

impl SharedMapping {
  /// This function will allocate a new SharedMapping returning back a reference counted handle
  pub fn new()->SharedMappingHandle {
    unsafe {
      let ptr = alloc::alloc::alloc(alloc::alloc::Layout::new::<MaybeUninit<SharedMapping>>()) as *mut MaybeUninit<SharedMapping>;
      SharedMapping::init(ptr, SharedMappingFlags::HeapAllocated as u64)
    }
  }

  /// This is unsafe because this could be done inside a stack frame, which makes safety guarantees more difficult.
  /// This has been made public for use in initializing a static.
  pub const unsafe fn init(uninit : *mut MaybeUninit<SharedMapping>, init_flags: u64)-> SharedMappingHandle {
    unsafe {
      let inner = (*uninit).as_mut_ptr();

      (*inner).count = AtomicU64::new(1);
      (*inner).flags = AtomicU64::new(init_flags);

      let mut i = 0;
      while i <= MAX_WRITER_THREAD_INDEX {
        (&raw mut (*inner).permissions[i]).write(AlignCache(ThreadPermission::init(i as u8)));
        (&raw mut (*inner).to_symbol[i]).write(AlignCache(std::sync::RwLock::new(PathMap::new())));
        (&raw mut (*inner).to_bytes[i]).write(AlignCache(std::sync::RwLock::new(PathMap::new())));

        i+=1;
      }
      SharedMappingHandle( core::ptr::NonNull::new_unchecked(inner) )
    }
  }

  /// Aquire the bytes associated with a [`Symbol`]
  pub fn get_bytes(&self, sym: Symbol)-> Option<&[u8]> {
    if sym[SYMBOL_THREAD_PERMIT_BYTE_POS] > i8::MIN as u8 {
      return None;
    }
    let bucket = sym[SYMBOL_THREAD_PERMIT_BYTE_POS];

    '_lock_scope : {
      self.to_bytes[bucket as usize].0.read().unwrap().get(sym)
    }.map(|t| unsafe {&*t.as_raw_slice()})
  }

  /// This function is not inherently unsafe, but should only be used as a last resort when
  /// the lifetime of references to the backing symbol table must linger.
  pub unsafe fn keep_slabs_alive(&self) {
    self.flags.store(SharedMappingFlags::KeepSlabsAlive as u64, atomic::Ordering::Release);
  }

  /// try to get a [`Symbol`] if it is already in the map.
  /// If one requires a guaranteed [`Symbol`], then consider creating a [`WritePermit`] and using [`WritePermit::get_or_insert`].
  pub fn get_sym(&self, bytes : &[u8]) -> Option<Symbol> {

    let hash = bounded_pearson_hash::<PEARSON_BOUND>(bytes);

    let trie_lock = &self.to_symbol[hash as usize % MAX_WRITER_THREADS].0;

    '_lock_scope:{
      let lock_guard = trie_lock.read().unwrap();

      lock_guard.get(bytes).copied()
    }
  }
}


impl core::ops::Drop for SharedMapping {
  fn drop(&mut self) {

    if self.flags.load(atomic::Ordering::Acquire) & SharedMappingFlags::KeepSlabsAlive as u64 != 0 {
      // leak the Slabs, but free the maps
      return;
    }

    for each in &self.permissions[..] {
      let slab = each.0.symbol_table_start.load(atomic::Ordering::Relaxed);
      unsafe {Slab::free(slab)};
    } 
  }
}


/// Represents the data that a thread can access after aquiring a [`WritePermit`], a thread can only have access to one permit.
/// each Thread permit has an index built into the top byte of it's `next_symbol` field.
pub(crate) struct ThreadPermission{
  // flags : AtomicU64,
  /// [`std::thread::ThreadId`] holds an [`std::num::NonZeroU64`]. this Atomic represents an `Option<std::num::NonZeroU64>` where `Option::None == 0`
  pub(crate) thread_id : AtomicU64, 
  /// the leading byte represents the "thread number"
  /// the rest represents the symbol count
  pub(crate) next_symbol : AtomicU64,
  /// this value should be null if a symbol table is not initialized
  pub(crate) symbol_table_start   : std::sync::atomic::AtomicPtr<Slab>,
  /// this value should be null if a symbol table is not initialized
  pub(crate) symbol_table_last : std::sync::atomic::AtomicPtr<Slab>,
}


impl ThreadPermission {
  const fn init(index : u8) -> ThreadPermission {
    core::debug_assert!(index < 0b_1000_0000, "The top bit of a symbol must be kept off.");
    let next_symbol_val = if index == 0 {1 /* We want to leave the 0 case clear, as that represents the De Bruijn variable introduction */} else {(index as u64) << (u64::BITS - u8::BITS*3 /* leave the top two bytes free for encoding in the pathmap the type/len, the third byte has the map index, the last 5 bytes leave the possibility for 2^40 symbols */)};
    ThreadPermission {
      thread_id: AtomicU64::new(0),
      next_symbol: AtomicU64::new(next_symbol_val),
      symbol_table_start: AtomicPtr::new(core::ptr::null_mut()),
      symbol_table_last: AtomicPtr::new(core::ptr::null_mut()),
    }
  }
}


/// micro-Pearson hash, this is just to spread the buckets threads deposit into, hoping to avoid degenerate cases.
/// `SELECTION` determines how many bytes will be selected for the hash.
/// `SELECTION` must be greater than 1, otherwise it would always return 0 (defeating the purpose of the hash).
fn bounded_pearson_hash<const SELECTION : usize>(bytes : &[u8]) -> u8 {
  core::debug_assert_ne!(SELECTION,0);

  // it's important that each value is unique;
  #[cfg_attr(rustfmt, rustfmt::skip)]
  const PEARSON_TABLE : [u8;256] = [
     65,  243,  145,   88,  141,   27,   18,   96,  233,  173,  239,  229,   48,   29,   67,  214,
     39,  230,   19,  237,  128,   49,   95,  220,  216,  198,  249,   79,  204,  171,  200,  184,
      0,  111,  219,  163,  140,   59,  114,   33,  207,   41,  210,   70,  104,  137,   14,  118,
     71,   80,  209,   35,  234,   13,  232,  149,   99,  159,  153,  165,  241,   47,   38,  218,
     57,  227,  131,   68,  247,  197,  187,  105,  253,   77,  156,   16,   24,   94,  255,  181,
     54,  120,  160,  182,  244,   62,  194,    8,  113,   20,   22,  138,   17,  135,  202,   61,
     58,  185,  240,   51,  169,  179,  196,  154,  167,   55,    3,  235,    4,  238,   12,  142,
    150,  157,  108,  133,  226,  109,  172,   34,   86,  103,  106,  127,  130,   42,  168,  148,
    245,  100,  143,  123,  155,  206,   60,   72,   11,   10,  180,   64,  215,  177,   92,  189,
     90,  186,  225,  115,  228,  208,  176,   82,  102,  190,  119,  222,  139,  166,  211,  136,
     89,  231,   74,   69,   56,  162,   53,    2,   87,  164,   76,  125,  205,  195,   73,    5,
    107,    6,   30,  203,  213,  188,  110,  248,  144,  101,  151,  126,   15,   91,  242,  183,
     44,  146,   25,   78,  223,  254,  236,  112,   50,   31,  224,  250,   84,  221,   46,   43,
     98,    7,  147,  199,   85,  116,   66,   28,  252,    1,   93,  192,  158,  212,  124,   81,
    175,   63,  201,   36,  217,  251,   83,   26,   52,   37,   97,  152,  134,   45,   21,  178,
    174,  193,  161,  129,  170,   75,  132,    9,  122,   32,   23,  246,  191,  117,  121,   40,
  ];

  let mut selection = [0;SELECTION];
  for each in 0..SELECTION.min(bytes.len()) {
    selection[each] = bytes[each]
  }
  let mut hash = 0;
  for each in selection {
    hash = PEARSON_TABLE[(hash ^ each) as usize]
  }

  hash
}

#[cfg(test)] mod test;