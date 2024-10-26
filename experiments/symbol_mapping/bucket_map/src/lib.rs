//! Bucket map attemps to tackle the symbol mapping problem by spreading the load to as many buckets as possible with a simple and efficient method to spit the keys

extern crate alloc;

use std::{mem::MaybeUninit, sync::atomic::{self, AtomicPtr, AtomicU64}};

use pathmap::trie_map::BytesTrieMap;
const U64_BYTES : usize = u64::BITS as usize / 8;
type Symbol = i64;
#[repr(align(64 /* bytes; cache line */))]
struct AlignCache<T>(T);
type AlignArray<T> = [AlignCache<T>; MAX_THREAD_INDEX+1];

#[repr(u64)]
enum SharedMappingFlags {
  KeepSlabsAlive = 1 << 0,
  HeapAlocated   = 1 << 1,
}
const PEARSON_BOUND : usize = 8;
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

/// it's importand theat the top bit is NOT set, as that would suggest it is a De Bruijn Level referene
const MAX_THREAD_INDEX : usize = i8::MAX as usize;
const MAX_THREADS : usize = MAX_THREAD_INDEX+1;
pub struct SharedMapping {
  pub(crate) count            : AtomicU64,
  pub(crate) flags            : AtomicU64,
  pub(crate) permissions      : AlignArray<ThreadPermission>,
  pub(crate) to_symbol        : AlignArray<std::sync::RwLock<BytesTrieMap<i64>>>,
  /// the path is a Symbol as __native endian bytes__.
  pub(crate) to_bytes         : AlignArray<std::sync::RwLock<BytesTrieMap<ThinBytes>>>,
}


/// WritePermit is a form of soft guard, the lifetime encourages scoped usage.
pub struct WritePermit<'a>(&'a SharedMappingHandle);

impl<'a> core::ops::Drop for WritePermit<'a> {
  fn drop(&mut self) {
    let permits = LIVE_PERMIT_HANDLES.get()-1;
    LIVE_PERMIT_HANDLES.set(permits);
    
    if permits == 0 {
      self.permissions[MAPPING_THREAD_INDEX.get().unwrap() as usize].0.thread_id.store(0, core::sync::atomic::Ordering::Release);
    }
  }
}

impl<'a> core::ops::Deref for WritePermit<'a> {
  type Target = SharedMapping;
  fn deref(&self) -> &Self::Target {
    unsafe {&*self.0.0.as_ptr()}
  }
}

impl<'a> WritePermit<'a> {
  pub fn get_or_insert(&self, bytes : &[u8]) -> Symbol {
    // the ordering of most of the atomics here use Relaxed, when one would expect Release.
    // the reason is that these atomics are not under contention, once a thread has a permission it is the only one allowed to change those atomic fields.
    // the alternative is to mutate under an `UnsafeCell`, but atomics already do that.

    // try first
    if let Some(sym) = self.get_sym(bytes) {
        return sym;
    }
    let index = MAPPING_THREAD_INDEX.get().unwrap();
    let thread_permission = &self.permissions[index as usize].0;

    // On the happy path we want to make the critical section as small as possible.
    // So we eagerly write to the Slab if the currently allocated one has space.
    // If we find out someone else has beat us to adding it to the store, we want to revert
    // our eager write.
    let mut eager_and_recovery = None;

    let mut slab_ptr = thread_permission.symbol_table_last.load(atomic::Ordering::Relaxed);

    if !thread_permission.symbol_table_start.load(core::sync::atomic::Ordering::Relaxed).is_null() {      
      unsafe {  
        if (*slab_ptr).slab_len-(*slab_ptr).write_pos >= bytes.len() + U64_BYTES {
          let recovery = (slab_ptr, *slab_ptr);
          eager_and_recovery = Some(((&mut *slab_ptr).register_bytes(bytes) ,recovery));
        }
      }
    }

    // as minimal as it might be, we want the critical section as small as posible, so we index first
    let sym_table_lock = &self.to_symbol[bounded_pearson_hash::<PEARSON_BOUND>(bytes) as usize % MAX_THREADS].0;
    let bytes_guard_lock = &self.to_bytes[MAPPING_THREAD_INDEX.get().unwrap() as usize].0;

    let sym = 'lock_scope_sym : {
      let mut sym_guard = sym_table_lock.write().unwrap();
      // try once more to see if we need to make the symbol
      if let Some(s) = sym_guard.get(bytes) {
        // Another thread beat us to it. yay!
        break 'lock_scope_sym *s;
      }

      let thin_bytes_ptr = if let Some((thin_bytes,_)) = eager_and_recovery {
        // the eager write pays off.
        thin_bytes
      } else {
        // We need to hold the lock while allocating, otherwise our allocation goes to waste.
        if slab_ptr.is_null() {
          let allocation = unsafe {Slab::allocate((bytes.len() + U64_BYTES) as u64)};
          thread_permission.symbol_table_start.store(allocation, atomic::Ordering::Relaxed);
          thread_permission.symbol_table_last.store(allocation, atomic::Ordering::Relaxed);
          slab_ptr = allocation;
        }
        unsafe {
          (&mut *slab_ptr).register_bytes(bytes)
        }
      };
      let new_sym = thread_permission.next_symbol.fetch_add(1, atomic::Ordering::Relaxed) as i64;
      
      let old_sym = sym_guard.insert(bytes, new_sym);
      core::debug_assert!(matches!(old_sym, Option::None));
      
      let sym_bytes = new_sym.to_ne_bytes();
      '_lock_scope_bytes : {
        let mut bytes_guard = bytes_guard_lock.write().unwrap();
        let old_thin = bytes_guard.insert(sym_bytes.as_slice(), thin_bytes_ptr);
        core::debug_assert!(matches!(old_thin, Option::None));
      }

      new_sym
    };

    // similarly to entering the critical section, we do cleanup after, even though normally we would prefer to do it as locally as possible
    let next = unsafe {(*slab_ptr).next};
    if !next.is_null() {
      thread_permission.symbol_table_last.store(next, atomic::Ordering::Release);
    }

    if let Some((_,(recovery_ptr, recovery_data))) = eager_and_recovery {
      // if we ever reach this point the ponter never changed, but we need to revert the `Slab` header
      unsafe {*recovery_ptr = recovery_data;}
    }

    sym
  }
}

/// micro-Pearson hash, this is just to spread the buckets threads deposit into, hoping to avoid degenerate cases.
/// `SELECTION` determines how many bytes will be selected for the hash.
/// `SELECTION` must be greater than 1, otherwise it would always return 0 (defeating the purpose of the hash).
fn bounded_pearson_hash<const SELECTION : usize>(bytes : &[u8]) -> u8 {
  core::debug_assert_ne!(SELECTION,0);

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
    
thread_local! {
  static MAPPING_THREAD_INDEX : core::cell::Cell<Option<u8>> = core::cell::Cell::new(None);
  static THREAD_ID : u64 = unsafe {core::mem::transmute::<_,u64> (std::thread::current().id()) };
  static LIVE_PERMIT_HANDLES : core::cell::Cell<usize> = core::cell::Cell::new(0)
}

pub struct SharedMappingHandle(core::ptr::NonNull<SharedMapping>);
impl SharedMappingHandle {


  /// Falure of this method marks a that all permissions were tried and it failed to aquire any.
  /// Failure can be spurious if there are a high number of threads (> [`MAX_THREADS`]), it is recommended to 
  /// retry even if there are many threads as this only competes with writer threads.
  pub fn try_aquire_permission<'a>(&'a self)->Result<WritePermit<'a>, ()> {
    // A thred can only have one permission at a time
    if let Some(_) = MAPPING_THREAD_INDEX.get() {
      LIVE_PERMIT_HANDLES.set(LIVE_PERMIT_HANDLES.get() + 1);
      return Ok(WritePermit(self));
    }

    for each in 0..MAX_THREADS {
      let p = &self.permissions[each];
      if let Ok(_) = p.0.thread_id.compare_exchange(0, THREAD_ID.with(|x|*x)+1, core::sync::atomic::Ordering::Acquire, core::sync::atomic::Ordering::Relaxed) {
        MAPPING_THREAD_INDEX.set(Some(each as u8));
        LIVE_PERMIT_HANDLES.set(LIVE_PERMIT_HANDLES.get() + 1);
        return Ok(WritePermit(self));
      }
    }

    Err(())
  }
}



impl core::ops::Deref for SharedMappingHandle {
  type Target = SharedMapping;
  fn deref(&self) -> &Self::Target {
    unsafe {&*self.0.as_ptr()}
  }
}

impl core::ops::Drop for SharedMappingHandle {
  fn drop(&mut self) {
    if 1 != self.count.fetch_sub(1, core::sync::atomic::Ordering::Release){
      return;
    };

    let allocated = self.flags.load(core::sync::atomic::Ordering::Acquire) & SharedMappingFlags::HeapAlocated as u64 != 0;

    unsafe { core::ptr::drop_in_place(self.0.as_mut()) }

    if allocated {
      unsafe { alloc::alloc::dealloc(self.0.as_ptr() as *mut u8, core::alloc::Layout::new::<SharedMapping>()) }
    }
  }
}

impl SharedMapping {
  /// This function will allocate a new SharedMapping returning back a reference counted handle
  pub fn new()->SharedMappingHandle {
    unsafe {
      let ptr = alloc::alloc::alloc(alloc::alloc::Layout::new::<MaybeUninit<SharedMapping>>()) as *mut MaybeUninit<SharedMapping>;
      SharedMapping::init(&mut *ptr, SharedMappingFlags::HeapAlocated as u64);
      SharedMappingHandle(core::ptr::NonNull::new(ptr as *mut SharedMapping).unwrap())
    }
  }
  /// This is unsafe because this could be done inside a stack frame, whick makes safety guarantees more difficult.
  /// This has been made public for use in initializing a static.
  pub unsafe fn init(uninit : &mut MaybeUninit<SharedMapping>, init_flags: u64)-> SharedMappingHandle {
    let inner = uninit.as_mut_ptr();
    unsafe {
      (*inner).count = AtomicU64::new(1);
      (*inner).flags = AtomicU64::new(init_flags);

      for each in 0..=MAX_THREAD_INDEX {
        (&raw mut (*inner).permissions[each]).write(AlignCache(ThreadPermission::init(each as u8)));
        (&raw mut (*inner).to_symbol[each]).write(AlignCache(std::sync::RwLock::new(BytesTrieMap::new())));
        (&raw mut (*inner).to_bytes[each]).write(AlignCache(std::sync::RwLock::new(BytesTrieMap::new())));
      }
      SharedMappingHandle( core::ptr::NonNull::new_unchecked(uninit.assume_init_mut() as *mut SharedMapping) )
    }
  }
  
  /// This function is not inherently unsafe, but should only be used as a last resort when
  /// the lifetime of references to the backing symbol table must linger.
  pub unsafe fn keep_slabs_alive(&self) {
    self.flags.store(SharedMappingFlags::KeepSlabsAlive as u64, core::sync::atomic::Ordering::Release);
  }
  pub fn get_sym(&self, bytes : &[u8]) -> Option<Symbol> {

    let hash = bounded_pearson_hash::<PEARSON_BOUND>(bytes);
    let trie_lock = &self.to_symbol[hash as usize % MAX_THREAD_INDEX].0;

    '_lock_scope:{
      let lock_guard = trie_lock.read().unwrap();
      lock_guard.get(bytes).copied()
    }    
  }
}

impl core::ops::Drop for SharedMapping {
  fn drop(&mut self) {

    if self.flags.load(core::sync::atomic::Ordering::Acquire) & SharedMappingFlags::KeepSlabsAlive as u64 != 0 {
      // leak the Slabs, but free the maps
      return;
    }

    for each in &self.permissions[..] {
      let slab = each.0.symbol_table_start.load(core::sync::atomic::Ordering::Relaxed);
      unsafe {Slab::free(slab)};
    } 
  }
}


/// [`ThinBytes`] is a private type that will be used to point to symbols in the symbol store. the first byte it points to is descibes the length.
/// if top bit set, the lenght is the bitwise not of that byte.
/// if the top is not set, read that byte and the next three as a u32 and use that as the length.
#[derive(Clone, Copy)]
struct ThinBytes(*const u8);

impl ThinBytes {
  fn as_raw_slice(self) -> *const [u8] {
    unsafe {
      let tag = *self.0;

      let (ptr, len) = if (1<<u8::BITS-1) & tag == 0 {
        (self.0.byte_add(1),(!tag) as usize)
      } else {
        (self.0.byte_add(U64_BYTES), (self.0 as *const u64).read_unaligned() as usize)
      };

      core::slice::from_raw_parts(ptr, len)
    }
  }
}

struct ThreadPermission{
  // flags : AtomicU64,
  /// [`std::thread::ThreadId`] holds an [`std::num::NonZeroU64`]. this Atomic represents an `Option<std::num::NonZeroU64>` where `Option::None == 0`
  thread_id : AtomicU64, 
  /// the leading byte represents the "thread number"
  /// the rest represents the symbol count
  next_symbol : AtomicU64,
  /// this value should be null if a symbol table is not initialized
  symbol_table_start   : std::sync::atomic::AtomicPtr<Slab>,
  /// this value should be null if a symbol table is not initialized
  symbol_table_last : std::sync::atomic::AtomicPtr<Slab>,
}


impl ThreadPermission {
  fn init(index : u8) -> ThreadPermission {
    core::debug_assert!(index < 0b_1000_0000, "The top bit of a symbol must be kept off.");
    ThreadPermission {
      thread_id: AtomicU64::new(0),
      next_symbol: AtomicU64::new(if index == 0 {1 /* We want to leave the 0 case clear, as that represents the De Bruijn variable introduction */} else {(index as u64) << (u64::BITS/8 - 1)} ),
      symbol_table_start: AtomicPtr::new(core::ptr::null_mut()),
      symbol_table_last: AtomicPtr::new(core::ptr::null_mut()),
    }

  }
}

#[derive(Clone, Copy /* Slab is just a header of an allocation, it does not "own" the next pointer */)]
#[repr(C)]
struct Slab {
  next : *mut Slab,
  write_pos : usize,
  slab_len : usize,  
  slab_data : [u8;0]
}
impl Slab {
  unsafe fn allocate(bytes : u64)-> *mut Slab {
    let slab_size = (bytes as usize).max(4098);
    let layout = alloc::alloc::Layout::array::<core::cell::UnsafeCell<u8>>(slab_size).unwrap().align_to(4098).unwrap();
    let allocation = alloc::alloc::alloc(layout);

    let out = allocation as *mut Slab;
    *out = Slab {
      next : core::ptr::null_mut(),
      write_pos : 0,
      slab_len : slab_size - core::mem::size_of::<Slab>(),
      slab_data : []
    };
    out
  }
  unsafe fn free(mut slab : *mut Self) {
    while !slab.is_null() {
      let size = core::mem::size_of::<Slab>() + (*slab).slab_len;

      let cur = slab;
      slab = (*slab).next;

      alloc::alloc::dealloc(cur as *mut u8, alloc::alloc::Layout::array::<u8>(size).unwrap());
    }
  }

  fn register_bytes(&mut self, bytes : &[u8]) -> ThinBytes {
    let len = bytes.len();
    core::debug_assert!(len < i64::MAX as usize);

    unsafe {
      if len + U64_BYTES > self.slab_len - self.write_pos {
        let next = Slab::allocate((len + U64_BYTES) as u64);
        self.next = next;
      }
      let head = &raw mut self.slab_data as *mut u8;

      let data_ptr = if len < i8::MAX as usize {
        head.write(!(len as u8));
        head.byte_add(1)
      } else { 
        (head as *mut u64).write_unaligned(len as u64);
        head.byte_add(U64_BYTES)
      };
      core::ptr::copy_nonoverlapping(bytes.as_ptr(), data_ptr, bytes.len());

      ThinBytes(head) 
    }
  }
}