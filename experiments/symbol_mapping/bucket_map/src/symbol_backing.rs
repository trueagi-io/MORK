use crate::*;
  
#[derive(Clone, Copy /* Slab is just a header of an allocation, it does not "own" the next pointer */)]
#[repr(C)]
pub(crate) struct Slab {
  pub(crate) next : *mut Slab,
  pub(crate) write_pos : usize,
  pub(crate) slab_len : usize,  
  pub(crate) slab_data : *mut u8,
}

impl Slab {
  pub(crate) unsafe fn allocate(bytes : u64)-> *mut Slab {
    let slab_size = (bytes as usize + core::mem::size_of::<Slab>()).max(4096);
    let layout = alloc::alloc::Layout::array::<core::cell::UnsafeCell<u8>>(slab_size).unwrap().align_to(4096).expect("Cannot be aligned");
    // for serialization we want the tail to be zeroed so that it compresses well
    let allocation = alloc::alloc::alloc_zeroed(layout);
    
    let out = allocation as *mut Slab;
    *out = Slab {
      next : core::ptr::null_mut(),
      write_pos : 0,
      slab_len : slab_size - core::mem::size_of::<Slab>(),
      slab_data : allocation.add(core::mem::size_of::<Slab>())
    };
    out
  }
  pub(crate) fn total_slab_size(&self) -> usize {
    self.slab_len + core::mem::size_of::<Slab>()
  }
  
  pub(crate) unsafe fn free(mut slab : *mut Self) {
    while !slab.is_null() {
      let size = core::mem::size_of::<Slab>() + (*slab).slab_len;
    
      let cur = slab;
      slab = (*slab).next;
    
      alloc::alloc::dealloc(cur as *mut u8, alloc::alloc::Layout::array::<u8>(size).unwrap().align_to(4096).unwrap());
    }
  }
  
  pub(crate) unsafe fn register_bytes(mut _self : *mut Self, bytes : &[u8]) -> ThinBytes {
    let len = bytes.len();
    core::debug_assert!(len < i64::MAX as usize);

    let mut slab = unsafe {*_self};
    unsafe {
      if len + U64_BYTES > slab.slab_len - slab.write_pos {
        let next = Slab::allocate((len + U64_BYTES) as u64);
        (*_self).next = next;
        _self = next;
        slab = *next;
      }
      let head = (*_self).slab_data.add(slab.write_pos);

      let offset = if len < i8::MAX as usize {
        head.write(!(len as u8));
        1
      } else { 
        // new version for serialization
        (head as *mut [u8;8]).write((len as u64).to_be_bytes());

        // // old version
        // (head as *mut u64).write_unaligned(len as u64);

        U64_BYTES
      };
      let data_ptr = head.byte_add(offset);
      (*_self).write_pos += offset + len;

      core::ptr::copy_nonoverlapping(bytes.as_ptr(), data_ptr, bytes.len());
    
      ThinBytes(head) 
    }
  }
}



/// [`ThinBytes`] is a private type that will be used to point to symbols in the symbol store. the first byte it points to is descibes the length.
/// if top bit set, the length is the bitwise not of that byte.
/// if the top is not set, read that byte and the next three as a u32 and use that as the length.
#[derive(Clone, Copy)]
pub struct ThinBytes(pub(crate) *const u8);

impl ThinBytes {
  pub(crate) fn as_raw_slice(self) -> *const [u8] {
    unsafe {
      let tag = *self.0;

      let (ptr, len) = if ((1<<u8::BITS-1) & tag) != 0 {
        (self.0.byte_add(1),(!tag) as usize)
      } else {
        // new version for serialization
        (self.0.byte_add(U64_BYTES), u64::from_be_bytes(*(self.0 as *const [u8;U64_BYTES])) as usize)

        // // old version
        // (self.0.byte_add(U64_BYTES), (self.0 as *const u64).read_unaligned() as usize)
      };

      core::slice::from_raw_parts(ptr, len)
    }
  }

  /// this is only for debugging
  #[doc(hidden)]
  pub unsafe fn as_raw(self)->*const [u8] {
    self.as_raw_slice()
  }
}

unsafe impl Send for ThinBytes {}
unsafe impl Sync for ThinBytes {}