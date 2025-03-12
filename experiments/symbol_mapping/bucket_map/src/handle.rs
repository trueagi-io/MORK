use crate::*;

/// WritePermit is a form of soft guard, the lifetime encourages scoped usage.
pub struct WritePermit<'a>(&'a SharedMappingHandle, PhantomData<*const (/* we do not want this to be Send or Sync */)>);

impl<'a> core::ops::Drop for WritePermit<'a> {
  fn drop(&mut self) {
    let permits = LIVE_PERMIT_HANDLES.get()-1;
    LIVE_PERMIT_HANDLES.set(permits);
    
    if permits == 0 {
      self.permissions[MAPPING_THREAD_INDEX.get().unwrap() as usize].0.thread_id.store(0, atomic::Ordering::Release);
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
  pub fn get_sym_or_insert(&self, bytes : &[u8]) -> Symbol {
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
    let mut eager_and_recovery : Option<(ThinBytes, (*mut Slab, Slab))> = None;

    let mut slab_ptr = thread_permission.symbol_table_last.load(atomic::Ordering::Relaxed);

    if !thread_permission.symbol_table_start.load(atomic::Ordering::Relaxed).is_null() {      
      unsafe {  
        if (*slab_ptr).slab_len-(*slab_ptr).write_pos >= bytes.len() + U64_BYTES {
          let recovery = (slab_ptr, *slab_ptr);
          eager_and_recovery = Some((Slab::register_bytes(slab_ptr,bytes) ,recovery));
        }
      }
    }

    let hash = bounded_pearson_hash::<PEARSON_BOUND>(bytes);

    // as minimal as it might be, we want the critical section as small as posible, so we index first
    let sym_table_lock = &self.to_symbol[hash as usize % MAX_WRITER_THREADS].0;
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
        eager_and_recovery = None;
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
          Slab::register_bytes(slab_ptr,bytes)
        }
      };
      let new_sym = thread_permission.next_symbol.fetch_add(1, atomic::Ordering::Relaxed).to_be_bytes();
      
      let old_sym = sym_guard.insert(bytes, new_sym);
      core::debug_assert!(matches!(old_sym, Option::None));

      let sym_bytes = new_sym;
      '_lock_scope_bytes : {
        let mut bytes_guard = bytes_guard_lock.write().unwrap();

        let old_thin = bytes_guard.insert(sym_bytes.as_slice(), thin_bytes_ptr);
        core::debug_assert!(matches!(old_thin, Option::None));
        }

      new_sym
    };

    // similarly to entering the critical section, we do cleanup after, even though normally we would prefer to do it as locally as possible
    if !slab_ptr.is_null() {
      let next = unsafe {(*slab_ptr).next};
      if !next.is_null() {
        thread_permission.symbol_table_last.store(next, atomic::Ordering::Release);
      }
    }

    if let Some((_,(recovery_ptr, recovery_data))) = eager_and_recovery {
      // if we ever reach this point the ponter never changed, but we need to revert the `Slab` header
      unsafe {*recovery_ptr = recovery_data;}
    }

    sym
  }
}
 
thread_local! {
  static MAPPING_THREAD_INDEX : core::cell::Cell<Option<u8>> = core::cell::Cell::new(None);
  static THREAD_ID : u64 = unsafe {core::mem::transmute::<_,u64> (std::thread::current().id()) };
  static LIVE_PERMIT_HANDLES : core::cell::Cell<usize> = core::cell::Cell::new(0)
}



pub struct SharedMappingHandle(pub(crate) core::ptr::NonNull<SharedMapping>);
unsafe impl Send for SharedMappingHandle {}
unsafe impl Sync for SharedMappingHandle {}

impl SharedMappingHandle {


  /// Falure of this method marks a that all permissions were tried and it failed to aquire any.
  /// Failure can be spurious if there are a high number of threads (> [`MAX_THREADS`]), it is recommended to 
  /// retry even if there are many threads as this only competes with writer threads.
  pub fn try_aquire_permission<'a>(&'a self)->Result<WritePermit<'a>, ()> {
    // A thred can only have one permission at a time
    if let Some(_) = MAPPING_THREAD_INDEX.get() {
      LIVE_PERMIT_HANDLES.set(LIVE_PERMIT_HANDLES.get() + 1);
      return Ok(WritePermit(self, PhantomData));
    }

    for each in 0..MAX_WRITER_THREADS {
      let p = &self.permissions[each];
      if let Ok(_) = p.0.thread_id.compare_exchange(0, THREAD_ID.with(|x|*x)+1, atomic::Ordering::Acquire, atomic::Ordering::Relaxed) {
        MAPPING_THREAD_INDEX.set(Some(each as u8));
        LIVE_PERMIT_HANDLES.set(LIVE_PERMIT_HANDLES.get() + 1);
        return Ok(WritePermit(self, PhantomData));
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

impl Clone for SharedMappingHandle {
    fn clone(&self) -> Self {
      self.count.fetch_add(1, atomic::Ordering::Relaxed);
      Self(self.0.clone())
    }
}

impl core::ops::Drop for SharedMappingHandle {
  fn drop(&mut self) {
    if 1 != self.count.fetch_sub(1, atomic::Ordering::Release){
      return;
    };

    let allocated = self.flags.load(atomic::Ordering::Acquire) & SharedMappingFlags::HeapAllocated as u64 != 0;

    unsafe { core::ptr::drop_in_place(self.0.as_mut()) }

    if allocated {
      unsafe { alloc::alloc::dealloc(self.0.as_ptr() as *mut u8, core::alloc::Layout::new::<SharedMapping>()) }
    }
  }
}
