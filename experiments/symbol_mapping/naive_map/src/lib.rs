use std::sync::Arc;
use pathmap::PathMap;

type Symbol = i64;

pub struct SharedMapping {
  next_sym   : core::sync::atomic::AtomicI64,
  to_symbols : std::sync::RwLock<PathMap<Symbol>>,
  to_bytes   : std::sync::RwLock<PathMap<Vec<u8>>>
}


impl SharedMapping {
  pub fn new()-> SharedMappingHandle {
    SharedMappingHandle(Arc::new(SharedMapping{
      next_sym : core::sync::atomic::AtomicI64::new(1),
      to_symbols: std::sync::RwLock::new(PathMap::new()), 
      to_bytes: std::sync::RwLock::new(PathMap::new()) }))
  }

  pub fn get_bytes(&self, sym : Symbol) -> Option<&[u8]> {
    '_lock_scope : {
      let lock = self.to_bytes.read().unwrap();
      lock.get(&sym.to_ne_bytes()).map(|v|unsafe {core::mem::transmute(&v[..])})
    }
  }

  pub fn get_sym(&self, bytes : &[u8]) -> Option<Symbol> {
    '_lock_scope : {
      let lock = self.to_symbols.read().unwrap();
      lock.get(bytes).copied()
    }
  }
}

pub struct SharedMappingHandle(Arc<SharedMapping>);
impl SharedMappingHandle {
    pub fn try_aquire_permission<'a>(&'a self)->Result<WritePermit<'a>, ()> {
      Ok(WritePermit(self))
    }
}

impl Clone for SharedMappingHandle {
    fn clone(&self) -> Self {
      Self(self.0.clone())
    }
}

pub struct WritePermit<'a>(&'a SharedMappingHandle);

impl<'a> WritePermit<'a> {
  pub fn get_sym_or_insert(&self, bytes : &[u8])->Symbol {
    '_lock_scope_sym : {
      let mut lock_sym = self.to_symbols.write().unwrap();
      if let Some(sym) = lock_sym.get(bytes) {
        return *sym;
      }

      let store = Vec::from(bytes);
      let sym = self.next_sym.fetch_add(1, core::sync::atomic::Ordering::Relaxed);
      '_lock_scope_bytes : {
        let mut lock_bytes = self.to_bytes.write().unwrap();
        lock_bytes.insert(sym.to_ne_bytes(), store);
        
        lock_sym.insert(bytes, sym);
        sym
      }
    }
  }
}

impl<'a> core::ops::Deref for WritePermit<'a> {
  type Target = SharedMapping;
  fn deref(&self) -> &Self::Target {
    &self.0.0
  }
}

impl core::ops::Deref for SharedMappingHandle {
  type Target = SharedMapping;
  fn deref(&self) -> &Self::Target {
    &self.0
  }
}

#[cfg(test)]
mod test;