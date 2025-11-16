use std::{io::{Read, Write}, path::Path};
use pathmap::{morphisms::Catamorphism, PathMap};
use zip::ZipArchive;
use crate::{bounded_pearson_hash, SharedMapping, SharedMappingHandle, Slab, Symbol, ThinBytes, MAX_WRITER_THREADS, SYMBOL_THREAD_PERMIT_BYTE_POS, SYM_LEN};

macro_rules! file_sizes_meta_filename {() => { "FileSizes.meta" }; }
const FILE_SIZES_META_FILENAME : &'static str = file_sizes_meta_filename!();
impl SharedMapping {
  /// Serialize the [`SharedMapping`] to a file. it must be deserialized using [`SharedMapping::deserialize`].
  /// The file at the out path will be overwritten.
  pub fn serialize(&self, out_path : impl AsRef<Path>)->Result<(),std::io::Error> {
    // we need to read-lock the all the maps
    let mut locks = Vec::new();
    for each in self.to_bytes.iter() {
      let lock = each.0.read().unwrap();
      locks.push(lock);
    }

    let out_file = std::fs::File::create(&std::path::Path::new(out_path.as_ref()))?;
    let mut buffer = zip::ZipWriter::new(out_file);
    
    let mut metadata = Vec::new();
    
    for (n, lock) in  locks.iter().enumerate() {
      core::debug_assert!(n<256);
      
      buffer.start_file::<String,_>(format!("SharedMapping_0x{:0>2X}.binary_data", n as u8), zip::write::FileOptions::<()>::default().large_file(true))?;

      let reader = lock.read_zipper();

      let mut count = 0;

      reader.into_cata_jumping_side_effect::<Result<(), std::io::Error>,_>(|_,_,_,v,o|{
        if let Some(ptr) = v {
          core::debug_assert_eq!(o.len(), SYM_LEN);
          let sym = unsafe { &*ptr.as_raw_slice() };

          let sym_len = sym.len();

          // the top two bytes of sym is intentionaly left as zeroes
          count += buffer.write(&o[2..])?;

          count += if sym_len <= i8::MAX as usize{
            buffer.write(&[!(sym_len as u8)])?
          } else {
            buffer.write(&(sym_len as u64).to_be_bytes())?
          };

          count += buffer.write(sym)?;
        };
        Ok(())
      })?;

      if count == 0 {
        buffer.abort_file()?;
        continue;
      }
      metadata.extend_from_slice(&(n as u64).to_be_bytes());
      metadata.extend_from_slice(&(count as u64).to_be_bytes());
    }

    buffer.start_file::<&str,_>(FILE_SIZES_META_FILENAME, zip::write::FileOptions::<()>::default())?;
    buffer.write_all(&metadata)?;

    buffer.finish()?.flush()?;

    Ok(())
  }

  /// Deserialize the [`SharedMapping`] from a file made by [`SharedMapping::serialize`].
  pub fn deserialize(in_path : impl AsRef<Path>) -> Result<SharedMappingHandle, std::io::Error> {
    let shared_mapping = SharedMapping::new();
    let mapping_ptr = shared_mapping.0.as_ptr();

    macro_rules! HEX {() => { (b'0'..=b'9'|b'A'..=b'F') };}
        
    let mut to_symbol = [(); MAX_WRITER_THREADS].map(|()|PathMap::<Symbol>::new());
    let mut to_bytes  = [(); MAX_WRITER_THREADS].map(|()|PathMap::<ThinBytes>::new());

    let file = std::fs::File::open(in_path.as_ref())?;
    let mut zip_archive = ZipArchive::new(file).map_err(|_|std::io::Error::other("failed to read zip archive"))?;
    let files = zip_archive.file_names().map(|s|s.to_owned()).collect::<Vec<_>>();
    
    fn hex_to_byte(&h : &u8)->u8 {
      match h {
        b'0'..=b'9' => h - b'0',
        b'A'..=b'F' => h - b'A' + 10,
        _ => core::unreachable!(),
      }
    }

    let mut file_sizes = [0_usize; MAX_WRITER_THREADS];
    let mut meta = Vec::new();
    zip_archive.by_name(FILE_SIZES_META_FILENAME)?.read_to_end(&mut meta)?;
    let mut meta_slice = &meta[..];
    if meta_slice.len() as u32 % (2*u64::BITS/u8::BITS) != 0 { return Err(std::io::Error::other("Malformed metadata file"));  }

    loop  {
      let Some((head, tail)) = meta_slice.split_at_checked((2*u64::BITS/u8::BITS) as usize) else {break;};
      let (idx, size) = head.split_at((u64::BITS/u8::BITS) as usize);
      unsafe {file_sizes[u64::from_be_bytes(*(idx.as_ptr() as *const [u8;8])) as usize] = u64::from_be_bytes(*(size.as_ptr() as *const [u8;8])) as usize}

      meta_slice = tail;
    }

    for file_name in files {
      if file_name.as_str() == FILE_SIZES_META_FILENAME { continue; }
        
      let file_name_bytes = file_name.as_bytes();
      
      const LEADING   : &[u8] = b"SharedMapping_0x";
      const EXTENSION : &[u8] = b".binary_data";
      
      let match_error = || Err(std::io::Error::other("Malformed filename, expected `SharedMapping_0x[0-9A-F]{2}\\.binary_data`"));
      let [top @ HEX!(), bot @ HEX!(), rest @ .. ] = &file_name_bytes[LEADING.len() ..] else { return match_error();};
      if &file_name_bytes[ .. LEADING.len() ] != LEADING
      || rest != EXTENSION
      {
        return match_error();
      }
      
      
      
      const HEX_BITS : u32 = 4;
      let index = (hex_to_byte(top) << HEX_BITS | hex_to_byte(bot)) as usize;
      let mut zip_file = zip_archive.by_name(&file_name).map_err(|_| std::io::Error::other("File failed to be extracted from zip"))?;
      let slab_size =file_sizes[index] ;
      
      unsafe {
        let slab_ptr = Slab::allocate(slab_size as u64);
        (*mapping_ptr).permissions[index].0.symbol_table_start.store(slab_ptr, core::sync::atomic::Ordering::Relaxed);
        (*mapping_ptr).permissions[index].0.symbol_table_last.store(slab_ptr, core::sync::atomic::Ordering::Relaxed);
        (*slab_ptr).write_pos = slab_size;
      
        let slab_slice = &mut *core::ptr::slice_from_raw_parts_mut((*slab_ptr).slab_data, (*slab_ptr).slab_len);
      
        // 6 byte symbol padding between the strings will persist, but this should dramatically load speed.
        let mut start = 0;
        while let diff @ 1..=usize::MAX = zip_file.read(&mut slab_slice[start..slab_size])? {
          start += diff;
        }
        
        drop(zip_file);
      
        // at this point we are done with the file. We have to parse the slice inside the slab
      
        let mut to_parse = &*slab_slice;
        let mut max_symbol = 0;
      
        
      
        while let Some((sym_bytes, to_parse_0)) = to_parse.split_at_checked(SYM_LEN-SYMBOL_THREAD_PERMIT_BYTE_POS) {
          let [s0,s1,s2,s3,s4,s5] = (sym_bytes.as_ptr() as *const [u8;SYM_LEN-SYMBOL_THREAD_PERMIT_BYTE_POS]).read();
          let sym : Symbol = [0,0,s0,s1,s2,s3,s4,s5];
          if u64::from_be_bytes(sym) == 0 {
            break
          }
      
          let leading_byte = to_parse_0[0];
      
          // read out the length
          let (length, to_parse_2) = if (leading_byte as i8).is_negative()
          { let Some((_, to_parse_1)) = to_parse_0.split_at_checked(1) else { return Err(std::io::Error::other(concat!("Malformed data, expected length byte, file : ", file!(), ", line : ", line!() ))); };
            ((!leading_byte) as usize, to_parse_1)
          } else {
            let Some((len_bytes, to_parse_1)) = to_parse_0.split_at_checked(8) else { return Err(std::io::Error::other(concat!("Malformed data, expected 8 length bytes, file : ", file!(), ", line : ", line!() )));};
            (u64::from_be_bytes((len_bytes.as_ptr() as *const [u8;8]).read()) as usize, to_parse_1)
          };
      
          max_symbol = max_symbol.max(u64::from_be_bytes(sym));
      

          to_symbol[bounded_pearson_hash::<{crate::PEARSON_BOUND}>(&to_parse[0..length]) as usize % MAX_WRITER_THREADS].insert(&to_parse_2[0..length], sym);         
          to_bytes[index].insert(&sym, ThinBytes(to_parse_0.as_ptr()));
        
          let Some((_, [to_parse_3 @ .. ])) = to_parse_2.split_at_checked(length) else { return Err(std::io::Error::other(concat!("Malformed data, unexpected end', file : ", file!(), ", line : ", line!() ))); };
      
          to_parse = to_parse_3;
        }
      
        (*mapping_ptr).permissions[index].0.next_symbol.store(max_symbol+1, core::sync::atomic::Ordering::Relaxed);
                
                
      
      }
    }

    // finally insert the deserilized data
    for (idx, (to_s, to_b)) in to_symbol.into_iter().zip(to_bytes).enumerate() {
      *shared_mapping.to_symbol[idx].0.write().unwrap() = to_s;
      *shared_mapping.to_bytes[idx].0.write().unwrap() = to_b;
    }


    Ok(shared_mapping)
  }


  /// this is only for debugging
  #[cfg(feature = "debug_api")]
  #[doc(hidden)]
  pub fn reveal_tables<'a>(&'a self) -> Tables<'a> {
    let mut to_bytes = Vec::new();
    for each in self.to_bytes.iter() {
      let lock = each.0.read().unwrap();
      to_bytes.push(lock);
    }
    let mut to_symbol = Vec::new();
    for each in self.to_symbol.iter() {
      let lock = each.0.read().unwrap();
      to_symbol.push(lock);
    }
    Tables { to_symbol, to_bytes }

  }
}

/// this is only for debugging
#[doc(hidden)]
pub struct Tables<'a> {
  pub to_symbol : Vec<std::sync::RwLockReadGuard<'a, PathMap<Symbol>>>,
  pub to_bytes  : Vec<std::sync::RwLockReadGuard<'a, PathMap<ThinBytes>>>
}


#[cfg(test)]
mod test {
  use std::collections::BTreeMap;



use super::*;

  #[test]
  fn serialize_long() {
    const ARR_LEN : usize = 50; 
    const ALPHA_NUM_LEN : usize = 62;
    const LEN : usize = ARR_LEN*ALPHA_NUM_LEN;
    const ALPHA_NUM : [[u8;ALPHA_NUM_LEN]; ARR_LEN] 
    = [*b"abcdefghijklmnopqrstuvwxyz\
       ABCDEFGHIJKLMNOPQRSTUVWXYZ\
       0123456789\
      "; ARR_LEN];
    static FLAT : &[u8 ; LEN]= unsafe {&(*((&ALPHA_NUM).as_ptr() as *const u8 as *const _)) };
    let handle = SharedMapping::new();

    let writer = handle.try_aquire_permission().unwrap();
  
    for each in 0..LEN {
      writer.get_sym_or_insert(&FLAT[0..each]);
    }
  
    let path = std::path::PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap()).join(".tmp").join("serialize_long.zip");
  
    handle.serialize(&path).unwrap();
    let load = SharedMapping::deserialize(&path).unwrap();
    
    core::assert_eq!(
      handle.to_bytes[0].0.read().unwrap().val_count(),
      load.to_bytes[0].0.read().unwrap().val_count()
    );
    load.to_bytes[0].0.read().unwrap().read_zipper().into_cata_side_effect(|_mask,_accs,val : Option<&ThinBytes>,_path|{
      match val {
        Some(id) => core::assert!(unsafe {&(*id.as_raw_slice())[..]}.iter().all(|c| c.is_ascii_alphanumeric())),
        None => (),
      };
    });

    core::assert!(unsafe {cmp_mappings(&handle, &load)});

    std::fs::remove_file(path).unwrap();
  }

  #[test]
  fn trivial_serialize() {

    let path = std::path::PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap()).join(".tmp").join("trivial_serialize.zip");
    
    const ALPHA_NUM : &'static [u8] = b"abcdefghijklmnopqrstuvwxyz\
                                        ABCDEFGHIJKLMNOPQRSTUVWXYZ\
                                        0123456789\
                                        abcdefghijklmnopqrstuvwxyz\
                                        ABCDEFGHIJKLMNOPQRSTUVWXYZ\
                                        0123456789\
                                        abcdefghijklmnopqrstuvwxyz\
                                        ABCDEFGHIJKLMNOPQRSTUVWXYZ\
                                        0123456789\
                                      ";
    
    let mapping = SharedMapping::new();
    static GO : std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);
    let mut handles = Vec::new();
    for each in 0..MAX_WRITER_THREADS {
      let handle = mapping.clone();
      handles.push(std::thread::spawn(move || {
        let handle_   = handle;
        let Ok(write_permit) = handle_.try_aquire_permission() else { return; };
        while !GO.load(std::sync::atomic::Ordering::Relaxed) {}

        let alph_num = &ALPHA_NUM[each..ALPHA_NUM.len()-(MAX_WRITER_THREADS-each)];
        for l in 0..alph_num.len() {
          write_permit.get_sym_or_insert(&alph_num[l..]);
          write_permit.get_sym_or_insert(&alph_num[..l]);
        }
      }));
    }

    GO.store(true, std::sync::atomic::Ordering::Relaxed);


    for h in  handles {
      h.join().unwrap();
    }

    mapping.serialize(&path).unwrap();
    let load = SharedMapping::deserialize(&path).unwrap();
    unsafe {
      assert!(cmp_mappings(&mapping, &load));
    }
    std::fs::remove_file(path).unwrap();

  }
  // below are helper functions that are not safe outside this test.
  unsafe fn cmp_mappings(left : &SharedMapping, right: &SharedMapping) -> bool{

    unsafe {
      let l = as_btree(left);
      let r = as_btree(right);

      l == r
    }
  }
  unsafe fn as_btree(shared_mapping : &SharedMapping) ->(BTreeMap<String, [u8;8]>, BTreeMap<[u8;8], String>) {
    let mut out = BTreeMap::new();
    let mut out2= BTreeMap::new();
    for each in 0..MAX_WRITER_THREADS {
      for (path, value) in shared_mapping.to_symbol[each].0.read().unwrap().iter()
      {
        out.insert(unsafe {core::mem::transmute(path)}, *value);
      }
      for (value, path) in shared_mapping.to_bytes[each].0.read().unwrap().iter()
      {
        core::assert!(value.len() == SYM_LEN);
        out2.insert(unsafe {*(value.as_ptr() as *const [u8;SYM_LEN])}, unsafe {core::mem::transmute((&*path.as_raw_slice()).to_owned())}, );
      }
    }
    
    (out, out2)
  }

}

