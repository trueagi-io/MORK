use std::{alloc::Layout, fs::FileType, io::{BufReader, BufWriter, Read, Write}, ops::Range, os::unix::ffi::OsStrExt, path::Path, u64, usize};
use pathmap::{morphisms::Catamorphism, trie_map::BytesTrieMap};
use zip::ZipArchive;
use crate::{bounded_pearson_hash, AlignCache, SharedMapping, SharedMappingHandle, Slab, Symbol, ThinBytes, ThreadPermission, MAX_WRITER_THREADS, SYM_LEN, U64_BYTES};


impl SharedMapping {
  pub fn serialize(&self, out_dir : impl AsRef<Path>)->Result<(),std::io::Error> {
    // we need to read-lock the all the maps
    let mut locks = Vec::new();
    for each in self.to_bytes.iter() {
      let lock = each.0.read().unwrap();
      locks.push(lock);
    }

    let path = std::path::Path::new(out_dir.as_ref());


    
    let out_file_path = path.join("SharedMapping.zip");
    let out_file = std::fs::File::create_new(&out_file_path)?;
    let mut buffer = zip::ZipWriter::new(out_file);
    
    for (n, lock) in  locks.iter().enumerate() {
      core::debug_assert!(n<256);
      
      // let out_file_path = path.join(format!("SharedMapping_0x{:0>2X}.binary_data", n as u8));

      // let out_file = std::fs::File::create_new(&out_file_path)?;
      // let mut buffer = BufWriter::new(out_file);
      
      buffer.start_file::<String,_>(format!("SharedMapping_0x{:0>2X}.binary_data", n as u8), zip::write::FileOptions::<()>::default().large_file(true))?;

      let reader = lock.read_zipper();

      let mut count = 0;

      reader.into_cata_jumping_side_effect::<Result<(), std::io::Error>,_>(|_,_,_,v,o|{
        if let Some(ptr) = v {
          core::debug_assert_eq!(o.len(), SYM_LEN);
          let sym = unsafe { &*ptr.as_raw_slice() };

          let sym_len = sym.len();

          buffer.write(&o[2..])?;

          if sym_len < i8::MAX as usize {
            buffer.write(&[!(sym_len as u8)])?;
          } else {
            buffer.write(&(sym_len as u64).to_be_bytes())?;
          }

          buffer.write(sym)?;
          // makes the file output mildly more readable
          // buffer.write(b"\n")?;

          count += 1;
        };
        Ok(())
      })?;

      // buffer.flush()?;


      // drop(buffer);

      if count == 0 {
        // while out_file_path.exists() {
        //   let _ = std::fs::remove_file(&out_file_path);
        // }
        buffer.abort_file()?;
      }
    }

    buffer.finish()?.flush()?;

    Ok(())
  }

  pub fn deserialize(in_dir : impl AsRef<Path>) -> Result<SharedMappingHandle, std::io::Error> {
    let path = in_dir.as_ref();

    // dbg!(&path);

    let shared_mapping = SharedMapping::new();
    let mapping_ptr = shared_mapping.0.as_ptr();

    macro_rules! HEX {() => { (b'0'..=b'9'|b'A'..=b'F') };}
        
    let mut to_symbol = [(); MAX_WRITER_THREADS].map(|()|BytesTrieMap::<Symbol>::new());
    let mut to_bytes  = [(); MAX_WRITER_THREADS].map(|()|BytesTrieMap::<ThinBytes>::new());

    let mut zip_file = ZipArchive::new( std::fs::File::open(path.join("SharedMapping.zip"))? ).map_err(|_|std::io::Error::other("failed to read zip archive"))?;

    let files = zip_file.file_names().map(|s|s.to_owned()).collect::<Vec<_>>();

    for file_name in files {
        let file_name_bytes = file_name.as_bytes();
    // }

    // for each in std::fs::read_dir(&path)? {
    //   let entry = each?;
    //   if entry.file_type()?.is_file() {
    //     let file_name = entry.file_name();
    //     let file_name_bytes = file_name.as_bytes();

        const LEADING   : &[u8] = b"SharedMapping_0x";
        const EXTENSION : &[u8] = b".binary_data";

        let match_error = || Err(std::io::Error::other("malformed filename, expected `SharedMapping_0x[0-9A-F]{2}\\.binary_data`"));
        let [top @ HEX!(), bot @ HEX!(), rest @ .. ] = &file_name_bytes[LEADING.len() ..] else { return match_error();};
        if &file_name_bytes[ .. LEADING.len() ] != LEADING
        || rest != EXTENSION
        {
          return match_error();
        }

        let hex_to_byte = |&h| match h {
          b'0'..=b'9' => h - b'0',
          b'A'..=b'F' => h - b'A' + 10,
          _ => core::unreachable!(),
        };

        const HEX_BITS : u32 = 4;
        let index = (hex_to_byte(top) << HEX_BITS | hex_to_byte(bot)) as usize;

        // let mut file = std::fs::File::open(path.join(&file_name))?;
        // let slab_size = file.metadata()?.len() as usize;

        let mut file = zip_file.by_name(&file_name).map_err(|_| std::io::Error::other("File failed to be extracted from zip"))?;
        let slab_size = file.size() as usize;

        unsafe {
          let slab_ptr = Slab::allocate(slab_size as u64);
          (*mapping_ptr).permissions[index].0.symbol_table_start.store(slab_ptr, core::sync::atomic::Ordering::Relaxed);
          (*mapping_ptr).permissions[index].0.symbol_table_last.store(slab_ptr, core::sync::atomic::Ordering::Relaxed);
          (*slab_ptr).write_pos = slab_size;

          let slab_slice = &mut *core::ptr::slice_from_raw_parts_mut((*slab_ptr).slab_data, (*slab_ptr).slab_len);

          let mut start = 0;
          while let diff @ 1..=usize::MAX = file.read(&mut slab_slice[start..slab_size])? {
            start += diff;
          }
          // file.flush()?;
          
          drop(file);

          // at this point we are done with the file. We have to parse the slice inside the slab

          let mut to_parse = &*slab_slice;
          // dbg!(to_parse.into_iter().map(|x| *x as char).collect::<String>());
          let mut max_symbol = 0;

          

          while let Some((sym_bytes, to_parse_0)) = to_parse.split_at_checked(SYM_LEN-2) {
            let [s0,s1,s2,s3,s4,s5] = (sym_bytes.as_ptr() as *const [u8;SYM_LEN-2]).read();
            let sym : Symbol = [0,0,s0,s1,s2,s3,s4,s5];
            // let sym : Symbol = (sym_bytes.as_ptr() as *const [u8;SYM_LEN]).read();
            if u64::from_be_bytes(sym) == 0 {
              break
            }

            let leading_byte = to_parse_0[0];

            // read out the length
            let (length, to_parse_2) = if (leading_byte | (1 << u8::BITS-1)) == 0 {
              let Some((len_bytes, to_parse_1)) = to_parse_0.split_at_checked(8) else { return Err(std::io::Error::other(concat!("Malformed data, expected 8 length bytes, file : ", file!(), ", line : ", line!() )));};
              (u64::from_be_bytes((len_bytes.as_ptr() as *const [u8;8]).read()) as usize, to_parse_1)
            } else {
              let Some((len_byte, to_parse_1)) = to_parse_0.split_at_checked(1) else { return Err(std::io::Error::other(concat!("Malformed data, expected length byte, file : ", file!(), ", line : ", line!() ))); };
              ((!len_byte[0]) as usize, to_parse_1)
            };
            // dbg!((length, to_parse_2.len()));

            max_symbol = max_symbol.max(u64::from_be_bytes(sym));

            to_symbol[bounded_pearson_hash::<{crate::PEARSON_BOUND}>(&to_parse[0..length]) as usize % MAX_WRITER_THREADS].insert(&to_parse_2[0..length], sym);         
            to_bytes[index].insert(sym_bytes, ThinBytes(to_parse_2.as_ptr()));
          
            // let Some((_, [b'\n', to_parse_3 @ .. ])) = to_parse_2.split_at_checked(length) else { return Err(std::io::Error::other(concat!("Malformed data, expected b'\\n', file : ", file!(), ", line : ", line!() ))); };
            let Some((_, [to_parse_3 @ .. ])) = to_parse_2.split_at_checked(length) else { return Err(std::io::Error::other(concat!("Malformed data, unexpected end', file : ", file!(), ", line : ", line!() ))); };

            to_parse = to_parse_3;
          }

          (*mapping_ptr).permissions[index].0.next_symbol.store(max_symbol+1, core::sync::atomic::Ordering::Relaxed);
        // }

      }
    }

    // finally insert the deserilized data
    for (idx, (to_s, to_b)) in to_symbol.into_iter().zip(to_bytes).enumerate() {
      *shared_mapping.to_symbol[idx].0.write().unwrap() = to_s;
      *shared_mapping.to_bytes[idx].0.write().unwrap() = to_b;
    }


    Ok(shared_mapping)
  }
}

#[cfg(test)]
mod test {
  use std::collections::BTreeMap;

use super::*;

  #[test]
  fn trivial_serialize() {
    let path = std::path::PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap()).join(".tmp").join("trivial_serialize");
    let _ = std::fs::remove_dir_all(&path);
    let _ = std::fs::create_dir_all(&path);
    
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
      let mut handle = mapping.clone();
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

    // below are helperfunctions that are not safe outside this test.

    unsafe fn cmp_mappings(left : &SharedMapping, right: &SharedMapping) -> bool{
  
      unsafe {
        let l = as_as_btree(left);
        let r = as_as_btree(right);

        dbg!((&l,&r));
    
        l == r
      }
    }
    unsafe fn as_as_btree(shared_mapping : &SharedMapping) ->BTreeMap<String, [u8;8]> {
      let mut out = BTreeMap::new();
      for each in 0..MAX_WRITER_THREADS {
        for (path, value) in shared_mapping.to_symbol[each].0.read().unwrap().iter()
        {
          out.insert(unsafe {core::mem::transmute(path)}, *value);
        }
      }
      out
    }
  }

}