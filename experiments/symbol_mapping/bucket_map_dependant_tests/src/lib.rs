#[cfg(test)]
mod tests {
  use std::{collections::BTreeMap, fs::create_dir_all, io::Read, path::PathBuf};
  use pathmap::trie_map::BytesTrieMap;
  use bucket_map::{SharedMappingHandle, SharedMapping};

  #[test]
  fn logic_query_small() {
    let workspace_root = std::env::var("CARGO_WORKSPACE_DIR").unwrap();
    let mut small_metta = std::fs::File::open(PathBuf::from(workspace_root).join("benchmarks/logic-query/resources/small.metta")).unwrap();
    let mut s = String::new();
    
    small_metta.read_to_string(&mut s).unwrap();

    let mut space : mork::space::Space = mork::space::Space::new();
    space.load_sexpr(s.as_bytes()).unwrap();
    let sm : SharedMappingHandle = space.sm.clone();

    let zip_file = "logic_query_small.zip";

    serialize_derserialize_cmp(sm, zip_file);
  }
  #[test]
  fn logic_query_big() {
    let workspace_root = std::env::var("CARGO_WORKSPACE_DIR").unwrap();
    let mut small_metta = std::fs::File::open(PathBuf::from(workspace_root).join("benchmarks/logic-query/resources/big.metta")).unwrap();
    let mut s = String::new();
    
    small_metta.read_to_string(&mut s).unwrap();

    let mut space : mork::space::Space = mork::space::Space::new();
    space.load_sexpr(s.as_bytes()).unwrap();
    let sm : SharedMappingHandle = space.sm.clone();

    let zip_file = "logic_query_small.zip";

    serialize_derserialize_cmp(sm, zip_file).unwrap();
  }

  fn serialize_derserialize_cmp(sm : SharedMappingHandle, zip_file_name : impl AsRef<std::path::Path>) -> Result<(), std::io::Error> {

    let dir_path = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap()).join(".tmp");
    create_dir_all(&dir_path)?;
    let path = dir_path.join(zip_file_name);
    
    sm.serialize(&path)?;

    let load = SharedMapping::deserialize(&path)?;
    unsafe { assert!(cmp_mappings(&sm, &load)) }
    std::fs::remove_file(path)
  }


  // below are helper functions that are not safe outside this test.
  unsafe fn cmp_mappings(left : &SharedMapping, right: &SharedMapping) -> bool{

    unsafe {
      let l = as_btree(left);
      let r = as_btree(right);

      l == r
    }
  }

  unsafe fn as_btree(shared_mapping : &SharedMapping) ->(BTreeMap<Vec<u8>, [u8;8]>, BTreeMap<[u8;8], Vec<u8>>) {
    let mut out = BTreeMap::new();
    let mut out2= BTreeMap::new();
    let bucket_map::serialization::Tables { to_symbol, to_bytes } = shared_mapping.reveal_tables();
    for each in 0..bucket_map::MAX_WRITER_THREADS {
      for (path, value) in to_symbol[each].iter()
      {
        out.insert(path, *value);
      }
      for (value, path) in to_bytes[each].iter()
      {
        core::assert!(value.len() == bucket_map::SYM_LEN);
        out2.insert(unsafe {*(value.as_ptr() as *const [u8;bucket_map::SYM_LEN])}, unsafe {(&*path.as_raw()).to_owned()}, );
      }
    }
    
    (out, out2)
  }
}
