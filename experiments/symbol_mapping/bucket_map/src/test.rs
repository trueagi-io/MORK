use crate::*;

#[test]
fn simple_example() {
  let handle = SharedMapping::new();
  
  core::assert_eq!(handle.get_sym(b"abc"), None);
  // core::assert_eq!(handle.get_bytes(5), None);
  core::assert_eq!(handle.get_bytes(5_i64.to_be_bytes()), None);

  let permit = handle.try_aquire_permission().unwrap();

  let sym = permit.get_sym_or_insert(b"abc");
  drop(permit);
  core::assert_eq!(Some(sym), handle.get_sym(b"abc"));
  core::assert_eq!(Some(&b"abc"[..]), handle.get_bytes(sym));

  drop(handle);
}


#[test]
fn multiple_values() {
  let handle = SharedMapping::new();
  
  core::assert_eq!(handle.get_sym(b"abc"), None);
  // core::assert_eq!(handle.get_bytes(5), None);
  core::assert_eq!(handle.get_bytes(5i64.to_be_bytes()), None);

  let permit = handle.try_aquire_permission().unwrap();

  let bytes =[b"abc", b"def", b"foo", b"bar"];
  let sym = bytes.map(|bs| permit.get_sym_or_insert(bs));

  drop(permit);
  
  for (idx, each) in sym.iter().enumerate() {
    core::assert_eq!(
      Some(*each), 
      handle.get_sym(&bytes[idx][..]));
    core::assert_eq!(
      Some(&bytes[idx][..]), 
      handle.get_bytes(*each)
    );

  }

  drop(handle);
}

#[test]
fn many_values() {
  let handle = SharedMapping::new();
  
  core::assert_eq!(handle.get_sym(b"abc"), None);
  core::assert_eq!(handle.get_bytes(5_i64.to_be_bytes()), None);

  let permit = handle.try_aquire_permission().unwrap();

  let bytes : &[&[u8]]=&[&b"abc"[..], &b"def"[..], &b"foo"[..], &b"bar"[..],
  
  
  &b"first_name"[..], &b"John"[..],
  &b"last_name"[..], &b"Smith"[..],
  &b"is_alive"[..], &b"true"[..],
  &b"age"[..], &b"27"[..],
  &b"address&b"[..],
    &b"street_address"[..], &b"21 2nd Street"[..],
    &b"city"[..], &b"New York"[..],
    &b"state"[..], &b"NY"[..],
    &b"postal_code"[..], &b"10021-3100"[..],
  &b"phone_numbers"[..],
    &b"type"[..], &b"home"[..], &b"number"[..], &b"212 555-1234"[..],
    &b"type"[..], &b"office"[..], &b"number"[..], &b"646 555-4567"[..],
    &b"children"[..], &b"Catherine"[..], &b"Thomas"[..], &b"Trevor"[..],
    &b"spouse"[..], &b"null"[..]
  
  
  ];
  let sym = bytes.iter().copied().map(|bs| permit.get_sym_or_insert(bs)).collect::<Vec<_>>();

  drop(permit);
  
  for (idx, each) in sym.into_iter().enumerate() {
    core::assert_eq!(
      Some(each), 
      handle.get_sym(&bytes[idx][..]));
    core::assert_eq!(
      Some(&bytes[idx][..]), 
      handle.get_bytes(each)
    );
  }

  drop(handle);
}



#[test]
fn same_sym() {
  let handle = SharedMapping::new();
  static READY : core::sync::atomic::AtomicU8 = core::sync::atomic::AtomicU8::new(0);
  static RACE : core::sync::atomic::AtomicBool = core::sync::atomic::AtomicBool::new(false);

  const BYTES : &[&[u8;3]] = [b"abc", b"def", b"efg", b"hij"].as_slice();

  /// this ammount makes it tractable to test with miri
  const WRITER_THREADS : u8 = 16;

  for bytes in BYTES {
    READY.store(0, core::sync::atomic::Ordering::Release);
    RACE.store(false, core::sync::atomic::Ordering::Release);

    let mut threads = Vec::new();
    for _ in 0..WRITER_THREADS {
      let handle_ = handle.clone();
      threads.push(std::thread::spawn(move || {
        let write_permit = handle_.try_aquire_permission().unwrap();

        READY.fetch_add(1, core::sync::atomic::Ordering::Release);
        while !RACE.load(core::sync::atomic::Ordering::Relaxed) {}

        write_permit.get_sym_or_insert(&bytes[..])
      }));
    }

    while WRITER_THREADS != READY.load(core::sync::atomic::Ordering::Acquire) {}
    RACE.store(true, core::sync::atomic::Ordering::Release);

    let mut in_par = threads.into_iter().map(|t|t.join());

    let first = in_par.next().unwrap().unwrap();
    for each in in_par {
      core::assert_eq!(first, each.unwrap());
    }
  }
}

#[test]
fn same_sym2() {
  let handle = SharedMapping::new();
  const BYTES : &[&[u8;3]] = [b"abc", b"def", b"efg", b"hij"].as_slice();

  const WRITER_THREADS : u8 = 16;

  let mut thread_join_handles = Vec::new();

  for thread_id in 0..WRITER_THREADS {
    let handle_ = handle.clone();
    thread_join_handles.push(std::thread::spawn(move || {
      let mut keys = Vec::with_capacity(BYTES.len());
      {
        let write_permit = handle_.try_aquire_permission().unwrap();
        std::thread::sleep(core::time::Duration::from_millis(50));
        for idx in 0..BYTES.len() {
          let sym = if thread_id % 2 == 0 {
            &BYTES[idx]
          } else {
            &BYTES[BYTES.len()-idx-1]
          };
          let key = write_permit.get_sym_or_insert(&sym[..]);
          keys.push(key);
          std::thread::sleep(core::time::Duration::from_millis(50));
        }
      }

      for (idx, key) in keys.iter().enumerate() {
        let sym = handle_.get_bytes(*key).unwrap();
        core::assert_eq!(sym, BYTES[idx]);
      }
    }));
  }

  thread_join_handles.into_iter().for_each(|t| t.join().unwrap())
}

#[test]
fn allocate_many() {
  // const LEN : usize = 3843;   // all dense nodes break point
  // const LEN : usize = 5449;      // breaking point with all dense nodes off
  // const LEN : usize = 4096*32; // original test
  const LEN : usize = 4096*2; 
  // const LEN : usize = 132; 
  static ONES : [u8 ; LEN]= [1;LEN];


  let handle = SharedMapping::new();

  let writer = handle.try_aquire_permission().unwrap();

  // for each in 3842..LEN {  // all dense nodes break point
  // for each in LEN-5441..LEN { // breaking point with all dense nodes off
  for each in 0..LEN {     // original test
    // println!("LEN : {each}");
    writer.get_sym_or_insert(&ONES[0..each]);
  }

  // let path = std::path::PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap()).join(".tmp").join("allocate_many.zip");
  // println!("{:?}", handle.to_bytes[0].0.read().unwrap().val_count());
  // handle.serialize(&path).unwrap();
  // let load = SharedMapping::deserialize(&path).unwrap();
  // println!("{:?}", load.to_bytes[0].0.read().unwrap().val_count());
  // std::fs::remove_file(path).unwrap(); 

}