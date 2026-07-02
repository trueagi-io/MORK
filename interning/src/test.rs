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

  const WRITER_THREADS: u64 = 16;

  let mut thread_join_handles = Vec::new();

  for _thread_idx in 0..WRITER_THREADS {
    let handle_ = handle.clone();
    thread_join_handles.push(std::thread::spawn(move || {
      //NOTE - Uncomment this line, which forces the threads to run one-at-a-time, and the test passes
      // std::thread::sleep(core::time::Duration::from_millis(100 * _thread_idx));

      let mut keys = Vec::with_capacity(BYTES.len());
      {
        let write_permit = handle_.try_aquire_permission().unwrap();
        for idx in 0..BYTES.len() {
          let sym = &BYTES[idx];
          let key = write_permit.get_sym_or_insert(&sym[..]);
          keys.push(key);
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

#[test]
fn permits_are_scoped_per_mapping() {
  // Same thread, two mappings, nested permits: each mapping must get its OWN
  // registered slot, and a release must never touch the other mapping. The old
  // single cached slot skipped registration on the second mapping entirely and
  // the last drop zeroed a slot through whichever handle it happened to hold.
  fn owned_slots(handle: &SharedMappingHandle) -> usize {
    (0..MAX_WRITER_THREADS)
      .filter(|&i| handle.permissions[i].0.thread_id.load(core::sync::atomic::Ordering::Relaxed) != 0)
      .count()
  }
  let a = SharedMapping::new();
  let b = SharedMapping::new();

  let pa = a.try_aquire_permission().unwrap();
  let pa2 = a.try_aquire_permission().unwrap();
  let pb = b.try_aquire_permission().unwrap();
  core::assert_eq!(owned_slots(&a), 1, "one slot on a, shared by both permits");
  core::assert_eq!(owned_slots(&b), 1, "the nested mapping must be registered too");

  drop(pb);
  core::assert_eq!(owned_slots(&a), 1, "releasing b must not touch a");
  core::assert_eq!(owned_slots(&b), 0, "b fully released");

  drop(pa);
  core::assert_eq!(owned_slots(&a), 1, "a still held by the second permit");
  drop(pa2);
  core::assert_eq!(owned_slots(&a), 0, "a fully released");

  let pa3 = a.try_aquire_permission().unwrap();
  core::assert_eq!(owned_slots(&a), 1, "re-acquisition registers afresh");
  drop(pa3);
  core::assert_eq!(owned_slots(&a), 0);
}

#[test]
fn interning_is_exclusive_under_thread_and_mapping_churn() {
  // Threads that each touch their own mappings and then a SHARED one: the old
  // thread-cached slot made the shared-mapping permit use an unowned slot, so
  // two threads raced the lock-free eager slab write (torn interned bytes).
  // Every symbol must read back byte-exact.
  let shared = SharedMapping::new();
  std::thread::scope(|s| {
    for t in 0..8usize {
      let shared = &shared;
      s.spawn(move || {
        for round in 0..300usize {
          let own = SharedMapping::new();
          let po = own.try_aquire_permission().unwrap();
          let own_text = std::format!("own-{t}-{round}");
          let own_sym = po.get_sym_or_insert(own_text.as_bytes());
          drop(po);
          core::assert_eq!(own.get_bytes(own_sym), Some(own_text.as_bytes()));

          let ps = shared.try_aquire_permission().unwrap();
          let text = std::format!("shared-{t}-{round}-{}", "x".repeat(round % 61));
          let sym = ps.get_sym_or_insert(text.as_bytes());
          drop(ps);
          core::assert_eq!(
            shared.get_bytes(sym),
            Some(text.as_bytes()),
            "interned bytes must read back exactly (thread {t}, round {round})"
          );
        }
      });
    }
  });
}
