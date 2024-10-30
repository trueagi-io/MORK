use std::sync::atomic::Ordering;
use std::thread::sleep;
use std::time::{Duration, Instant};
use rayon::{ThreadPool, ThreadPoolBuilder};
use pathmap::zipper::{Zipper, ReadZipperUntracked, WriteZipperUntracked, ZipperIteration, ZipperHead, ZipperAbsolutePath};
use pathmap::trie_map::BytesTrieMap;
use pathmap::zipper::WriteZipper;


fn homo<F: FnMut(u32, &mut ReadZipperUntracked<()>) -> ()>(at_least: u32, rz: &mut ReadZipperUntracked<()>, f: &mut F) {
    rz.descend_until();

    let mut cs = rz.child_mask().iter().fold(0, |t, x| t + x.count_ones());

    if cs >= at_least {
        f(cs, rz);
        return;
    }

    cs = 0;
    rz.descend_first_byte();
    loop {
        cs += rz.child_mask().iter().fold(0, |t, x| t + x.count_ones());
        if !rz.to_sibling(true) { break }
    }
    rz.ascend_byte();
    rz.descend_first_byte();
    if cs >= at_least {
        loop {
            f(cs, rz);
            if !rz.to_sibling(true) { break }
        }
    } else {
        panic!("not implemented at_least={}, cs={}", at_least, cs)
    }
}

static mut M: Option<Box<BytesTrieMap<()>>> = None;
static mut ZH: Option<Box<ZipperHead<()>>> = None;

fn setup() -> &'static mut ZipperHead<'static, 'static, ()> {
    unsafe {
        M = Some(Box::new(BytesTrieMap::new()));
        ZH = Some(Box::new(M.as_deref_mut().unwrap().zipper_head()));
        ZH.as_mut().unwrap()
    }
}

fn parallel_map() {
    const k: u64 = 1_000_000_000;
    const TC: u32 = 12;

    let zh = setup();

    let mut buildz = unsafe { zh.write_zipper_at_exclusive_path_unchecked(&[0]) };
    buildz.graft_map(BytesTrieMap::range::<true, u64>(0, k, 1, ()));
    drop(buildz);
    let mut dz = unsafe { zh.read_zipper_at_path_unchecked(&[0]) };

    let mut dispatches = 0;
    let mut chunks = 0;
    let t0 = Instant::now();
    let mut run = 0;
    let mut units = vec![];
    let mut handles = vec![];
    homo(TC, &mut dz, &mut |cs, z: &mut ReadZipperUntracked<()>| {
        let cutoff = cs.div_ceil(TC);
        z.descend_first_byte();
        loop {
            chunks += 1;
            run += 1;

            // println!("p {:?} c {}", z.path(), z.child_mask().iter().fold(0, |t, x| t + x.count_ones()))
            let mut work_input = unsafe { zh.read_zipper_at_path_unchecked(z.origin_path().unwrap()) };
            let mut opath = vec![1];
            opath.extend_from_slice(z.path());
            // println!("created zpath={:?} ({}) opath={opath:?} for {}", z.path(), z.val_count(), dispatches + 1);
            let mut work_output = unsafe { zh.write_zipper_at_exclusive_path_unchecked(&opath[..]) };

            units.push((work_input, work_output));

            if run >= cutoff {
                // dispatch and clear
                let mut thread_units = std::mem::take(&mut units);
                run = 0;
                dispatches += 1;
                println!("dispatched {} up to {} ({})", dispatches, chunks, thread_units.len());
                handles.push(std::thread::spawn(move || {
                    // println!("thread {} working", dispatches);
                    // work_output.set_value(());
                    for (work_input, work_output) in thread_units.iter_mut() {
                        // work_output.graft(work_input);
                        // println!("thread {} processing origin={:?} (queued: {})", dispatches, work_input.origin_path(), work_input.val_count());
                        loop {
                            if work_input.to_next_val().is_none() { break }
                            // println!("tp {:?}", work_input.path());
                            let mut buffer = [0; 8];
                            for (s, t) in work_input.path().iter().rev().zip(buffer.iter_mut().rev()) {
                                *t = *s;
                            }
                            let v = u64::from_be_bytes(buffer);
                            work_output.descend_to(work_input.path());
                            let vr = (v as f64).sqrt() as u64;
                            // println!("calculated f({v}) = {vr}");
                            work_output.descend_to(&vr.to_be_bytes()[..]);
                            work_output.set_value(());
                            work_output.reset();
                        }
                    }
                    // println!("thread {} done working", dispatches);
                }));
            }

            if !z.to_sibling(true) { break }
        }
        z.ascend_byte();
    });
    if run > 0 {
        let mut thread_units = std::mem::take(&mut units);
        run = 0;
        dispatches += 1;
        println!("dispatched {} up to {} ({})", dispatches, chunks, thread_units.len());
        handles.push(std::thread::spawn(move || {
            // work_output.set_value(());
            for (work_input, work_output) in thread_units.iter_mut() {
                // work_output.graft(work_input);
                loop {
                    if work_input.to_next_val().is_none() { break }
                    // println!("tp {:?}", work_input.path());
                    let mut buffer = [0; 8];
                    for (s, t) in work_input.path().iter().rev().zip(buffer.iter_mut().rev()) {
                        *t = *s;
                    }
                    let v = u64::from_be_bytes(buffer);
                    work_output.descend_to(work_input.path());
                    let vr = (v as f64).sqrt() as u64;
                    // println!("calculated f({v}) = {vr}");
                    work_output.descend_to(&vr.to_be_bytes()[..]);
                    work_output.set_value(());
                    work_output.reset();
                }
            }
        }));
    }
    drop(dz);
    println!("delegating {chunks} chunks took {} micros", t0.elapsed().as_micros());

    let t1 = Instant::now();
    for handle in handles { handle.join().unwrap() }
    // sleep(Duration::new(1, 0));
    println!("processing took {} micros", t1.elapsed().as_micros());

    let mut rz = unsafe { zh.read_zipper_at_path_unchecked(&[]) };
    println!("result count: {}", rz.val_count());
    // while let Some(_) = rz.to_next_val() {
    //     println!("o {:?}", rz.path());
    // }
}

fn task_parallel_map() {
    const k: u64 = 1_000_000_000;
    const TC: u32 = 32;
    let pool = ThreadPoolBuilder::new().num_threads(TC as usize).build().unwrap();
    static mut counter: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

    let zh = setup();

    let mut buildz = unsafe { zh.write_zipper_at_exclusive_path_unchecked(&[0]) };
    buildz.graft_map(BytesTrieMap::range::<true, u64>(0, k, 1, ()));
    drop(buildz);
    let mut dz = unsafe { zh.read_zipper_at_path_unchecked(&[0]) };

    let mut chunks = 0;
    let t0 = Instant::now();
    homo(TC, &mut dz, &mut |_, z: &mut ReadZipperUntracked<()>| {
        z.descend_first_byte();
        loop {
            chunks += 1;
            // println!("p {:?} c {}", z.path(), z.child_mask().iter().fold(0, |t, x| t + x.count_ones()))
            let mut work_input = unsafe { zh.read_zipper_at_path_unchecked(z.origin_path().unwrap()) };
            let mut opath = vec![1];
            opath.extend_from_slice(&z.path()[..]);
            // println!("dispatched zpath={:?} ({}) opath={opath:?}", z.path(), z.val_count());
            let mut work_output = unsafe { zh.write_zipper_at_exclusive_path_unchecked(&opath[..]) };
            unsafe { counter.fetch_add(1, Ordering::Relaxed) };
            pool.spawn(move || {
                // work_output.set_value(());
                loop {
                    if work_input.to_next_val().is_none() { break }
                    // println!("tp {:?}", work_input.path());
                    let mut buffer = [0; 8];
                    for (s, t) in work_input.path().iter().rev().zip(buffer.iter_mut().rev()) {
                        *t = *s;
                    }
                    let v = u64::from_be_bytes(buffer);
                    work_output.descend_to(work_input.path());
                    let vr = (v as f64).sqrt() as u64;
                    // println!("calculated f({v}) = {vr}");
                    work_output.descend_to(&vr.to_be_bytes()[..]);
                    work_output.set_value(());
                    work_output.reset();
                }
                unsafe { counter.fetch_sub(1, Ordering::Relaxed) };
            });

            if !z.to_sibling(true) { break }
        }
        z.ascend_byte();
    });
    drop(dz);
    println!("delegating {chunks} chunks took {} micros", t0.elapsed().as_micros());

    let t1 = Instant::now();
    while unsafe { counter.load(Ordering::Acquire) > 0 } {}
    // sleep(Duration::new(1, 0));
    println!("processing took {} micros", t1.elapsed().as_micros());

    let mut rz = unsafe { zh.read_zipper_at_path_unchecked(&[]) };
    println!("result count: {}", rz.val_count());
    // while let Some(_) = rz.to_next_val() {
    //     println!("o {:?}", rz.path());
    // }
}

fn sequential_map() {
    // const k: u64 = 1000;
    const k: u64 = 1_000_000_000;

    let zh = setup();

    let mut buildz = unsafe { zh.write_zipper_at_exclusive_path_unchecked(&[0]) };
    buildz.graft_map(BytesTrieMap::range::<true, u64>(0, k, 1, ()));
    drop(buildz);
    let mut dz = unsafe { zh.read_zipper_at_path_unchecked(&[0]) };
    let mut oz = unsafe { zh.write_zipper_at_exclusive_path_unchecked(&[1]) };

    let t0 = Instant::now();
    loop {
        if dz.to_next_val().is_none() { break }
        // println!("tp {:?}", dz.path());
        let mut buffer = [0; 8];
        for (s, t) in dz.path().iter().rev().zip(buffer.iter_mut().rev()) {
            *t = *s;
        }
        let v = u64::from_be_bytes(buffer);
        oz.descend_to(dz.path());
        let vr = (v as f64).sqrt() as u64;
        // println!("calculated f({v}) = {vr}");
        oz.descend_to(&vr.to_be_bytes()[..]);
        oz.set_value(());
        oz.reset();
    }
    drop(oz);
    println!("processing took {} micros", t0.elapsed().as_micros());

    let mut rz = unsafe { zh.read_zipper_at_path_unchecked(&[]) };
    println!("result count: {}", rz.val_count());
    // while let Some(_) = rz.to_next_val() {
    //     println!("o {:?}", rz.path());
    // }
    // let counters = pathmap::counters::Counters::count_ocupancy(unsafe { M.as_ref() }.unwrap());
    // counters.print_histogram_by_depth();
    // counters.print_run_length_histogram();
    // counters.print_list_node_stats();
}


fn main() {
    // sequential_map();
    // task_parallel_map();
    parallel_map();
}
