use std::sync::atomic::Ordering;
use std::time::Instant;
use rayon::ThreadPoolBuilder;
use pathmap::zipper::{Zipper, ReadZipperUntracked, ZipperIteration, ZipperAbsolutePath};
use pathmap::trie_map::BytesTrieMap;
use pathmap::zipper::*;

const K: u64 = 1_000_000_000;

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
        if !rz.to_next_sibling_byte() { break }
    }
    rz.ascend_byte();
    rz.descend_first_byte();
    if cs >= at_least {
        loop {
            f(cs, rz);
            if !rz.to_next_sibling_byte() { break }
        }
    } else {
        panic!("not implemented at_least={}, cs={}", at_least, cs)
    }
}

#[allow(unused)]
fn parallel_map() {
    const TC: u32 = 64;

    let mut map = BytesTrieMap::new();
    let zh = map.zipper_head();

    let mut buildz = unsafe { zh.write_zipper_at_exclusive_path_unchecked(&[0]) };
    buildz.graft_map(pathmap::utils::ints::gen_int_range(0, K, 1, ()));
    drop(buildz);
    let mut dz = unsafe { zh.read_zipper_at_path_unchecked(&[0]) };

    std::thread::scope(|scope| {

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
                let work_input = unsafe { zh.read_zipper_at_path_unchecked(z.origin_path()) };
                let mut opath = vec![1];
                opath.extend_from_slice(z.path());
                // println!("created zpath={:?} ({}) opath={opath:?} for {}", z.path(), z.val_count(), dispatches + 1);
                let work_output = unsafe { zh.write_zipper_at_exclusive_path_unchecked(&opath[..]) };

                units.push((work_input, work_output));

                if run >= cutoff {
                    // dispatch and clear
                    let mut thread_units = std::mem::take(&mut units);
                    run = 0;
                    dispatches += 1;
                    println!("dispatched {} up to {} ({})", dispatches, chunks, thread_units.len());
                    handles.push(scope.spawn(move || {
                        // println!("thread {} working", dispatches);
                        // work_output.set_value(());
                        for (work_input, work_output) in thread_units.iter_mut() {
                            // work_output.graft(work_input);
                            // println!("thread {} processing origin={:?} (queued: {})", dispatches, work_input.origin_path(), work_input.val_count());
                            loop {
                                if !work_input.to_next_val() { break }
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

                if !z.to_next_sibling_byte() { break }
            }
            z.ascend_byte();
        });
        if run > 0 {
            let mut thread_units = std::mem::take(&mut units);
            dispatches += 1;
            println!("dispatched {} up to {} ({})", dispatches, chunks, thread_units.len());
            handles.push(scope.spawn(move || {
                // work_output.set_value(());
                for (work_input, work_output) in thread_units.iter_mut() {
                    // work_output.graft(work_input);
                    loop {
                        if !work_input.to_next_val() { break }
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

    let rz = unsafe { zh.read_zipper_at_path_unchecked(&[]) };
    println!("result count: {}", rz.val_count());
    // while let Some(_) = rz.to_next_val() {
    //     println!("o {:?}", rz.path());
    // }
    });
}

#[allow(unused)]
fn task_parallel_map() {
    const TC: u32 = 32;
    let pool = ThreadPoolBuilder::new().num_threads(TC as usize).build().unwrap();
    static COUNTER: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

    let mut map = BytesTrieMap::new();
    let zh = map.zipper_head();

    let mut buildz = unsafe { zh.write_zipper_at_exclusive_path_unchecked(&[0]) };
    buildz.graft_map(pathmap::utils::ints::gen_int_range(0, K, 1, ()));
    drop(buildz);

    let mut work_zippers = vec![];
    let mut dz = unsafe { zh.read_zipper_at_path_unchecked(&[0]) };
    let mut chunks = 0;
    let t0 = Instant::now();
    homo(TC, &mut dz, &mut |_, z: &mut ReadZipperUntracked<()>| {
        z.descend_first_byte();
        loop {
            chunks += 1;
            // println!("p {:?} c {}", z.path(), z.child_mask().iter().fold(0, |t, x| t + x.count_ones()))
            let work_input = unsafe { zh.read_zipper_at_path_unchecked(z.origin_path()) };
            let mut opath = vec![1];
            opath.extend_from_slice(&z.path()[..]);
            // println!("dispatched zpath={:?} ({}) opath={opath:?}", z.path(), z.val_count());
            let work_output = unsafe { zh.write_zipper_at_exclusive_path_unchecked(&opath[..]) };
            unsafe { COUNTER.fetch_add(1, Ordering::Relaxed) };

            work_zippers.push((work_input, work_output));

            if !z.to_next_sibling_byte() { break }
        }
        z.ascend_byte();
    });
    drop(dz);

    let mut t1 = Instant::now();
    pool.scope(|scope| {
        for (mut work_input, mut work_output) in work_zippers {
            scope.spawn(move |_| {
                // work_output.set_value(());
                loop {
                    if !work_input.to_next_val() { break }
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
                unsafe { COUNTER.fetch_sub(1, Ordering::Relaxed) };
            });
        }
        println!("delegating {chunks} chunks took {} micros", t0.elapsed().as_micros());

        t1 = Instant::now();
    });

    while unsafe { COUNTER.load(Ordering::Acquire) > 0 } {}
    println!("processing took {} micros", t1.elapsed().as_micros());

    let rz = unsafe { zh.read_zipper_at_path_unchecked(&[]) };
    println!("result count: {}", rz.val_count());
    // while let Some(_) = rz.to_next_val() {
    //     println!("o {:?}", rz.path());
    // }
}

#[allow(unused)]
fn sequential_map() {

    let mut map = BytesTrieMap::new();
    let zh = map.zipper_head();

    let mut buildz = unsafe { zh.write_zipper_at_exclusive_path_unchecked(&[0]) };
    buildz.graft_map(pathmap::utils::ints::gen_int_range(0, K, 1, ()));
    drop(buildz);
    let mut dz = unsafe { zh.read_zipper_at_path_unchecked(&[0]) };
    let mut oz = unsafe { zh.write_zipper_at_exclusive_path_unchecked(&[1]) };

    let t0 = Instant::now();
    loop {
        if !dz.to_next_val() { break }
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

    let rz = unsafe { zh.read_zipper_at_path_unchecked(&[]) };
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

// using K = 1_000_000_000
/*
> sequential_map
processing took 98_984_927 micros

jemalloc
> parallel_map
(8) 93% eff.
delegating 60 chunks took 619 micros
processing took 13_352_843 micros

(16) 83% eff.
delegating 60 chunks took 1091 micros
processing took 7_451_781 micros

(32) 73% eff.
delegating 60 chunks took 1888 micros
processing took 4_191_062 micros

(48) 69% eff.
delegating 15259 chunks took 9439 micros
processing took 2_952_002 micros

(64) 55% eff.
delegating 15259 chunks took 10814 micros
processing took 2_766_225 micros
 */

/*
> sequential map
processing took 80_667_456 micros  (racy rc 76_223_403)

> parallel map jemalloc+2MB THP
(8) 39% eff.
delegating 60 chunks took 214 micros
processing took 25775365 micros (racy rc 24_525_754)

(16) 35% eff.
delegating 60 chunks took 754 micros
processing took 14284084 micros

(32) 32% eff.
delegating 60 chunks took 1870 micros
processing took 7856521 micros

(48) 31% eff.
delegating 60 chunks took 795 micros
processing took 5437888 micros

(64) 30% eff.
delegating 60 chunks took 3457 micros
processing took 4081127 micros (racy rc 3_787_482)
 */