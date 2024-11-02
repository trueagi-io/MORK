use std::thread;
use std::sync::mpsc;
use std::time::Instant;

use pathmap::trie_map::BytesTrieMap;
use pathmap::zipper::*;

// ===================================================================================================
// USAGE: set the THREAD_CNT, N, and change the `Test` alias to edit parameters
// ===================================================================================================
const THREAD_CNT: usize = 64;
const N: usize = 100_000_000;
type Test<'a> = ReadZipperGet<'a>;
// type Test<'a> = WriteZipperInsert<'a>;


struct ReadZipperGet<'a> {
    phantom: core::marker::PhantomData<&'a ()>
}

struct WriteZipperInsert<'a> {
    phantom: core::marker::PhantomData<&'a ()>
}

trait TestParams<'a> {
    type V;
    type InZipperT;
    fn init(element_cnt: usize, real_thread_cnt: usize) -> BytesTrieMap<Self::V>;
    fn dispatch_zipper(zipper_head: &'a ZipperHead<'_, '_, Self::V>, thread_idx: usize, element_cnt: usize, real_thread_cnt: usize) -> Self::InZipperT;
    fn thread_body(zipper: Self::InZipperT, thread_idx: usize, element_cnt: usize, real_thread_cnt: usize);
}

impl<'a> TestParams<'a> for ReadZipperGet<'a> {
    type V = usize;
    type InZipperT = ReadZipperUntracked<'a, 'static, usize>;
    fn init(element_cnt: usize, real_thread_cnt: usize) -> BytesTrieMap<Self::V> {
        let elements_per_thread = element_cnt / real_thread_cnt;
        let mut map = BytesTrieMap::<usize>::new();
        for n in 0..real_thread_cnt {
            let path = [n as u8];
            let mut zipper = map.write_zipper_at_path(&path);
            for i in (n * elements_per_thread)..((n+1) * elements_per_thread) {
                zipper.descend_to(prefix_key(&(i as u64)));
                zipper.set_value(i);
                zipper.reset();
            }
        }
        map
    }
    fn dispatch_zipper(zipper_head: &'a ZipperHead<'_, '_, Self::V>, thread_idx: usize, _element_cnt: usize, _real_thread_cnt: usize) -> Self::InZipperT {
        let path = [thread_idx as u8];
        unsafe{ zipper_head.read_zipper_at_path_unchecked(path) }
    }
    fn thread_body(mut zipper: Self::InZipperT, thread_idx: usize, element_cnt: usize, real_thread_cnt: usize) {
        let elements_per_thread = element_cnt / real_thread_cnt;
        for i in (thread_idx * elements_per_thread)..((thread_idx+1) * elements_per_thread) {
            zipper.descend_to(prefix_key(&(i as u64)));
            assert_eq!(zipper.get_value().unwrap(), &i);
            zipper.reset();
        }
    }
}

impl<'a> TestParams<'a> for WriteZipperInsert<'a> {
    type V = usize;
    type InZipperT = WriteZipperUntracked<'a, 'static, usize>;
    fn init(_element_cnt: usize, _real_thread_cnt: usize) -> BytesTrieMap<Self::V> {
        BytesTrieMap::<usize>::new()
    }
    fn dispatch_zipper(zipper_head: &'a ZipperHead<'_, '_, Self::V>, thread_idx: usize, _element_cnt: usize, _real_thread_cnt: usize) -> Self::InZipperT {
        let path = [thread_idx as u8];
        unsafe{ zipper_head.write_zipper_at_exclusive_path_unchecked(path) }
    }
    fn thread_body(mut zipper: Self::InZipperT, thread_idx: usize, element_cnt: usize, real_thread_cnt: usize) {
        let elements_per_thread = element_cnt / real_thread_cnt;
        for i in (thread_idx * elements_per_thread)..((thread_idx+1) * elements_per_thread) {
            zipper.descend_to(prefix_key(&(i as u64)));
            zipper.set_value(i);
            zipper.reset();
        }
    }
}

fn main() {
    let thread_cnt = THREAD_CNT;
    let elements = N;
    let real_thread_cnt = thread_cnt.max(1);

    println!("{}, N={N}\nThread_cnt={THREAD_CNT}", std::any::type_name::<Test>());

    let t_init = Instant::now();
    let mut map = Test::init(elements, real_thread_cnt);
    println!("Init took:                  {}µs", t_init.elapsed().as_micros());

    let zipper_head_obj = map.zipper_head();
    let zipper_head = &zipper_head_obj;

    let t_thread_scope = Instant::now();
    let mut d_spawn: u128 = 0;
    let mut d_parallel: u128 = 0;
    let mut d_dispatch: u128 = 0;
    let mut t_terminate = Instant::now();
    thread::scope(|scope| {

        let mut zipper_senders = Vec::with_capacity(thread_cnt);
        let mut signal_receivers = Vec::with_capacity(thread_cnt);

        //Spawn all the threads
        let t_spawn = Instant::now();
        for n in 0..thread_cnt {
            let (zipper_tx, zipper_rx) = mpsc::channel::<<Test<'_> as TestParams>::InZipperT>();
            zipper_senders.push(zipper_tx);
            let (signal_tx, signal_rx) = mpsc::channel::<bool>();
            signal_receivers.push(signal_rx);

            scope.spawn(move || {
                loop {
                    //The thread will block here waiting for the zipper to be sent
                    match zipper_rx.recv() {
                        Ok(zipper) => {
                            //We got the zipper, do the stuff
                            Test::thread_body(zipper, n, elements, real_thread_cnt);

                            //Tell the main thread we're done
                            signal_tx.send(true).unwrap();
                        },
                        Err(_) => {
                            //The zipper_sender channel is closed, meaning it's time to shut down
                            break;
                        }
                    }
                }
            });
        }
        d_spawn = t_spawn.elapsed().as_micros();
        println!("Spawning took:              {}µs", d_spawn);

        if thread_cnt > 0 {

            //Dispatch a zipper to each thread
            let t_dispatch = Instant::now();
            for n in 0..thread_cnt {

                let zipper = Test::dispatch_zipper(&zipper_head, n, elements, real_thread_cnt);
                zipper_senders[n].send(zipper).unwrap();
            };
            d_dispatch = t_dispatch.elapsed().as_micros();
            println!("Dispatch took:              {}µs", d_dispatch);

            //Wait for the threads to all be done
            let t_parallel = Instant::now();
            for n in 0..thread_cnt {
                assert_eq!(signal_receivers[n].recv().unwrap(), true);
            };
            d_parallel = t_parallel.elapsed().as_micros();
            println!("Parallel took:              {}µs", d_parallel);

        } else {
            //No-thread case, to measure overhead of sync vs. 1-thread case
            let zipper = Test::dispatch_zipper(&zipper_head, 0, elements, real_thread_cnt);
            Test::thread_body(zipper, 0, elements, real_thread_cnt);
        }

        t_terminate = Instant::now();
    });
    let d_terminate = t_terminate.elapsed().as_micros();
    println!("Terminating threads took:   {}µs", d_terminate);
    println!("Unaccounted thread scope:   {}µs", t_thread_scope.elapsed().as_micros() - d_parallel - d_dispatch - d_spawn - d_terminate);

    let t_dropping = Instant::now();
    drop(zipper_head_obj);
    drop(map);
    println!("Dropping took:              {}µs", t_dropping.elapsed().as_micros() );

}

fn prefix_key(k: &u64) -> &[u8] {
    let bs = (8 - k.leading_zeros()/8) as u8;
    let kp: *const u64 = k;
    unsafe { std::slice::from_raw_parts(kp as *const _, (bs as usize).max(1)) }
}
