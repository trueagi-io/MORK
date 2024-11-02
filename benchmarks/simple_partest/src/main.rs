use std::thread;
use std::sync::mpsc;
use std::time::Instant;

use pathmap::trie_map::BytesTrieMap;
use pathmap::zipper::*;

const THREAD_CNT: usize = 64;
const N: usize = 100_000_000;

fn main() {
    let thread_cnt = THREAD_CNT;
    let elements = N;
    let real_thread_cnt = thread_cnt.max(1);
    let elements_per_thread = elements / real_thread_cnt;

    let mut map = BytesTrieMap::<usize>::new();
    let zipper_head = map.zipper_head();

    let t_thread_scope = Instant::now();
    let mut d_spawn: u128 = 0;
    let mut d_parallel: u128 = 0;
    let mut d_dispatch: u128 = 0;
    let mut t_terminate = Instant::now();
    thread::scope(|scope| {

        let mut zipper_senders: Vec<mpsc::Sender<WriteZipperUntracked<'_, '_, usize>>> = Vec::with_capacity(thread_cnt);
        let mut signal_receivers: Vec<mpsc::Receiver<bool>> = Vec::with_capacity(thread_cnt);

        //Spawn all the threads
        let t_spawn = Instant::now();
        for n in 0..thread_cnt {
            let (zipper_tx, zipper_rx) = mpsc::channel::<WriteZipperUntracked<'_, '_, usize>>();
            zipper_senders.push(zipper_tx);
            let (signal_tx, signal_rx) = mpsc::channel::<bool>();
            signal_receivers.push(signal_rx);

            scope.spawn(move || {
                loop {
                    //The thread will block here waiting for the zipper to be sent
                    match zipper_rx.recv() {
                        Ok(mut zipper) => {
                            //We got the zipper, do the stuff
                            for i in (n * elements_per_thread)..((n+1) * elements_per_thread) {
                                zipper.descend_to(prefix_key(&(i as u64)));
                                zipper.set_value(i);
                                zipper.reset();
                            }

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
                let path = [n as u8];
                let zipper = unsafe{ zipper_head.write_zipper_at_exclusive_path_unchecked(path) };
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
            let mut zipper = unsafe{ zipper_head.write_zipper_at_exclusive_path_unchecked(&[0]) };
            for i in 0..elements {
                zipper.descend_to(prefix_key(&(i as u64)));
                zipper.set_value(i);
                zipper.reset();
            }
        }

        t_terminate = Instant::now();
    });
    let d_terminate = t_terminate.elapsed().as_micros();
    println!("Terminating threads took:   {}µs", d_terminate);
    println!("Unaccounted thread scope:   {}µs", t_thread_scope.elapsed().as_micros() - d_parallel - d_dispatch - d_spawn - d_terminate);

    let t_dropping = Instant::now();
    drop(zipper_head);
    drop(map);
    println!("Dropping took:              {}µs", t_dropping.elapsed().as_micros() );

}

fn prefix_key(k: &u64) -> &[u8] {
    let bs = (8 - k.leading_zeros()/8) as u8;
    let kp: *const u64 = k;
    unsafe { std::slice::from_raw_parts(kp as *const _, (bs as usize).max(1)) }
}
