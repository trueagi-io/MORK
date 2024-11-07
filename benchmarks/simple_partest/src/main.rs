use std::mem::MaybeUninit;
use std::thread;
use std::sync::mpsc;
use std::time::Instant;

use clap::Parser;
use pathmap::trie_map::BytesTrieMap;
use pathmap::zipper::*;

// ===================================================================================================
// USAGE: set the THREAD_CNT, N, and change the `Test` alias to edit parameters
// ===================================================================================================
const N: usize = 100_000_000;

#[cfg(feature = "pathmap_read")]
type Test = PathMapReadZipperGet;

#[cfg(feature = "pathmap_write")]
type Test = PathMapWriteZipperInsert;

#[cfg(feature = "unique_buf_test")]
type Test = UniqueBuffers;

#[cfg(feature = "contiguous_test")]
type Test = ContiguousRanges;

#[cfg(feature = "interleaved_test")]
type Test = InterleavedRanges;

#[cfg(feature = "alloc_test")]
type Test = AllocLinkedList;

//ContiguousButScattered not selectable with feature, but can be enabled here!
// type Test = ContiguousButScattered;

#[cfg(all(not(feature = "pathmap_read"), not(feature = "pathmap_write"), not(feature = "unique_buf_test"), not(feature = "contiguous_test"), not(feature = "interleaved_test"), not(feature = "alloc_test")))]
type Test = Dummy;

const BLOCK_PAD_SIZE: usize = 64 - 16;
const SCATTER_STEP_SIZE: usize = 256; //Used with `ContiguousButScattered` test

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct CliArgs {
    /// Sweep the thread count from 0..256
    #[arg(long, default_value_t = false)]
    sweep: bool,

    /// The number of threads to run
    #[arg(short, long, default_value_t = 64)]
    threads: usize,
}

struct Dummy;

struct AllocLinkedList {
    heads: Vec<core::cell::UnsafeCell<Option<Box<Node>>>>,
}

/// Possibly the real best case.  A separate buffer to write to for each thread
struct UniqueBuffers {
    bufs: core::cell::UnsafeCell<Vec<Vec<core::cell::UnsafeCell<core::mem::MaybeUninit<Node>>>>>,
}

/// Best case.  All items are written into a contiguous block by the thread
struct ContiguousRanges {
    buf: core::cell::UnsafeCell<Vec<core::cell::UnsafeCell<core::mem::MaybeUninit<Node>>>>,
}

/// Worst case.  All threads are interleaving writes to adjacent cache lines
struct InterleavedRanges {
    buf: core::cell::UnsafeCell<Vec<core::cell::UnsafeCell<core::mem::MaybeUninit<Node>>>>,
}

/// Middle case.  Each thread has its own block, but the writes are to non-contiguous cache lines
struct ContiguousButScattered {
    buf: core::cell::UnsafeCell<Vec<core::cell::UnsafeCell<core::mem::MaybeUninit<Node>>>>,
}

#[repr(align(64))]
struct Node {
    _val: usize,
    next: core::cell::UnsafeCell<Option<Box<Node>>>,
    _pad: [u8; BLOCK_PAD_SIZE],
}

struct PathMapReadZipperGet {
    map: BytesTrieMap<usize>,
}

struct PathMapWriteZipperInsert  {
    map: BytesTrieMap<usize>,
}

trait TestParams<'map, 'head> {
    type HeadT;
    type InZipperT;
    fn init(element_cnt: usize, real_thread_cnt: usize) -> Self;
    fn prepare(&'map mut self) -> Self::HeadT;
    fn dispatch_zipper(state: &'head Self::HeadT, thread_idx: usize, element_cnt: usize, real_thread_cnt: usize) -> Self::InZipperT;
    fn thread_body(zipper: Self::InZipperT, thread_idx: usize, element_cnt: usize, real_thread_cnt: usize);
    fn drop_head(head: Self::HeadT);
    fn drop_self(self);
}

impl<'map, 'head> TestParams<'map, 'head> for ContiguousRanges {
    type HeadT = &'map Self where Self: 'map;
    type InZipperT = &'head mut [core::cell::UnsafeCell<MaybeUninit<Node>>];
    fn init(element_cnt: usize, _real_thread_cnt: usize) -> Self {
        let mut buf = Vec::with_capacity(element_cnt);
        buf.resize_with(element_cnt, || core::cell::UnsafeCell::new(MaybeUninit::uninit()));
        Self {
            buf: core::cell::UnsafeCell::new(buf)
        }
    }
    fn prepare(&'map mut self) -> Self::HeadT {
        self
    }
    fn dispatch_zipper(head: &'head Self::HeadT, thread_idx: usize, element_cnt: usize, real_thread_cnt: usize) -> Self::InZipperT {
        let elements_per_thread = element_cnt / real_thread_cnt;
        let buf = unsafe{ &mut*head.buf.get() };
        &mut buf[(thread_idx * elements_per_thread)..((thread_idx+1) * elements_per_thread)]
    }
    fn thread_body(slice: Self::InZipperT, thread_idx: usize, element_cnt: usize, real_thread_cnt: usize) {
        let elements_per_thread = element_cnt / real_thread_cnt;
        let base = thread_idx * elements_per_thread;
        for i in 0..elements_per_thread {
            slice[i] = core::cell::UnsafeCell::new(MaybeUninit::new(Node{
                _val: base + i,
                next: core::cell::UnsafeCell::new(None),
                _pad: [0u8; BLOCK_PAD_SIZE],
            }));
        }
    }
    fn drop_head(_head: Self::HeadT) { }
    fn drop_self(self) { }
}

impl<'map, 'head> TestParams<'map, 'head> for UniqueBuffers {
    type HeadT = &'map Self where Self: 'map;
    type InZipperT = &'head mut [core::cell::UnsafeCell<MaybeUninit<Node>>];
    fn init(element_cnt: usize, real_thread_cnt: usize) -> Self {
        let elements_per_thread = element_cnt / real_thread_cnt;
        let mut bufs = Vec::with_capacity(real_thread_cnt);
        for _ in 0..real_thread_cnt {
            let mut buf = Vec::with_capacity(elements_per_thread);
            buf.resize_with(elements_per_thread, || core::cell::UnsafeCell::new(MaybeUninit::uninit()));
            bufs.push(buf)
        }
        Self {
            bufs: core::cell::UnsafeCell::new(bufs)
        }
    }
    fn prepare(&'map mut self) -> Self::HeadT {
        self
    }
    fn dispatch_zipper(head: &'head Self::HeadT, thread_idx: usize, _element_cnt: usize, _real_thread_cnt: usize) -> Self::InZipperT {
        let bufs = unsafe{ &mut*head.bufs.get() };
        let buf = bufs.get_mut(thread_idx).unwrap();
        &mut buf[..]
    }
    fn thread_body(slice: Self::InZipperT, thread_idx: usize, element_cnt: usize, real_thread_cnt: usize) {
        let elements_per_thread = element_cnt / real_thread_cnt;
        let base = thread_idx * elements_per_thread;
        for i in 0..elements_per_thread {
            slice[i] = core::cell::UnsafeCell::new(MaybeUninit::new(Node{
                _val: base + i,
                next: core::cell::UnsafeCell::new(None),
                _pad: [0u8; BLOCK_PAD_SIZE],
            }));
        }
    }
    fn drop_head(_head: Self::HeadT) { }
    fn drop_self(self) { }
}

impl<'map, 'head> TestParams<'map, 'head> for InterleavedRanges {
    type HeadT = &'map Self where Self: 'map;
    type InZipperT = &'head mut [core::cell::UnsafeCell<MaybeUninit<Node>>];
    fn init(element_cnt: usize, _real_thread_cnt: usize) -> Self {
        let mut buf = Vec::with_capacity(element_cnt);
        buf.resize_with(element_cnt, || core::cell::UnsafeCell::new(MaybeUninit::uninit()));
        Self {
            buf: core::cell::UnsafeCell::new(buf)
        }
    }
    fn prepare(&'map mut self) -> Self::HeadT {
        self
    }
    fn dispatch_zipper(head: &'head Self::HeadT, _thread_idx: usize, _element_cnt: usize, _real_thread_cnt: usize) -> Self::InZipperT {
        let buf = unsafe{ &mut*head.buf.get() };
        &mut buf[..] // This isn't going to pass muster with miri, but it's just an experiment
    }
    fn thread_body(slice: Self::InZipperT, thread_idx: usize, element_cnt: usize, real_thread_cnt: usize) {
        let elements_per_thread = element_cnt / real_thread_cnt;
        for i in 0..elements_per_thread {
            let idx = (i*real_thread_cnt) + thread_idx;
            slice[idx] = core::cell::UnsafeCell::new(MaybeUninit::new(Node{
                _val: idx,
                next: core::cell::UnsafeCell::new(None),
                _pad: [0u8; BLOCK_PAD_SIZE],
            }));
        }
    }
    fn drop_head(_head: Self::HeadT) { }
    fn drop_self(self) { }
}

impl<'map, 'head> TestParams<'map, 'head> for ContiguousButScattered {
    type HeadT = &'map Self where Self: 'map;
    type InZipperT = &'head mut [core::cell::UnsafeCell<MaybeUninit<Node>>];
    fn init(element_cnt: usize, _real_thread_cnt: usize) -> Self {
        let mut buf = Vec::with_capacity(element_cnt);
        buf.resize_with(element_cnt, || core::cell::UnsafeCell::new(MaybeUninit::uninit()));
        Self {
            buf: core::cell::UnsafeCell::new(buf)
        }
    }
    fn prepare(&'map mut self) -> Self::HeadT {
        self
    }
    fn dispatch_zipper(head: &'head Self::HeadT, thread_idx: usize, element_cnt: usize, real_thread_cnt: usize) -> Self::InZipperT {
        let elements_per_thread = element_cnt / real_thread_cnt;
        let buf = unsafe{ &mut*head.buf.get() };
        &mut buf[(thread_idx * elements_per_thread)..((thread_idx+1) * elements_per_thread)]
    }
    fn thread_body(slice: Self::InZipperT, thread_idx: usize, element_cnt: usize, real_thread_cnt: usize) {
        let elements_per_thread = element_cnt / real_thread_cnt;
        let base = elements_per_thread * thread_idx;
        for j in 0..SCATTER_STEP_SIZE {
            for i in 0..(elements_per_thread / SCATTER_STEP_SIZE) {
                let idx = (i*SCATTER_STEP_SIZE) + j;
                slice[idx] = core::cell::UnsafeCell::new(MaybeUninit::new(Node{
                    _val: base + idx,
                    next: core::cell::UnsafeCell::new(None),
                    _pad: [0u8; BLOCK_PAD_SIZE],
                }));
            }
        }
    }
    fn drop_head(_head: Self::HeadT) { }
    fn drop_self(self) { }
}

impl<'map, 'head> TestParams<'map, 'head> for AllocLinkedList {
    type HeadT = &'map Self where Self: 'map;
    type InZipperT = &'head mut Option<Box<Node>>;
    fn init(_element_cnt: usize, real_thread_cnt: usize) -> Self {
        let heads = (0..real_thread_cnt).into_iter()
            .map(|_| core::cell::UnsafeCell::new(None)).collect();
        Self {
            heads,
        }
    }
    fn prepare(&'map mut self) -> Self::HeadT {
        self
    }
    fn dispatch_zipper(heads: &'head Self::HeadT, thread_idx: usize, _element_cnt: usize, _real_thread_cnt: usize) -> Self::InZipperT {
        unsafe{ &mut *heads.heads[thread_idx].get() }
    }
    fn thread_body(mut cur: Self::InZipperT, thread_idx: usize, element_cnt: usize, real_thread_cnt: usize) {
        let elements_per_thread = element_cnt / real_thread_cnt;
        for i in (thread_idx * elements_per_thread)..((thread_idx+1) * elements_per_thread) {
            *cur = Some(Box::new(Node{
                _val: i,
                next: core::cell::UnsafeCell::new(None),
                _pad: [0u8; BLOCK_PAD_SIZE],
            }));
            cur = unsafe{ &mut *cur.as_mut().unwrap().next.get() };
        }
    }
    fn drop_head(_head: Self::HeadT) { }
    fn drop_self(self) {
        for head in self.heads {
            let cur = unsafe{ &mut *head.get() };
            while let Some(node) = cur {
                let next = unsafe{ &mut *node.next.get() };
                *cur = core::mem::take(next);
            }
        }
    }
}

impl<'map, 'head> TestParams<'map, 'head> for PathMapReadZipperGet {
    type HeadT = ZipperHead<'map, 'map, usize>;
    type InZipperT = ReadZipperUntracked<'head, 'static, usize>;
    fn init(element_cnt: usize, real_thread_cnt: usize) -> Self {
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
        Self {
            map,
        }
    }
    fn prepare(&'map mut self) -> Self::HeadT {
        self.map.zipper_head()
    }
    fn dispatch_zipper(zipper_head: &'head Self::HeadT, thread_idx: usize, _element_cnt: usize, _real_thread_cnt: usize) -> Self::InZipperT {
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
    fn drop_head(_head: Self::HeadT) { }
    fn drop_self(self) { }
}

impl<'map, 'head>  TestParams<'map, 'head>  for PathMapWriteZipperInsert  {
    type HeadT = ZipperHead<'map, 'map, usize>;
    type InZipperT = WriteZipperUntracked<'head, 'static, usize>;
    fn init(_element_cnt: usize, _real_thread_cnt: usize) -> Self {
        Self {
            map: BytesTrieMap::<usize>::new(),
        }
    }
    fn prepare(&'map mut self) -> Self::HeadT {
        self.map.zipper_head()
    }
    fn dispatch_zipper(zipper_head: &'head Self::HeadT, thread_idx: usize, _element_cnt: usize, _real_thread_cnt: usize) -> Self::InZipperT {
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
    fn drop_head(_head: Self::HeadT) { }
    fn drop_self(self) { }
}

impl<'map, 'head> TestParams<'map, 'head> for Dummy {
    type HeadT = ();
    type InZipperT = ();
    fn init(_element_cnt: usize, _real_thread_cnt: usize) -> Self {
        panic!("\nMust specify a test feature at build time.\n");
    }
    fn prepare(&'map mut self) -> Self::HeadT { }
    fn dispatch_zipper(_head: &'head Self::HeadT, _thread_idx: usize, _element_cnt: usize, _real_thread_cnt: usize) -> Self::InZipperT { }
    fn thread_body(_zipper: Self::InZipperT, _thread_idx: usize, _element_cnt: usize, _real_thread_cnt: usize) { }
    fn drop_head(_head: Self::HeadT) { }
    fn drop_self(self) { }
}

const THREAD_CNT_TABLE: [usize; 16] = [0, 1, 2, 4, 8, 16, 24, 32, 48, 64, 96, 128, 160, 192, 224, 256];

fn main() {
    let args = CliArgs::parse();

    let mut thread_cnt_table_idx = 0;
    loop {
        let thread_cnt = if args.sweep {
            THREAD_CNT_TABLE[thread_cnt_table_idx]
        } else {
            args.threads
        };
        let elements = N;
        let real_thread_cnt = thread_cnt.max(1);

        println!("\n{}\nN={elements}, Thread_cnt={thread_cnt}", std::any::type_name::<Test>());

        let t_init = Instant::now();
        let mut map = Test::init(elements, real_thread_cnt);
        let zipper_head = Test::prepare(&mut map);
        let zipper_head_ref = &zipper_head; //So the thread scope closure doesn't capture the ZipperHead
        println!("Init took:                  {}µs", t_init.elapsed().as_micros());

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
                let (zipper_tx, zipper_rx) = mpsc::channel::<<Test as TestParams>::InZipperT>();
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

                    let zipper = Test::dispatch_zipper(zipper_head_ref, n, elements, real_thread_cnt);
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
                let zipper = Test::dispatch_zipper(zipper_head_ref, 0, elements, real_thread_cnt);
                Test::thread_body(zipper, 0, elements, real_thread_cnt);
            }

            t_terminate = Instant::now();
        });
        let d_terminate = t_terminate.elapsed().as_micros();
        println!("Terminating threads took:   {}µs", d_terminate);
        println!("Unaccounted thread scope:   {}µs", t_thread_scope.elapsed().as_micros() - d_parallel - d_dispatch - d_spawn - d_terminate);

        let t_dropping = Instant::now();
        Test::drop_head(zipper_head);
        Test::drop_self(map);
        println!("Dropping took:              {}µs", t_dropping.elapsed().as_micros() );

        thread_cnt_table_idx += 1;
        if thread_cnt_table_idx >= THREAD_CNT_TABLE.len() || !args.sweep {
            break;
        }
    }
}

fn prefix_key(k: &u64) -> &[u8] {
    let bs = (8 - k.leading_zeros()/8) as u8;
    let kp: *const u64 = k;
    unsafe { std::slice::from_raw_parts(kp as *const _, (bs as usize).max(1)) }
}
