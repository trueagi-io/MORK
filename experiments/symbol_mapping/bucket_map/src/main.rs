#[allow(unused_imports)]
use std::{hint::black_box, mem, ptr, time::Instant};
#[allow(unused_imports)]
use pathmap::ring::Lattice;
use bucket_map::*;
use rayon::prelude::*;
use mork_bytestring::{Expr, ExprZipper};
use mork_frontend::bytestring_parser::{ParseContext, Parser, ParserErrorType};
use pathmap::trie_map::BytesTrieMap;
// use pathmap::zipper::WriteZipper;
// use bstr::ByteSlice;
// use naive_map;



/*** no interning, single threaded ***/
/*
struct IdentityDataParser { count: u64 }

impl Parser for IdentityDataParser {
    fn tokenizer<'r>(&mut self, s: &[u8]) -> &'r [u8] {
        self.count += 1;
        return unsafe { std::mem::transmute(s) };
    }
}

impl IdentityDataParser {
    fn new() -> Self {
        Self {
            count: 3,
        }
    }
}

fn make_map(slice: &[u8]) -> BytesTrieMap<()> {
    let mut btm: BytesTrieMap<()> = BytesTrieMap::new();
    let mut it = Context::new(slice);
    let mut parser = IdentityDataParser::new();
    let mut i = 0;
    let mut stack = [0; 2 << 19];
    loop {
        unsafe {
            let mut ez = ExprZipper::new(Expr{ptr: stack.as_mut_ptr()});
            match parser.sexpr(&mut it, &mut ez) {
                Ok(()) => { btm.insert(&stack[..ez.loc], ()); }
                Err(ParserError::InputFinished) => { break }
                Err(other) => { panic!("{:?}", other) }
            }
            i += 1;
            it.variables.clear();
        }
    }
    println!("inserted {}, symbols {}", i, parser.count - 3);
    btm
}

fn main() {
    let filepath = "/run/media/adam/2c0662f2-6bf7-4afb-8c8b-a9e645f31bc6/bmkg/ckg_v3/results/kg_properties_aggregated.metta";
    let mut file = std::fs::File::open(filepath)
        .expect("Should have been able to read the file");
    let slice = unsafe { memmap2::Mmap::map(&file).unwrap() };

    let t0 = Instant::now();
    println!("processing");
    let m = make_map(&slice);
    println!("processing took {} millis", t0.elapsed().as_millis());
    println!("map contains: {}", m.val_count());
}
*/
/*
/run/media/adam/2c0662f2-6bf7-4afb-8c8b-a9e645f31bc6/bmkg/ckg_v3/results/kg_properties_aggregated.metta
inserted 603528346, symbols 2211304036
processing took 294178 millis
map contains: 344777665
User time (seconds): 336.93
System time (seconds): 14.77
Percent of CPU this job got: 99%
Elapsed (wall clock) time (h:mm:ss or m:ss): 5:53.08
Average shared text size (kbytes): 0
Average unshared data size (kbytes): 0
Average stack size (kbytes): 0
Average total size (kbytes): 0
Maximum resident set size (kbytes): 97836120
Average resident set size (kbytes): 0
Major (requiring I/O) page faults: 1
Minor (reclaiming a frame) page faults: 17383174
Voluntary context switches: 704
Involuntary context switches: 4513
 */

/*** interning, single threaded ***/
/*
struct SequentialDataParser {
    count: u64,
    symbols: BytesTrieMap<u64>,
    strings: BytesTrieMap<&'static [u8]>,
}

impl SequentialDataParser {
    fn new() -> Self {
        Self {
            count: 3,
            symbols: BytesTrieMap::new(),
            strings: BytesTrieMap::new(),
        }
    }

    const EMPTY: &'static [u8] = &[];
}

impl Parser for SequentialDataParser {
    fn tokenizer<'r>(&mut self, s: &[u8]) -> &'r [u8] {
        if s.len() == 0 { return Self::EMPTY }
        let mut z = self.symbols.write_zipper_at_path(s);
        let r = z.get_value_or_insert_with(|| {
            self.count += 1;
            u64::from_be(self.count)
        });
        let bs = (8 - r.trailing_zeros()/8) as usize;
        let l = bs.max(1);
        let interned: &[u8] = unsafe { std::slice::from_raw_parts_mut((r as *mut u64 as *mut u8).byte_offset((8 - l) as isize), l) };
        self.strings.insert(interned, unsafe { mem::transmute(s) });
        interned
    }
}


fn make_map(slice: &[u8]) -> BytesTrieMap<()> {
    let mut btm: BytesTrieMap<()> = BytesTrieMap::new();
    let mut it = Context::new(slice);
    let mut parser = SequentialDataParser::new();
    let mut i = 0;
    let mut stack = [0; 2 << 19];
    loop {
        unsafe {
            let mut ez = ExprZipper::new(Expr{ptr: stack.as_mut_ptr()});
            match parser.sexpr(&mut it, &mut ez) {
                Ok(()) => { btm.insert(&stack[..ez.loc], ()); }
                Err(ParserError::InputFinished) => { break }
                Err(other) => { panic!("{:?}", other) }
            }
            i += 1;
            it.variables.clear();
        }
    }
    println!("inserted {}, symbols {}", i, parser.count - 3);
    btm
}

fn main() {
    let filepath = "/run/media/adam/2c0662f2-6bf7-4afb-8c8b-a9e645f31bc6/bmkg/ckg_v3/results/kg_properties_aggregated.metta";
    let mut file = std::fs::File::open(filepath)
        .expect("Should have been able to read the file");
    let slice = unsafe { memmap2::Mmap::map(&file).unwrap() };

    let t0 = Instant::now();
    println!("processing");
    let m = make_map(&slice);
    println!("processing took {} millis", t0.elapsed().as_millis());
    println!("map contains: {}", m.val_count());
}
*/
/*
inserted 603528346, symbols 67442965
processing took 690479 millis
map contains: 344777665
Command being timed: "../../../target/release/bucket_map"
User time (seconds): 733.84
System time (seconds): 15.02
Percent of CPU this job got: 99%
Elapsed (wall clock) time (h:mm:ss or m:ss): 12:31.21
Average shared text size (kbytes): 0
Average unshared data size (kbytes): 0
Average stack size (kbytes): 0
Average total size (kbytes): 0
Maximum resident set size (kbytes): 83023984
Average resident set size (kbytes): 0
Major (requiring I/O) page faults: 0
Minor (reclaiming a frame) page faults: 13947423
Voluntary context switches: 1
Involuntary context switches: 10089
*/
/*** no interning, multi-threaded ***/
/*
struct PromiseSafe(BytesTrieMap<()>);

unsafe impl Send for PromiseSafe {}

struct IdentityDataParser { count: u64 }

impl Parser for IdentityDataParser {
    fn tokenizer<'r>(&mut self, s: &[u8]) -> &'r [u8] {
        self.count += 1;
        return unsafe { std::mem::transmute(s) };
    }
}

impl IdentityDataParser {
    fn new() -> Self {
        Self {
            count: 3,
        }
    }
}

fn make_map(slice: &[u8]) -> BytesTrieMap<()> {
    let mut btm: BytesTrieMap<()> = BytesTrieMap::new();
    let mut it = Context::new(slice);
    let mut parser = IdentityDataParser::new();
    let mut i = 0;
    let mut stack = [0; 2 << 19];
    loop {
        unsafe {
            let mut ez = ExprZipper::new(Expr{ptr: stack.as_mut_ptr()});
            match parser.sexpr(&mut it, &mut ez) {
                Ok(()) => { btm.insert(&stack[..ez.loc], ()); }
                Err(ParserError::InputFinished) => { break }
                Err(other) => { panic!("{:?}", other) }
            }
            i += 1;
            it.variables.clear();
        }
    }
    // println!("inserted {}, symbols {}", i, parser.count - 3);
    btm
}

fn main() {
    let filepath = "/run/media/adam/2c0662f2-6bf7-4afb-8c8b-a9e645f31bc6/bmkg/ckg_v3/results/kg_properties_aggregated.metta";
    let mut file = std::fs::File::open(filepath)
        .expect("Should have been able to read the file");
    let slice = unsafe { memmap2::Mmap::map(&file).unwrap() };

    println!("init");
    let tinit = Instant::now();
    let cores: usize = std::thread::available_parallelism().unwrap().into();
    let chunk_size = slice.len() / cores;
    let mut chunks: Vec<(usize, usize)> = vec![];
    let mut start = 0;
    for _ in 0..cores {
        let end = (start + chunk_size).min(slice.len());
        let next_new_line = match memchr::memchr(b'\n', &slice[end..]) {
            Some(v) => v,
            None => {
                assert_eq!(end, slice.len());
                0
            }
        };
        let end = end + next_new_line;
        chunks.push((start, end));
        start = end + 1;
    }

    println!("init took {} micros", tinit.elapsed().as_micros());
    println!("par");
    let tpar = Instant::now();
    let parts: Vec<_> = chunks
        .par_iter()
        .map(|(start, end)| PromiseSafe(make_map(&mut &slice[*start..*end])))
        .collect();

    println!("par took {} millis", tpar.elapsed().as_millis());
    println!("fold");
    let tfold = Instant::now();
    let m: BytesTrieMap<()> = parts.into_par_iter().reduce(|| PromiseSafe(BytesTrieMap::new()), |a, b| {
        PromiseSafe(a.0.join(&b.0))
    }).0;
    println!("fold took {} millis", tfold.elapsed().as_millis());
    println!("map contains: {}", m.val_count());
}
*/
/*
init took 388 micros
par took 4604 millis
fold took 11076 millis
map contains: 344777665
Command being timed: "../../../target/release/bucket_map"
User time (seconds): 461.48
System time (seconds): 62.26
Percent of CPU this job got: 580%
Elapsed (wall clock) time (h:mm:ss or m:ss): 1:30.25
Average shared text size (kbytes): 0
Average unshared data size (kbytes): 0
Average stack size (kbytes): 0
Average total size (kbytes): 0
Maximum resident set size (kbytes): 105628636
Average resident set size (kbytes): 0
Major (requiring I/O) page faults: 0
Minor (reclaiming a frame) page faults: 20229729
Voluntary context switches: 55613
Involuntary context switches: 13194
*/
/*** bucket-map interning, multi-threaded ***/

struct PromiseSafe(BytesTrieMap<()>);

unsafe impl Send for PromiseSafe {}

struct ParDataParser<'a> { count: u64, buf: [u8; 8], write_permit: WritePermit<'a> }

impl <'a> Parser for ParDataParser<'a> {
    fn tokenizer<'r>(&mut self, s: &[u8]) -> &'r [u8] {
        self.count += 1;
        // FIXME hack until either the parser is rewritten or we can take a pointer of the symbol
        self.buf = self.write_permit.get_sym_or_insert(s);
        return unsafe { std::mem::transmute(&self.buf[..]) };
    }
}

impl <'a> ParDataParser<'a> {
    fn new(handle: &'a SharedMappingHandle) -> Self {
        Self {
            count: 3,
            buf: (3u64).to_be_bytes(),
            write_permit: handle.try_aquire_permission().unwrap()
        }
    }
}

fn make_map<'a>(handle: &'a SharedMappingHandle, slice: &[u8]) -> BytesTrieMap<()> {
    let mut btm: BytesTrieMap<()> = BytesTrieMap::new();
    let mut it = ParseContext::new(slice);
    let mut parser = ParDataParser::new(handle);
    #[allow(unused_variables)]
    let mut i = 0;
    let mut stack = [0; 2 << 19];
    loop {
        let mut ez = ExprZipper::new(Expr{ptr: stack.as_mut_ptr()});
        match parser.sexpr_(&mut it, &mut ez) {
            Ok(()) => { btm.insert(&stack[..ez.loc], ()); }
            Err(err) => {
                if err.error_type == ParserErrorType::InputFinished{
                    break
                } else {
                    panic!("{:?}", err)
                }
            }
        }
        i += 1;
    }
    // println!("inserted {}, symbols {}", i, parser.count - 3);
    btm
}

fn main() {
    // let filepath = "/run/media/adam/43323a1c-ad7e-4d9a-b3c0-cf84e69ec61a/awesome-biomedical-kg/ckg_v3/kg_properties_aggregated.metta";
    let filepath = "/home/adam/Projects/MORK/frontend/resources/edges67458171.metta";
    let file = std::fs::File::open(filepath)
        .expect("Should have been able to read the file");
    let slice = unsafe { memmap2::Mmap::map(&file).unwrap() };

    println!("init");
    let tinit = Instant::now();
    let handle = SharedMapping::new();
    let cores: usize = std::thread::available_parallelism().unwrap().into();
    let chunk_size = slice.len() / cores;
    let mut chunks: Vec<(usize, usize, SharedMappingHandle)> = vec![];
    let mut start = 0;
    for _ in 0..cores {
        let end = (start + chunk_size).min(slice.len());
        let next_new_line = match memchr::memchr(b'\n', &slice[end..]) {
            Some(v) => v,
            None => {
                assert_eq!(end, slice.len());
                0
            }
        };
        let end = end + next_new_line;
        chunks.push((start, end, handle.clone()));
        start = end + 1;
    }

    println!("init took {} micros", tinit.elapsed().as_micros());
    println!("par");
    let tpar = Instant::now();
    let parts: Vec<_> = chunks
        .par_iter()
        .map(|(start, end, handle)| PromiseSafe(make_map(handle, &mut &slice[*start..*end])))
        .collect();

    println!("par took {} millis", tpar.elapsed().as_millis());
    println!("fold");
    let tfold = Instant::now();
    let m: BytesTrieMap<()> = parts.into_par_iter().reduce(|| PromiseSafe(BytesTrieMap::new()), |a, b| {
        PromiseSafe(a.0.join(&b.0))
    }).0;
    println!("fold took {} millis", tfold.elapsed().as_millis());
    println!("map contains: {}", m.val_count());
}

/*
init took 482 micros
par took 29410 millis
fold took 18362 millis
map contains: 344777665
Command being timed: "../../../target/release/bucket_map"
User time (seconds): 2123.51
System time (seconds): 858.15
Percent of CPU this job got: 2147%
Elapsed (wall clock) time (h:mm:ss or m:ss): 2:18.86
Average shared text size (kbytes): 0
Average unshared data size (kbytes): 0
Average stack size (kbytes): 0
Average total size (kbytes): 0
Maximum resident set size (kbytes): 117762876
Average resident set size (kbytes): 0
Major (requiring I/O) page faults: 0
Minor (reclaiming a frame) page faults: 24184549
Voluntary context switches: 20251815
Involuntary context switches: 854191
 */
/*** naive-map interning, multi-threaded ***/
/*
struct PromiseSafe(BytesTrieMap<()>);

unsafe impl Send for PromiseSafe {}

struct ParDataParser<'a> { count: u64, buf: [u8; 8], write_permit: naive_map::WritePermit<'a> }

impl <'a> Parser for ParDataParser<'a> {
    fn tokenizer<'r>(&mut self, s: &[u8]) -> &'r [u8] {
        self.count += 1;
        // FIXME hack until either the parser is rewritten or we can take a pointer of the symbol
        self.buf = (self.write_permit.get_sym_or_insert(s) as u64).to_be_bytes();
        return unsafe { std::mem::transmute(&self.buf[..]) };
    }
}

impl <'a> ParDataParser<'a> {
    fn new(handle: &'a naive_map::SharedMappingHandle) -> Self {
        Self {
            count: 3,
            buf: (3u64).to_be_bytes(),
            write_permit: handle.try_aquire_permission().unwrap()
        }
    }
}

fn make_map<'a>(handle: &'a naive_map::SharedMappingHandle, slice: &[u8]) -> BytesTrieMap<()> {
    let mut btm: BytesTrieMap<()> = BytesTrieMap::new();
    let mut it = Context::new(slice);
    let mut parser = ParDataParser::new(handle);
    let mut i = 0;
    let mut stack = [0; 2 << 19];
    loop {
        unsafe {
            let mut ez = ExprZipper::new(Expr{ptr: stack.as_mut_ptr()});
            match parser.sexpr(&mut it, &mut ez) {
                Ok(()) => { btm.insert(&stack[..ez.loc], ()); }
                Err(ParserError::InputFinished) => { break }
                Err(other) => { panic!("{:?}", other) }
            }
            i += 1;
            it.variables.clear();
        }
    }
    // println!("inserted {}, symbols {}", i, parser.count - 3);
    btm
}

fn main() {
    let filepath = "/run/media/adam/2c0662f2-6bf7-4afb-8c8b-a9e645f31bc6/bmkg/ckg_v3/results/kg_properties_aggregated.metta";
    let mut file = std::fs::File::open(filepath)
        .expect("Should have been able to read the file");
    let slice = unsafe { memmap2::Mmap::map(&file).unwrap() };

    println!("init");
    let tinit = Instant::now();
    let handle = naive_map::SharedMapping::new();
    let cores: usize = std::thread::available_parallelism().unwrap().into();
    let chunk_size = slice.len() / cores;
    let mut chunks: Vec<(usize, usize, naive_map::SharedMappingHandle)> = vec![];
    let mut start = 0;
    for _ in 0..cores {
        let end = (start + chunk_size).min(slice.len());
        let next_new_line = match memchr::memchr(b'\n', &slice[end..]) {
            Some(v) => v,
            None => {
                assert_eq!(end, slice.len());
                0
            }
        };
        let end = end + next_new_line;
        chunks.push((start, end, handle.clone()));
        start = end + 1;
    }

    println!("init took {} micros", tinit.elapsed().as_micros());
    println!("par");
    let tpar = Instant::now();
    let parts: Vec<_> = chunks
        .par_iter()
        .map(|(start, end, handle)| PromiseSafe(make_map(handle, &mut &slice[*start..*end])))
        .collect();

    println!("par took {} millis", tpar.elapsed().as_millis());
    println!("fold");
    let tfold = Instant::now();
    let m: BytesTrieMap<()> = parts.into_par_iter().reduce(|| PromiseSafe(BytesTrieMap::new()), |a, b| {
        PromiseSafe(a.0.join(&b.0))
    }).0;
    println!("fold took {} millis", tfold.elapsed().as_millis());
    println!("map contains: {}", m.val_count());
}
*/
/*
init took 423 micros
par took 1324043 millis
fold took 18436 millis
map contains: 344777665
Command being timed: "../../../target/release/bucket_map"
User time (seconds): 3957.11
System time (seconds): 158467.07
Percent of CPU this job got: 11054%
Elapsed (wall clock) time (h:mm:ss or m:ss): 24:29.30
Average shared text size (kbytes): 0
Average unshared data size (kbytes): 0
Average stack size (kbytes): 0
Average total size (kbytes): 0
Maximum resident set size (kbytes): 119486804
Average resident set size (kbytes): 0
Major (requiring I/O) page faults: 0
Minor (reclaiming a frame) page faults: 26026208
Voluntary context switches: 1356187
Involuntary context switches: 2302661
*/
