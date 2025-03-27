// use std::future::Future;
// use std::task::Poll;
use std::time::Instant;
use mork::space::Space;

// Remy : Adam, You seem does not seem to like using the test framework for benchmarks, I'm sure you have reasons.
//        I'd like to avoid breaking your code on refactoring, I'm sure there is a more elegant solution using conditional compilation,
//        but in the meantime, I've put this basic framework in place so that your code will not silently break.

/// change this to choice your benchmark
const BENCH : usize = 2;
fn main() {
    match BENCH {
        0 => bench_0(),
        1 => bench_1(),
        2 => bench_2(),
        _ => panic!("no more benchmark tests")
    }
}

fn bench_0() {
    let mut s = Space::new();
    let t0 = Instant::now();
    let nodesf = std::fs::File::open("/run/media/adam/43323a1c-ad7e-4d9a-b3c0-cf84e69ec61a/awesome-biomedical-kg/ckg_v3-002/results/nodes.json").unwrap();
    let nodesfs = unsafe { memmap2::Mmap::map(&nodesf).unwrap() };
    let loaded = s.load_json( unsafe { std::str::from_utf8_unchecked(nodesfs.as_ref()) }).unwrap();
    println!("loaded {} nodes in {} seconds", loaded, t0.elapsed().as_secs());
    let t1 = Instant::now();
    let edgesf = std::fs::File::open("/run/media/adam/43323a1c-ad7e-4d9a-b3c0-cf84e69ec61a/awesome-biomedical-kg/ckg_v3-002/results/edges.json").unwrap();
    let edgesfs = unsafe { memmap2::Mmap::map(&edgesf).unwrap() };
    let loaded = s.load_json( unsafe { std::str::from_utf8_unchecked( edgesfs.as_ref() )}).unwrap();
    println!("loaded {} edges in {} seconds", loaded, t1.elapsed().as_secs());
    done(&s);
}


fn bench_1() {
    let mut s = Space::new();
    let t0 = Instant::now();
    let nodesf = std::fs::File::open("/run/media/adam/43323a1c-ad7e-4d9a-b3c0-cf84e69ec61a/awesome-biomedical-kg/ckg_v3-002/results/nodes.json").unwrap();
    let nodesfs = unsafe { memmap2::Mmap::map(&nodesf).unwrap() };
    let loaded = s.load_json( unsafe { std::str::from_utf8_unchecked(nodesfs.as_ref()) }).unwrap();
    println!("loaded {} nodes in {} seconds", loaded, t0.elapsed().as_secs());
    let t1 = Instant::now();
    let edgesf = std::fs::File::open("/run/media/adam/43323a1c-ad7e-4d9a-b3c0-cf84e69ec61a/awesome-biomedical-kg/ckg_v3-002/results/edges.json").unwrap();
    let edgesfs = unsafe { memmap2::Mmap::map(&edgesf).unwrap() };
    let loaded = s.load_json( unsafe { std::str::from_utf8_unchecked( edgesfs.as_ref() )}).unwrap();
    println!("loaded {} edges in {} seconds", loaded, t1.elapsed().as_secs());
    done(&s);
}

const TEST_DAG : bool = false;
fn bench_2() {
    let mut s = Space::new();

    let restore_symbols_start = Instant::now();
    println!("resoted symbols {:?}", s.restore_symbols("/dev/shm/combined.symbols.zip").unwrap());
    println!("symbols backup took {}", restore_symbols_start.elapsed().as_secs());
    println!("{:?}", s.sm.get_sym(b"SPO"));

    let restore_paths_start = Instant::now();
    println!("restored paths {:?}", s.restore_paths("/dev/shm/combined.paths.gz").unwrap());
    println!("paths restore took {}", restore_paths_start.elapsed().as_secs());
    s.statistics();
    
    #[cfg(feature="neo4j")]
    #[allow(unused)]
    if TEST_DAG {

        let restore_start = Instant::now();
        s.restore_from_dag("/dev/shm/");
        println!("restore took {}", restore_start.elapsed().as_secs());
        s.statistics();
    
    
        let property_load_start = Instant::now();
        println!("{:?}", s.load_neo4j_node_properties("bolt://localhost:7687", "neo4j", "morkwork").unwrap());
        println!("property loading took {}", property_load_start.elapsed().as_secs());
        s.statistics();
        
        let load_start = Instant::now();
        s.load_neo4j_triples("bolt://localhost:7687", "neo4j", "morkwork");
        println!("loading took {}", load_start.elapsed().as_secs());
        s.statistics();
    
        // edges 331291528
        // nodes 76683739
        // props 567148252
        // paths 898439780
    
    
        let backup_start = Instant::now();
        s.backup_as_dag("/dev/shm/combined.remydag");
        println!("backup took {}", backup_start.elapsed().as_secs());
    
        let backup_paths_start = Instant::now();
        s.backup_paths("/dev/shm/combined.paths.gz");
        println!("paths backup took {}", backup_paths_start.elapsed().as_secs());
        
        let backup_symbols_start = Instant::now();
        s.backup_symbols("/dev/shm/combined.symbols.zip");
        println!("symbols backup took {}", backup_symbols_start.elapsed().as_secs());
    }
}

#[allow(unused_variables)]
pub fn done(s : &Space) -> ! {
    // let inner = s.inner_map_as_ref();
    // let counters = pathmap::counters::Counters::count_ocupancy(inner);
    // counters.print_histogram_by_depth();
    // counters.print_run_length_histogram();
    // counters.print_list_node_stats();
    // println!("#symbols {}", self.sm.symbol_count());
    std::process::exit(0)
}