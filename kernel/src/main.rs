// use std::future::Future;
// use std::task::Poll;
use std::time::Instant;
use pathmap::zipper::{ZipperAbsolutePath, ZipperIteration, ZipperMoving};
use mork_frontend::bytestring_parser::Parser;
use mork::{expr, sexpr};
use mork::prefix::Prefix;
use mork::space::Space;
use mork_bytestring::{item_byte, Tag};

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
fn work(s: &mut Space) {
    let add_gene_name_index_start = Instant::now();
    s.transform(expr!(s, "[4] NKV $ gene_name $"), expr!(s, "[3] gene_name_of _2 _1"));
    println!("add gene name index took {}", add_gene_name_index_start.elapsed().as_secs());
    s.statistics();

    let all_related_to_gene_start = Instant::now();
    s.transform_multi(&[
        expr!(s, "[3] gene_name_of TP73-AS1 $"),
        expr!(s, "[4] SPO _1 includes $"),
        expr!(s, "[4] SPO _1 transcribed_from $"),
    ], expr!(s, "[4] res0 _1 _2 _3"));
    println!("all_related_to_gene_start {}", all_related_to_gene_start.elapsed().as_micros());
    let mut count = 0;
    s.query(Prefix::NONE, expr!(s, "[4] res0 $ $ $"), |e| {
        println!("{}", sexpr!(s, e));
        count += 1
    });
    println!("res0 count {}", count);

    let add_exon_chr_index_start = Instant::now();
    s.transform(expr!(s, "[4] NKV $ chr $"), expr!(s, "[3] chr_of _2 _1"));
    println!("add exon chr index took {}", add_exon_chr_index_start.elapsed().as_secs());
    s.statistics();

    let ops_index_start = Instant::now();
    s.transform(expr!(s, "[4] SPO $ $ $"), expr!(s, "[4] OPS _3 _2 _1"));
    println!("add ops index took {}", ops_index_start.elapsed().as_secs());
    s.statistics();

    let transitive_chr1_start = Instant::now();
    s.transform_multi(&[
        expr!(s, "[3] chr_of chr1 $"),
        expr!(s, "[4] OPS _1 includes $"),
        expr!(s, "[4] SPO _2 translates_to $"),
        expr!(s, "[4] OPS _3 interacts_with $"),
    ], expr!(s, "[5] res1 _1 _2 _3 _4"));
    println!("transitive_chr1 {}", transitive_chr1_start.elapsed().as_micros());
    let mut count = 0;
    s.query(Prefix::NONE, expr!(s, "[5] res1 $ $ $ $"), |_| {
        // println!("{}", sexpr!(s, e));
        count += 1
    });
    println!("res1 count {}", count);

    let q0_start = Instant::now();
    s.transform_multi(&[
        expr!(s, "[3] gene_name_of BRCA2 $"),
        expr!(s, "[4] SPO _1 transcribed_to $"),
        expr!(s, "[4] SPO _2 translates_to $"),
        expr!(s, "[4] OPS _3 interacts_with $"),
        expr!(s, "[4] SPO _1 genes_pathways $"),
    ], expr!(s, "[6] res2 _1 _2 _3 _4 _5"));
    println!("q0 {}", q0_start.elapsed().as_micros());
    let mut count = 0;
    s.query(Prefix::NONE, expr!(s, "[6] res2 $ $ $ $ $"), |_| {
        // println!("{}", sexpr!(s, e));
        count += 1
    });
    println!("res2 count {}", count);

}
const TEST_DAG : bool = false;
fn bench_2() {


    // println!("{}", mork_bytestring::serialize(&[3, 3, 200, 84, 80, 55, 51, 45, 65, 83, 49, 204, 103, 101, 110, 101, 95, 110, 97, 109, 101, 95, 111, 102, 200, 0, 0, 0, 0, 4, 129, 29, 29, 4, 195, 83, 80, 79, 200, 0, 0, 0, 0, 4, 129, 29, 29, 200]));
    //
    // return;
    let mut s = Space::new();

    let restore_symbols_start = Instant::now();
    println!("restored symbols {:?}", s.restore_symbols("/dev/shm/combined.symbols.zip").unwrap());
    println!("symbols backup took {}", restore_symbols_start.elapsed().as_secs());
    println!("{:?}", s.sm.get_sym(b"SPO"));
    println!("{:?}", s.sm.get_sym(b"IL9R-207"));
    let bucket_map::serialization::Tables { to_symbol, to_bytes } = s.sm.reveal_tables();
    println!("to_symbol.len() = {}; to_bytes.len() = {}", to_symbol.len(), to_bytes.len());
    println!("to_symbol.first().unwrap().val_count() = {:?}; to_bytes.first().unwrap().val_count() = {:?}", to_symbol.last().unwrap().val_count(), to_bytes.last().unwrap().val_count());

    // for to_symbol_part in to_symbol {
    //     print!("{},", to_symbol_part.val_count());
    // }

    // for to_byte_part in to_bytes {
    //     print!("{},", to_byte_part.val_count());
    // }

    let mut to_symbol_rz = to_symbol.last().unwrap().read_zipper();
    while let Some(v) = to_symbol_rz.to_next_val() {
        println!("{:?} {:?}", std::str::from_utf8(to_symbol_rz.path()).unwrap_or(format!("{:?}", to_symbol_rz.path()).as_str()), v)
    }
    drop(to_symbol_rz);
    drop(to_symbol);
    drop(to_bytes);

    let restore_paths_start = Instant::now();
    println!("restored paths {:?}", s.restore_paths("/dev/shm/combined_ni.paths.gz").unwrap());
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

        let load_labels_start = Instant::now();
        println!("{:?}", s.load_neo4j_node_lables("bolt://localhost:7687", "neo4j", "morkwork").unwrap());
        println!("loading labels took {}", load_labels_start.elapsed().as_secs());
        s.statistics();
        
        let mut rz = s.btm.read_zipper_at_path(&[item_byte(Tag::Arity(4)), item_byte(Tag::SymbolSize(3)), b'S', b'P', b'O']);
        println!("SPO's {}", rz.val_count());
        rz.to_next_val();
        println!("{}", mork_bytestring::serialize(rz.origin_path().unwrap()));
        drop(rz);
       
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
    work(&mut s);
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