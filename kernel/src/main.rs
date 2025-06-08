// // use std::future::Future;
// // use std::task::Poll;
// use std::time::Instant;
// use pathmap::zipper::{ZipperIteration, ZipperMoving, ZipperReadOnlyValues};
// use mork::{expr, Space};
// use mork::space::DefaultSpace;

// // Remy : Adam, You seem does not seem to like using the test framework for benchmarks, I'm sure you have reasons.
// //        I'd like to avoid breaking your code on refactoring, I'm sure there is a more elegant solution using conditional compilation,
// //        but in the meantime, I've put this basic framework in place so that your code will not silently break.

// /// change this to choice your benchmark
// const BENCH : usize = 2;
// fn main() {
//     match BENCH {
//         0 => bench_0(),
//         1 => bench_1(),
//         2 => bench_2(),
//         3 => bench_3(),
//         4 => bench_4(),
//         5 => bench_5(),
//         _ => panic!("no more benchmark tests")
//     }
// }

// fn bench_0() {
//     let mut s = DefaultSpace::new();
//     let t0 = Instant::now();
//     let nodesf = std::fs::File::open("/run/media/adam/43323a1c-ad7e-4d9a-b3c0-cf84e69ec61a/awesome-biomedical-kg/ckg_v3-002/results/nodes.json").unwrap();
//     let nodesfs = unsafe { memmap2::Mmap::map(&nodesf).unwrap() };
//     let loaded = s.load_json( unsafe { std::str::from_utf8_unchecked(nodesfs.as_ref()) }).unwrap();
//     println!("loaded {} nodes in {} seconds", loaded, t0.elapsed().as_secs());
//     let t1 = Instant::now();
//     let edgesf = std::fs::File::open("/run/media/adam/43323a1c-ad7e-4d9a-b3c0-cf84e69ec61a/awesome-biomedical-kg/ckg_v3-002/results/edges.json").unwrap();
//     let edgesfs = unsafe { memmap2::Mmap::map(&edgesf).unwrap() };
//     let loaded = s.load_json( unsafe { std::str::from_utf8_unchecked( edgesfs.as_ref() )}).unwrap();
//     println!("loaded {} edges in {} seconds", loaded, t1.elapsed().as_secs());
//     done(&s);
// }


// <<<<<<< HEAD
// fn bench_1() {
//     let mut s = DefaultSpace::new();
//     let t0 = Instant::now();
//     let nodesf = std::fs::File::open("/run/media/adam/43323a1c-ad7e-4d9a-b3c0-cf84e69ec61a/awesome-biomedical-kg/ckg_v3-002/results/nodes.json").unwrap();
//     let nodesfs = unsafe { memmap2::Mmap::map(&nodesf).unwrap() };
//     let loaded = s.load_json( unsafe { std::str::from_utf8_unchecked(nodesfs.as_ref()) }).unwrap();
//     println!("loaded {} nodes in {} seconds", loaded, t0.elapsed().as_secs());
//     let t1 = Instant::now();
//     let edgesf = std::fs::File::open("/run/media/adam/43323a1c-ad7e-4d9a-b3c0-cf84e69ec61a/awesome-biomedical-kg/ckg_v3-002/results/edges.json").unwrap();
//     let edgesfs = unsafe { memmap2::Mmap::map(&edgesf).unwrap() };
//     let loaded = s.load_json( unsafe { std::str::from_utf8_unchecked( edgesfs.as_ref() )}).unwrap();
//     println!("loaded {} edges in {} seconds", loaded, t1.elapsed().as_secs());
//     done(&s);
// }
// fn work(s: &mut DefaultSpace) {
// =======
// // fn main() {
// //     let mut s = Space::new();
// //     let t0 = Instant::now();
// //     let nodesf = std::fs::File::open("/run/media/adam/43323a1c-ad7e-4d9a-b3c0-cf84e69ec61a/awesome-biomedical-kg/ckg_v3-002/results/nodes.json").unwrap();
// //     let nodesfs = unsafe { memmap2::Mmap::map(&nodesf).unwrap() };
// //     let loaded = s.load_json(nodesfs.as_ref()).unwrap();
// //     println!("loaded {} nodes in {} seconds", loaded, t0.elapsed().as_secs());
// //     let t1 = Instant::now();
// //     let edgesf = std::fs::File::open("/run/media/adam/43323a1c-ad7e-4d9a-b3c0-cf84e69ec61a/awesome-biomedical-kg/ckg_v3-002/results/edges.json").unwrap();
// //     let edgesfs = unsafe { memmap2::Mmap::map(&edgesf).unwrap() };
// //     let loaded = s.load_json(edgesfs.as_ref()).unwrap();
// //     println!("loaded {} edges in {} seconds", loaded, t1.elapsed().as_secs());
// //     s.done();
// // }

// fn work(s: &mut Space) {
//     let restore_paths_start = Instant::now();
//     println!("restored paths {:?}", s.restore_paths("/dev/shm/combined_ni.paths.gz").unwrap());
//     println!("paths restore took {}", restore_paths_start.elapsed().as_secs());
//     s.statistics();

// >>>>>>> main
//     let add_gene_name_index_start = Instant::now();
//     s.transform(expr!(s, "[4] NKV $ gene_name $"), expr!(s, "[3] gene_name_of _2 _1"));
//     println!("add gene name index took {} ms", add_gene_name_index_start.elapsed().as_millis());
//     s.statistics();

//     let all_related_to_gene_start = Instant::now();
//     s.transform_multi(&[
//         expr!(s, "[3] gene_name_of TP73-AS1 $"),
//         expr!(s, "[4] SPO _1 includes $"),
//         expr!(s, "[4] SPO _1 transcribed_from $"),
//     ], expr!(s, "[4] res0 _1 _2 _3"));
//     println!("all_related_to_gene_start {}", all_related_to_gene_start.elapsed().as_micros());
//     let mut count = 0;
//     s.query(expr!(s, "[4] res0 $ $ $"), |_, e| {
//         // println!("{}", sexpr!(s, e));
//         count += 1
//     });
//     println!("res0 count {}", count);

//     let add_exon_chr_index_start = Instant::now();
//     s.transform(expr!(s, "[4] NKV $ chr $"), expr!(s, "[3] chr_of _2 _1"));
//     println!("add exon chr index took {}", add_exon_chr_index_start.elapsed().as_secs());
//     s.statistics();

//     let ops_index_start = Instant::now();
//     s.transform(expr!(s, "[4] SPO $ $ $"), expr!(s, "[4] OPS _3 _2 _1"));
//     println!("add ops index took {}", ops_index_start.elapsed().as_secs());
//     s.statistics();

//     let transitive_chr1_start = Instant::now();
//     s.transform_multi(&[
//         expr!(s, "[3] chr_of chr1 $"),
//         expr!(s, "[4] OPS _1 includes $"),
//         expr!(s, "[4] SPO _2 translates_to $"),
//         expr!(s, "[4] OPS _3 interacts_with $"),
//     ], expr!(s, "[5] res1 _1 _2 _3 _4"));
//     println!("transitive_chr1 {} ms", transitive_chr1_start.elapsed().as_millis());
//     let mut count = 0;
//     s.query(expr!(s, "[5] res1 $ $ $ $"), |_, e| {
//         // println!("{}", sexpr!(s, e));
//         count += 1
//     });
//     println!("res1 count {}", count);

//     let q0_start = Instant::now();
//     s.transform_multi(&[
//         expr!(s, "[3] gene_name_of BRCA2 $"),
//         expr!(s, "[4] SPO _1 transcribed_to $"),
//         expr!(s, "[4] SPO _2 translates_to $"),
//         expr!(s, "[4] OPS _3 interacts_with $"),
//         expr!(s, "[4] SPO _1 genes_pathways $"),
//     ], expr!(s, "[6] res2 _1 _2 _3 _4 _5"));
//     println!("q0 {}", q0_start.elapsed().as_micros());
//     let mut count = 0;
//     s.query( expr!(s, "[6] res2 $ $ $ $ $"), |_, e| {
//         // println!("{}", sexpr!(s, e));
//         count += 1
//     });
//     println!("res2 count {}", count);

// }
// fn bench_2() {
//     const sexpr_contents: &str = r#"(Duck Quack)
//     (Human BlaBla)"#;
    
//     let mut s = DefaultSpace::new();
    
//     s.load_sexpr_simple(sexpr_contents.as_bytes(),
//                  expr!(s, "[2] $ $"),
//                  expr!(s, "[2] root [2] Sound [2] Sound [2] _1 _2")).unwrap();
    
//     s.transform_multi_multi_simple(
//         &[expr!(s, "[2] root [2] Sound [2] Sound [2] $ $")],
//         &[expr!(s, "[2] root [2] Output [5] The _1 makes sounds _2")]
//     );
    
//     let mut v = vec![];
//     s.dump_sexpr(expr!(s, "$"), expr!(s, "_1"), &mut v).unwrap();
    
//     println!("{}", String::from_utf8(v).unwrap());
//     return;

// <<<<<<< HEAD
// }

// fn bench_3() {
//         let mut s = DefaultSpace::new();
//     const space: &str = r#"
// (exec PC0 (, (? $channel $payload $body) (! $channel $payload) (exec PC0 $p $t)) (, $body (exec PC0 $p $t)))
// (exec PC1 (, (| $lprocess $rprocess) (exec PC1 $p $t)) (, $lprocess $rprocess (exec PC1 $p $t)))
// =======
// const work_mm2: &str = r#"
// (exec P0 (, (NKV $x gene_name $y)) (,) (, (gene_name_of $y $x)))
// (exec P0' (,) (, (MICROS $t) (U64.DIV $t 1000 $tms)) (, (time "add gene name index" $tms ms)))
// >>>>>>> main

// (exec P1 (, (gene_name_of TP73-AS1 $x)
//             (SPO $x includes $y)
//             (SPO $x transcribed_from $z)) (,) (, (res0 $x $y $z))))
// (exec P1' (,) (, (MICROS $t)) (, (time "all related to gene" $t us)))
// (exec P1'' (, (res0 $x $y $z)) (, (COUNT (res0 $x $y $z))) (, (count "query TP73-AS1" $c)))
// (exec P1''' (,) (, (MICROS $t)) (, (time "query TP73-AS1" $t us)))

// (exec P2 (, (NKV $x chr $y)) (,) (, (chr_of $y $x)))
// (exec P2' (,) (, (MICROS $t)) (, (time "add exon chr index" $t us)))

// (exec P3 (, (SPO $s $p $o)) (,) (, (OPS $o $p $s)))
// (exec P3' (,) (, (MICROS $t)) (, (time "add exon chr index" $t us)))

// (exec P4 (, (chr_of chr1 $x)
//             (OPS $x includes $y)
//             (SPO $y transcribed_from $z)
//             (OPS $z transcribed_from $w)) (,) (, (res1 $x $y $z $w))))
// (exec P4' (,) (, (MICROS $t)) (, (time "all related to gene" $t us)))
// (exec P4'' (, (res1 $x $y $z $w)) (, (COUNT (res1 $x $y $z $w))) (, (count "query chr1" $c)))
// (exec P4''' (,) (, (MICROS $t)) (, (time "query chr1" $t us)))

// (exec P5 (, (gene_name_of BRCA2 $x)
//             (SPO $x transcribed_to $y)
//             (SPO $y translates_to $z)
//             (OPS $z interacts_with $p)
//             (SPO $x genes_pathways $q)) (,) (, (res2 $x $y $z $p $q))))
// (exec P5' (,) (, (MICROS $t)) (, (time "all related to gene" $t us)))
// (exec P5'' (, (res2 $x $y $z $p $q)) (, (COUNT (res2 $x $y $z $p $q))) (, (count "query BRCA2" $c)))
// (exec P5''' (,) (, (MICROS $t)) (, (time "query BRCA2" $t us)))
// "#;
// <<<<<<< HEAD
    
//     s.load_sexpr_simple(space.as_bytes(), expr!(s, "$"), expr!(s, "_1")).unwrap();
// =======
// >>>>>>> main

// fn work_mm2_run() {
//     let mut s = Space::new();
//     let restore_paths_start = Instant::now();
//     println!("restored paths {:?}", s.restore_paths("/dev/shm/combined_ni.paths.gz").unwrap());
//     println!("paths restore took {}", restore_paths_start.elapsed().as_secs());
//     s.statistics();

//     s.metta_calculus();

//     let backup_paths_start = Instant::now();
//     println!("{:?}", s.backup_paths("/run/media/adam/43323a1c-ad7e-4d9a-b3c0-cf84e69ec61a/whole_flybase.paths.gz").unwrap());
//     println!("paths backup took {}", backup_paths_start.elapsed().as_secs());
// }

// /*
// paths restore took 135
//  978700221 atoms
// add gene name index took 8637 ms
//  979015756 atoms
// query TP73-AS1
//  193 µs
//  142
// add exon chr index took 32 s
//  1054962128 atoms
// add ops index took 91 s
//  1386253656 atoms
// query chr1
//  7691 ms
//  40172978 atoms
// query BRCA2
//  33295 µs
//  151956 atoms
//  */

// fn basic() {
//     let mut s = Space::new();

//     const space: &str = r#"
// (Straight 1 2)
// (Straight 2 3)

// (exec P1 (, (Straight $x $y) (Straight $y $z)) (, (Transitive $x $z)))

// (exec P2 (, (Transitive $x $y)) (, (Line $x $q)))
// (exec P2 (, (Transitive $x $y)) (, (Line $q $y)))

// "#;
//     // (exec (P0 reverse) (, (Straight $x $y) (exec (P0 reverse) $P $T)) (, (Reverse $y $x) (pexec (P0 reverse) $P $T)))
//     //
//     // (exec P1 (, (Straight $x $y) (Straight $y $z)) (, (Transitive $x $z)))
//     //

//     s.load_sexpr(space.as_bytes(), expr!(s, "$"), expr!(s, "_1")).unwrap();

//     s.metta_calculus();

//     let mut v = vec![];
//     s.dump_sexpr(expr!(s, "$"), expr!(s, "_1"), &mut v).unwrap();

//     println!("out {}", String::from_utf8(v).unwrap());


// }

// fn main() {
//     env_logger::init();

//     // basic();
//     // return;

//     let mut s = Space::new();
//     const space: &str = r#"
// (exec P0 (, (sudoku p2 input (row ($r $x1 $x2 $x3 $x4 $x5 $x6 $x7 $x8 $x9)))) 
//          (, (cell 1 $r $x1) (cell 2 $r $x2) (cell 3 $r $x3)  (cell 4 $r $x4) (cell 5 $r $x5) (cell 6 $r $x6)  (cell 7 $r $x7) (cell 8 $r $x8) (cell 9 $r $x9)  ))

// (exec P1 (, (cell $c $r _))
//          (, (cell $c $r 1) (cell $c $r 2) (cell $c $r 3)  (cell $c $r 4) (cell $c $r 5) (cell $c $r 6)  (cell $c $r 7) (cell $c $r 8) (cell $c $r 9)  ))

// (exec P2 (, (cell $ca $r $va) (cell $cb $r $vb))
//          (, (Deduction remaining (cell $ca $r $x) (cell $cb $r $y))))

// "#;
//     //
//     // (exec P2 (, (cell $ca $r $va) (cell $cb $r $vb))
//     // (, (Deduction remaining (cell $ca $r X) (cell $cb $r Y))))

//     // (exec P3 (, (cell $c $ra $va) (cell $c $rb $vb))
//     // (, (Deduction remaining (cell $c $ra X) (cell $c $rb Y))))
//     // 
//     // 
//     // (exec P4 (, (cell $c $ra $va) (cell $c $rb $vb))
//     // (, (Deduction remaining (cell $c $ra $x) (cell $c $rb $y))))
//     // (block 0 1 1) (block 0 1 2) (block 0 1 3)
//     // (block 0 2 1) (block 0 2 2) (block 0 2 3)
//     // (block 0 3 1) (block 0 3 2) (block 0 3 3)

//     const sudoku_p2: &str = r#"
// 1 2 3 4 5 6 7 8 9
// _ 5 _ _ _ _ 9 _ _
// _ _ _ 8 3 1 2 5 _
// 2 _ 7 _ _ _ 6 1 3
// 9 _ 6 _ _ 7 _ 3 _
// 1 2 8 _ _ _ 7 _ _
// _ _ _ 2 _ 4 _ 9 6
// 8 1 _ 7 6 _ _ 2 9
// 7 3 4 _ 2 8 _ _ 1
// _ _ _ 4 1 _ _ _ _"#;
    
//     s.load_csv(sudoku_p2.as_bytes(), expr!(s, "$"), expr!(s, "[4] sudoku p2 input [2] row _1"), b' ').unwrap();
    
//     s.load_sexpr(space.as_bytes(), expr!(s, "$"), expr!(s, "_1")).unwrap();

//     s.metta_calculus();
    
//     // println!("size {:?}", s.btm.val_count());
    
//     let mut v = vec![];
//     s.dump_sexpr(expr!(s, "$"), expr!(s, "_1"), &mut v).unwrap();
    
//     println!("{}", String::from_utf8(v).unwrap());
    
//     return;
//     /*let mut s = Space::new();
//     const space: &str = r#"
// (= (add (S $x) $y) (S (add $x $y)))
// (= (add Z $y) $y)
// (= (mul (S (S $x)) $y) (add $y (mul (S $x) $y)))
// (= (mul (S Z) $y) $y)
// (= (mul Z $y) Z)

// (PC (Cat (Point3D 39 9504 34980)))
// (PC (Cat (Point3D 39 9504 34980)))
// (PC (Cat (Point3D 39 9480 34980)))
// (PC (Cat (Point3D 39 4830 34980)))
// (PC (Cat (Point3D 39 9504 34980)))
// (PC (Cat (Point3D 39 3230 34923)))
// (PC (Cat (Point3D 27 3410 34900)))
// (PC (Cat (Point3D 27 3410 34964)))
// (PC (Cat (Point3D 23 3459 34932)))

// "#;

//     s.load_sexpr(space.as_bytes(), expr!(s, "$"), expr!(s, "_1")).unwrap();


//     let [(t1, _), (t2, _)] = &s.token_bfs(&[], expr!(s, "$"))[..] else { panic!() };
//     println!("{:?}", s.token_bfs(&t1[..], expr!(s, "$")));
//     println!("{:?}", s.token_bfs(t2, expr!(s, "$")));

//     // let mut v = vec![];
//     // s.dump_sexpr(expr!(s, "$"), expr!(s, "_1"), &mut v).unwrap();
//     //
//     // println!("{}", String::from_utf8(v).unwrap());
//     return;*/
//     /*

//     let mut s = Space::new();
//     const facts: &str = "0,1\n1,2\n2,3\n3,4\n4,5\n5,0\n5,6\n6,7\n7,8\n8,9\n9,10\n10,7";
//     const expected_same_clique: &str = "...";
//     const expected_reachable: &str = "...";


//     s.load_csv(facts.as_bytes(), expr!(s, "[2] $ $"), expr!(s, "[3] edge _1 _2")).unwrap();
//     */

//     // (reachable $x $y) :- (edge $x $y)
//     // (reachable $x $y) :- (edge $x $z), (reachable $z $y)
//     // (same_clique $x $y) :- (reachable $x $y), (reachable $y $x)
//     s.datalog(&[
//         expr!(s, "[3] -: [2] , [3] edge $ $ [3] reachable _1 _2"),
//         expr!(s, "[3] -: [3] , [3] edge $ $ [3] reachable _2 $ [3] reachable _1 _3"),
//         expr!(s, "[3] -: [3] , [3] reachable $ $ [3] reachable _2 _1 [3] same_clique _1 _2"),
//     ]);
// }

// fn bench_4() {
//     /*
//     s.load_sexpr(sexpr_contents.as_bytes(), expr!(s, "[2] useful $"), expr!(s, "[2] data [2] mysexpr _1")).unwrap();

//     let mut v = vec![];
//     s.dump_sexpr(expr!(s, "[2] data [2] mycsv $"), expr!(s, "_1"), &mut v).unwrap();

//     println!("{}", String::from_utf8(v).unwrap());
//     return;
//     */
//     // println!("{}", mork_bytestring::serialize(&[3, 3, 200, 84, 80, 55, 51, 45, 65, 83, 49, 204, 103, 101, 110, 101, 95, 110, 97, 109, 101, 95, 111, 102, 200, 0, 0, 0, 0, 4, 129, 29, 29, 4, 195, 83, 80, 79, 200, 0, 0, 0, 0, 4, 129, 29, 29, 200]));
//     //
// <<<<<<< HEAD
//     // return;
//     let mut s = DefaultSpace::new();

//     let everythingf = std::fs::File::open("/mnt/zram/whole_flybase.json").unwrap();
//     let everythingfs = unsafe { memmap2::Mmap::map(&everythingf).unwrap() };
//     let load_compressed = Instant::now();
//     println!("done {} {}", s.load_json( unsafe { std::str::from_utf8_unchecked(everythingfs.as_ref()) }).unwrap(), load_compressed.elapsed().as_secs());

//     let backup_paths_start = Instant::now();
//     println!("{:?}", s.backup_paths("/run/media/adam/43323a1c-ad7e-4d9a-b3c0-cf84e69ec61a/whole_flybase.paths.gz").unwrap());
//     println!("paths backup took {}", backup_paths_start.elapsed().as_secs());
// =======
//     return;
//     // let mut s = Space::new();

//     // let tree = pathmap::arena_compact::ArenaCompactTree::open_mmap("/run/media/adam/43323a1c-ad7e-4d9a-b3c0-cf84e69ec61a/whole_flybase.tree").unwrap();
//     // 
//     // let iter_tree_start = Instant::now();
//     // let mut rz = tree.read_zipper();
//     // let mut npaths = 0usize; 
//     // let mut nbytes = 0; 
//     // while rz.to_next_val() {
//     //     nbytes += rz.path().len();
//     //     npaths += 1;
//     //     if npaths % 10_000_000 == 0 {
//     //         println!("npaths {}", npaths);
//     //     }
//     // }
//     // println!("iterating tree backup {} {} took {}", npaths, nbytes, iter_tree_start.elapsed().as_secs());
    
//     // let restore_paths_start = Instant::now();
//     // let restored = s.restore_paths("/run/media/adam/43323a1c-ad7e-4d9a-b3c0-cf84e69ec61a/whole_flybase.paths.gz").unwrap();
//     // println!("restored paths {:?} {}", restored, restore_paths_start.elapsed().as_secs());
    
//     // let everythingf = std::fs::File::open("/run/media/adam/43323a1c-ad7e-4d9a-b3c0-cf84e69ec61a/whole_flybase.jsonl").unwrap();
//     // let everythingfs = unsafe { memmap2::Mmap::map(&everythingf).unwrap() };
//     // let load_compressed = Instant::now();
//     // println!("done {:?} {}", s.load_jsonl(everythingfs.as_ref()).unwrap(), load_compressed.elapsed().as_secs());
//     // // done (326728210, 6798095370) 1934s
//     // 
//     // let backup_paths_start = Instant::now();
//     // println!("{:?}", s.backup_paths("/run/media/adam/43323a1c-ad7e-4d9a-b3c0-cf84e69ec61a/whole_flybase.paths.gz").unwrap());
//     // println!("paths backup took {}", backup_paths_start.elapsed().as_secs());
//     // // SerializationStats { bytes_out: 42_741_214_528, bytes_in: 355_357_500_042, path_count: 6798095370 }
//     // //                                                           328_165_118_562
//     // // paths backup took 4619s
//     // 
//     // let backup_tree_start = Instant::now();
//     // println!("{:?}", s.backup_tree("/run/media/adam/43323a1c-ad7e-4d9a-b3c0-cf84e69ec61a/whole_flybase.tree").unwrap());
//     // println!("tree backup took {}", backup_tree_start.elapsed().as_secs());
//     // // tree backup took 3033
//     // 
//     // let backup_dag_start = Instant::now();
//     // println!("{:?}", s.backup("/run/media/adam/43323a1c-ad7e-4d9a-b3c0-cf84e69ec61a/").unwrap());
//     // println!("dag backup took {}", backup_dag_start.elapsed().as_secs());
// >>>>>>> main

// }
// const TEST_DAG : bool = false;
// fn bench_5() {

//     let mut s = DefaultSpace::new();

//     let restore_symbols_start = Instant::now();
//     println!("restored symbols {:?}", s.restore_symbols("/dev/shm/combined.symbols.zip").unwrap());
//     println!("symbols backup took {}", restore_symbols_start.elapsed().as_secs());
//     println!("{:?}", s.symbol_table().get_sym(b"SPO"));
//     println!("{:?}", s.symbol_table().get_sym(b"IL9R-207"));
//     let bucket_map::Tables { to_symbol, to_bytes } = s.symbol_table().reveal_tables();
//     println!("to_symbol.len() = {}; to_bytes.len() = {}", to_symbol.len(), to_bytes.len());
//     println!("to_symbol.first().unwrap().val_count() = {:?}; to_bytes.first().unwrap().val_count() = {:?}", to_symbol.last().unwrap().val_count(), to_bytes.last().unwrap().val_count());

//     // for to_symbol_part in to_symbol {
//     //     print!("{},", to_symbol_part.val_count());
//     // }

//     // for to_byte_part in to_bytes {
//     //     print!("{},", to_byte_part.val_count());
//     // }

//     let mut to_symbol_rz = to_symbol.last().unwrap().read_zipper();
//     while to_symbol_rz.to_next_val() {
//         let v = to_symbol_rz.get_value().unwrap();
//         println!("{:?} {:?}", std::str::from_utf8(to_symbol_rz.path()).unwrap_or(format!("{:?}", to_symbol_rz.path()).as_str()), v)
//     }
//     drop(to_symbol_rz);
//     drop(to_symbol);
//     drop(to_bytes);

//     let restore_paths_start = Instant::now();
//     println!("restored paths {:?}", s.restore_paths("/dev/shm/combined_ni.paths.gz").unwrap());
//     println!("paths restore took {}", restore_paths_start.elapsed().as_secs());
//     s.statistics();
    
//     #[cfg(feature="neo4j")]
//     #[allow(unused)]
//     if TEST_DAG {

//         // let restore_start = Instant::now();
//         // s.restore_from_dag("/dev/shm/");
//         // println!("restore took {}", restore_start.elapsed().as_secs());
//         // s.statistics();
    
    
//         // let property_load_start = Instant::now();
//         // println!("{:?}", s.load_neo4j_node_properties("bolt://localhost:7687", "neo4j", "morkwork").unwrap());
//         // println!("property loading took {}", property_load_start.elapsed().as_secs());
//         // s.statistics();

//         // let load_labels_start = Instant::now();
//         // println!("{:?}", s.load_neo4j_node_lables("bolt://localhost:7687", "neo4j", "morkwork").unwrap());
//         // println!("loading labels took {}", load_labels_start.elapsed().as_secs());
//         // s.statistics();
        
//         // let mut rz = s.btm.read_zipper_at_path(&[item_byte(Tag::Arity(4)), item_byte(Tag::SymbolSize(3)), b'S', b'P', b'O']);
//         // println!("SPO's {}", rz.val_count());
//         // rz.to_next_val();
//         // println!("{}", mork_bytestring::serialize(rz.origin_path()));
//         // drop(rz);
       
//         // let load_start = Instant::now();
//         // s.load_neo4j_triples("bolt://localhost:7687", "neo4j", "morkwork");
//         // println!("loading took {}", load_start.elapsed().as_secs());
//         // s.statistics();
    
//         // // edges 331291528
//         // // nodes 76683739
//         // // props 567148252
//         // // paths 898439780
    
    
//         // let backup_start = Instant::now();
//         // s.backup_as_dag("/dev/shm/combined.remydag");
//         // println!("backup took {}", backup_start.elapsed().as_secs());
    
//         // let backup_paths_start = Instant::now();
//         // s.backup_paths("/dev/shm/combined.paths.gz");
//         // println!("paths backup took {}", backup_paths_start.elapsed().as_secs());
        
//         // let backup_symbols_start = Instant::now();
//         // s.backup_symbols("/dev/shm/combined.symbols.zip");
//         // println!("symbols backup took {}", backup_symbols_start.elapsed().as_secs());
//     }
//     work(&mut s);
// }


// fn load_csv_with_pat() {
//     let csv_contents = r#"1,2
// 10,20
// 10,30"#;

//     let mut s = DefaultSpace::new();
//     // s.load_csv(csv_contents.as_bytes(), expr!(s, "[2] $ $"), expr!(s, "[2] mycsv [3] my precious _2")).unwrap();
//     s.load_csv_simple(csv_contents.as_bytes(), expr!(s, "[2] 10 $"), expr!(s, "[2] mycsv [3] my precious _1")).unwrap();

//     let mut v = vec![];
//     s.dump_sexpr(expr!(s, "$"), expr!(s, "_1"), &mut v).unwrap();

//     println!("{}", String::from_utf8(v).unwrap());
//     return;
// }

// #[allow(unused_variables)]
// pub fn done(s : &DefaultSpace) -> ! {
//     // let inner = s.inner_map_as_ref();
//     // let counters = pathmap::counters::Counters::count_ocupancy(inner);
//     // counters.print_histogram_by_depth();
//     // counters.print_run_length_histogram();
//     // counters.print_list_node_stats();
//     // println!("#symbols {}", self.sm.symbol_count());
//     std::process::exit(0)
// }
