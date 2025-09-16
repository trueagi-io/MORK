use std::collections::HashSet;
// use std::future::Future;
// use std::task::Poll;
use std::time::Instant;
use pathmap::trie_map::BytesTrieMap;
use pathmap::zipper::{Zipper, ZipperAbsolutePath, ZipperIteration, ZipperMoving};
use mork_frontend::bytestring_parser::Parser;
use mork::{expr, prefix, sexpr};
use mork::prefix::Prefix;
use mork::space::{transitions, unifications, Space};
use mork_bytestring::{item_byte, Tag};
/*fn main() {
    let mut s = Space::new();
    let t0 = Instant::now();
    let nodesf = std::fs::File::open("/run/media/adam/43323a1c-ad7e-4d9a-b3c0-cf84e69ec61a/awesome-biomedical-kg/ckg_v3-002/results/nodes.json").unwrap();
    let nodesfs = unsafe { memmap2::Mmap::map(&nodesf).unwrap() };
    let loaded = s.load_json(nodesfs.as_ref()).unwrap();
    println!("loaded {} nodes in {} seconds", loaded, t0.elapsed().as_secs());
    let t1 = Instant::now();
    let edgesf = std::fs::File::open("/run/media/adam/43323a1c-ad7e-4d9a-b3c0-cf84e69ec61a/awesome-biomedical-kg/ckg_v3-002/results/edges.json").unwrap();
    let edgesfs = unsafe { memmap2::Mmap::map(&edgesf).unwrap() };
    let loaded = s.load_json(edgesfs.as_ref()).unwrap();
    println!("loaded {} edges in {} seconds", loaded, t1.elapsed().as_secs());
    s.done();
}*/


// fn main() {
//     let mut s = Space::new();
//     let t0 = Instant::now();
//     let nodesf = std::fs::File::open("/run/media/adam/43323a1c-ad7e-4d9a-b3c0-cf84e69ec61a/awesome-biomedical-kg/ckg_v3-002/results/nodes.json").unwrap();
//     let nodesfs = unsafe { memmap2::Mmap::map(&nodesf).unwrap() };
//     let loaded = s.load_json(nodesfs.as_ref()).unwrap();
//     println!("loaded {} nodes in {} seconds", loaded, t0.elapsed().as_secs());
//     let t1 = Instant::now();
//     let edgesf = std::fs::File::open("/run/media/adam/43323a1c-ad7e-4d9a-b3c0-cf84e69ec61a/awesome-biomedical-kg/ckg_v3-002/results/edges.json").unwrap();
//     let edgesfs = unsafe { memmap2::Mmap::map(&edgesf).unwrap() };
//     let loaded = s.load_json(edgesfs.as_ref()).unwrap();
//     println!("loaded {} edges in {} seconds", loaded, t1.elapsed().as_secs());
//     s.done();
// }

// fn work(s: &mut Space) {
//     let restore_paths_start = Instant::now();
//     println!("restored paths {:?}", s.restore_paths("/dev/shm/combined_ni.paths.gz").unwrap());
//     println!("paths restore took {}", restore_paths_start.elapsed().as_secs());
//     s.statistics();
//
//     let add_gene_name_index_start = Instant::now();
//     s.transform(expr!(s, "[4] NKV $ gene_name $"), expr!(s, "[3] gene_name_of _2 _1"));
//     println!("add gene name index took {} ms", add_gene_name_index_start.elapsed().as_millis());
//     s.statistics();
//
//     let all_related_to_gene_start = Instant::now();
//     s.transform_multi(&[
//         expr!(s, "[3] gene_name_of TP73-AS1 $"),
//         expr!(s, "[4] SPO _1 includes $"),
//         expr!(s, "[4] SPO _1 transcribed_from $"),
//     ], expr!(s, "[4] res0 _1 _2 _3"));
//     println!("all_related_to_gene_start {}", all_related_to_gene_start.elapsed().as_micros());
//     let mut count = 0;
//     s.query(expr!(s, "[4] res0 $ $ $"), |_, e| {
//         println!("{}", sexpr!(s, e));
//         count += 1
//     });
//     println!("res0 count {}", count);
//
//     let add_exon_chr_index_start = Instant::now();
//     s.transform(expr!(s, "[4] NKV $ chr $"), expr!(s, "[3] chr_of _2 _1"));
//     println!("add exon chr index took {}", add_exon_chr_index_start.elapsed().as_secs());
//     s.statistics();
//
//     let ops_index_start = Instant::now();
//     s.transform(expr!(s, "[4] SPO $ $ $"), expr!(s, "[4] OPS _3 _2 _1"));
//     println!("add ops index took {}", ops_index_start.elapsed().as_secs());
//     s.statistics();
//
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
//
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
//
// }

const work_mm2: &str = r#"
(exec P0 (, (NKV $x gene_name $y)) (,) (, (gene_name_of $y $x)))
(exec P0' (,) (, (MICROS $t) (U64.DIV $t 1000 $tms)) (, (time "add gene name index" $tms ms)))

(exec P1 (, (gene_name_of TP73-AS1 $x)
            (SPO $x includes $y)
            (SPO $x transcribed_from $z)) (,) (, (res0 $x $y $z))))
(exec P1' (,) (, (MICROS $t)) (, (time "all related to gene" $t us)))
(exec P1'' (, (res0 $x $y $z)) (, (COUNT (res0 $x $y $z))) (, (count "query TP73-AS1" $c)))
(exec P1''' (,) (, (MICROS $t)) (, (time "query TP73-AS1" $t us)))

(exec P2 (, (NKV $x chr $y)) (,) (, (chr_of $y $x)))
(exec P2' (,) (, (MICROS $t)) (, (time "add exon chr index" $t us)))

(exec P3 (, (SPO $s $p $o)) (,) (, (OPS $o $p $s)))
(exec P3' (,) (, (MICROS $t)) (, (time "add exon chr index" $t us)))

(exec P4 (, (chr_of chr1 $x)
            (OPS $x includes $y)
            (SPO $y transcribed_from $z)
            (OPS $z transcribed_from $w)) (,) (, (res1 $x $y $z $w))))
(exec P4' (,) (, (MICROS $t)) (, (time "all related to gene" $t us)))
(exec P4'' (, (res1 $x $y $z $w)) (, (COUNT (res1 $x $y $z $w))) (, (count "query chr1" $c)))
(exec P4''' (,) (, (MICROS $t)) (, (time "query chr1" $t us)))

(exec P5 (, (gene_name_of BRCA2 $x)
            (SPO $x transcribed_to $y)
            (SPO $y translates_to $z)
            (OPS $z interacts_with $p)
            (SPO $x genes_pathways $q)) (,) (, (res2 $x $y $z $p $q))))
(exec P5' (,) (, (MICROS $t)) (, (time "all related to gene" $t us)))
(exec P5'' (, (res2 $x $y $z $p $q)) (, (COUNT (res2 $x $y $z $p $q))) (, (count "query BRCA2" $c)))
(exec P5''' (,) (, (MICROS $t)) (, (time "query BRCA2" $t us)))
"#;

fn work_mm2_run() {
    let mut s = Space::new();
    let restore_paths_start = Instant::now();
    println!("restored paths {:?}", s.restore_paths("/dev/shm/combined_ni.paths.gz").unwrap());
    println!("paths restore took {}", restore_paths_start.elapsed().as_secs());
    s.statistics();

    s.metta_calculus(100);

    let backup_paths_start = Instant::now();
    println!("{:?}", s.backup_paths("/run/media/adam/43323a1c-ad7e-4d9a-b3c0-cf84e69ec61a/whole_flybase.paths.gz").unwrap());
    println!("paths backup took {}", backup_paths_start.elapsed().as_secs());
}

/*
paths restore took 135
 978700221 atoms
add gene name index took 8637 ms
 979015756 atoms
query TP73-AS1
 193 µs
 142
add exon chr index took 32 s
 1054962128 atoms
add ops index took 91 s
 1386253656 atoms
query chr1
 7691 ms
 40172978 atoms
query BRCA2
 33295 µs
 151956 atoms
 */

fn peano(x: usize) -> String {
    if x == 0 { "Z".to_string() }
    else { format!("(S {})", peano(x - 1)) }
}

fn basic() {
    let mut s = Space::new();

    const space: &str = r#"
(Straight 1 2)
(Straight 2 3)

(exec P1 (, (Straight $x $y) (Straight $y $z)) (, (Transitive $x $z)))

(exec P2 (, (Transitive $x $y)) (, (Line $x $q)))
(exec P2 (, (Transitive $x $y)) (, (Line $q $y)))

"#;
    // (exec (P0 reverse) (, (Straight $x $y) (exec (P0 reverse) $P $T)) (, (Reverse $y $x) (pexec (P0 reverse) $P $T)))
    //
    // (exec P1 (, (Straight $x $y) (Straight $y $z)) (, (Transitive $x $z)))
    //

    s.load_sexpr(space.as_bytes(), expr!(s, "$"), expr!(s, "_1")).unwrap();

    s.metta_calculus(100);

    let mut v = vec![];
    s.dump_sexpr(expr!(s, "$"), expr!(s, "_1"), &mut v);

    println!("out {}", String::from_utf8(v).unwrap());


}

fn bench_process_calculus(steps: usize, x: usize, y: usize) {
    let mut s = Space::new();

    // note 'idle' MM2-like statement that can be activated by moving it to the exec space
    let space_exprs = format!(r#"
(exec (IC 0 1 {})
               (, (exec (IC $x $y (S $c)) $sp $st)
                  ((exec $x) $p $t))
               (, (exec (IC $y $x $c) $sp $st)
                  (exec (R $x) $p $t)))

((exec 0)
      (, (petri (? $channel $payload $body))
         (petri (! $channel $payload)) )
      (, (petri $body)))
((exec 1)
      (, (petri (| $lprocess $rprocess)))
      (, (petri $lprocess)
         (petri $rprocess)))

(petri (? (add $ret) ((S $x) $y) (| (! (add (PN $x $y)) ($x $y))
                                    (? (PN $x $y) $z (! $ret (S $z)))  )  ))
(petri (? (add $ret) (Z $y) (! $ret $y)))
(petri (! (add result) ({} {})))
    "#, peano(steps), peano(x), peano(y));

    s.load_sexpr(space_exprs.as_bytes(), expr!(s, "$"), expr!(s, "_1")).unwrap();

    let t0 = Instant::now();
    let mcalc_steps = s.metta_calculus(1000000000000000); // big number to show the MM2 inference control working
    let elapsed = t0.elapsed();
    
    let mut v = vec![];
    // s.dump_all_sexpr(&mut v).unwrap();
    // We're only interested in the petri dish (not the state of exec), and specifically everything that was outputted `!` to `result`
    s.dump_sexpr(expr!(s, "[2] petri [3] ! result $"), expr!(s, "_1"), &mut v);
    let res = String::from_utf8(v).unwrap();

    println!("{x}+{y} ({} steps) in {} µs result: {res}", steps, elapsed.as_micros());
    assert_eq!(res, format!("{}\n", peano(x+y)));
    println!("unifications {}, transitions {}", unsafe { unifications }, unsafe { transitions });
    // (badbad)
    // 200+200 (1000 steps) in 42274298 µs
}

fn process_calculus_reverse() {
    let mut s = Space::new();

    // note 'idle' MM2-like statement that can be activated by moving it to the exec space
    const SPACE_EXPRS: &str = r#"
(exec (IC 0 1  (S (S (S (S (S (S (S (S (S (S Z)))))))))) )
               (, (exec (IC $x $y (S $c)) $sp $st)
                  ((exec $x) $p $t))
               (, (exec (IC $y $x $c) $sp $st)
                  (exec (R $x) $p $t)))

((exec 0)
      (, (petri (! $channel $payload))
         (petri (? $channel $payload $body)) )
      (, (petri $body)))
((exec 1)
      (, (petri (| $lprocess $rprocess)))
      (, (petri $lprocess)
         (petri $rprocess)))

(petri (? (add $ret) ((S $x) $y) (| (! (add (PN $x $y)) ($x $y))
                                    (? (PN $x $y) $z (! $ret (S $z)))  )  ))
(petri (? (add $ret) (Z $y) (! $ret $y)))
(petri (! (add result) ( (S (S Z)) (S (S Z)) )))
    "#;

    s.load_sexpr(SPACE_EXPRS.as_bytes(), expr!(s, "$"), expr!(s, "_1")).unwrap();

    let steps = s.metta_calculus(1000000000000000); // big number to show the MM2 inference control working

    let mut v = vec![];
    s.dump_sexpr(expr!(s, "[2] petri [3] ! result $"), expr!(s, "_1"), &mut v);
    let res = String::from_utf8(v).unwrap();

    println!("result: {res}");
    assert_eq!(res, "(S (S (S (S Z))))\n");
}

fn lookup() {
    let mut s = Space::new();

    const SPACE_EXPRS: &str = r#"
(exec 0 (, (Something (very specific))) (, MATCHED))

(Something (very specific))
    "#;

    s.load_all_sexpr(SPACE_EXPRS.as_bytes()).unwrap();

    let mut t0 = Instant::now();
    let steps = s.metta_calculus(1000000000000000);
    println!("elapsed {} steps {} size {}", t0.elapsed().as_millis(), steps, s.btm.val_count());

    let mut v = vec![];
    s.dump_all_sexpr(&mut v).unwrap();
    let res = String::from_utf8(v).unwrap();

    println!("result: {res}");
    assert!(res.contains("MATCHED\n"));
}

fn positive() {
    let mut s = Space::new();

    const SPACE_EXPRS: &str = r#"
(exec 0 (, (Something $unspecific)) (, MATCHED))

(Something (very specific))
    "#;

    s.load_all_sexpr(SPACE_EXPRS.as_bytes()).unwrap();

    let mut t0 = Instant::now();
    let steps = s.metta_calculus(1000000000000000);
    println!("elapsed {} steps {} size {}", t0.elapsed().as_millis(), steps, s.btm.val_count());

    let mut v = vec![];
    s.dump_all_sexpr(&mut v).unwrap();
    let res = String::from_utf8(v).unwrap();

    println!("result: {res}");
    assert!(res.contains("MATCHED\n"));
}

fn positive_equal() {
    let mut s = Space::new();

    const SPACE_EXPRS: &str = r#"
(exec 0 (, (Something $repeated $repeated)) (, MATCHED))

(Something (very specific) (very specific))
    "#;

    s.load_all_sexpr(SPACE_EXPRS.as_bytes()).unwrap();

    let mut t0 = Instant::now();
    let steps = s.metta_calculus(1000000000000000);
    println!("elapsed {} steps {} size {}", t0.elapsed().as_millis(), steps, s.btm.val_count());

    let mut v = vec![];
    s.dump_all_sexpr(&mut v).unwrap();
    let res = String::from_utf8(v).unwrap();

    println!("result: {res}");
    assert!(res.contains("MATCHED\n"));
}

fn negative() {
    let mut s = Space::new();

    // note 'idle' MM2-like statement that can be activated by moving it to the exec space
    const SPACE_EXPRS: &str = r#"
(exec 0 (, (Something (very specific))) (, MATCHED))

(Something $unspecific)

    "#;

    s.load_sexpr(SPACE_EXPRS.as_bytes(), expr!(s, "$"), expr!(s, "_1")).unwrap();

    let mut t0 = Instant::now();
    let steps = s.metta_calculus(1000000000000000); // big number to show the MM2 inference control working
    println!("elapsed {} steps {} size {}", t0.elapsed().as_millis(), steps, s.btm.val_count());

    let mut v = vec![];
    s.dump_all_sexpr(&mut v).unwrap();
    let res = String::from_utf8(v).unwrap();

    println!("result: {res}");
    assert!(res.contains("MATCHED\n"));
}

fn negative_equal() {
    let mut s = Space::new();

    // note 'idle' MM2-like statement that can be activated by moving it to the exec space
    const SPACE_EXPRS: &str = r#"
(exec 0 (, (Something (very specific) (very specific))) (, MATCHED))

(Something $repeated $repeated)

    "#;

    s.load_sexpr(SPACE_EXPRS.as_bytes(), expr!(s, "$"), expr!(s, "_1")).unwrap();

    let mut t0 = Instant::now();
    let steps = s.metta_calculus(1000000000000000); // big number to show the MM2 inference control working
    println!("elapsed {} steps {} size {}", t0.elapsed().as_millis(), steps, s.btm.val_count());

    let mut v = vec![];
    s.dump_all_sexpr(&mut v).unwrap();
    let res = String::from_utf8(v).unwrap();

    println!("result: {res}");
    assert!(res.contains("MATCHED\n"));
}

fn bipolar() {
    let mut s = Space::new();

    // note 'idle' MM2-like statement that can be activated by moving it to the exec space
    const SPACE_EXPRS: &str = r#"
(exec 0 (, (Something (very $unspecific))) (, MATCHED))

(Something ($unspecific specific))

    "#;

    s.load_sexpr(SPACE_EXPRS.as_bytes(), expr!(s, "$"), expr!(s, "_1")).unwrap();

    let mut t0 = Instant::now();
    let steps = s.metta_calculus(1000000000000000); // big number to show the MM2 inference control working
    println!("elapsed {} steps {} size {}", t0.elapsed().as_millis(), steps, s.btm.val_count());

    let mut v = vec![];
    s.dump_all_sexpr(&mut v).unwrap();
    let res = String::from_utf8(v).unwrap();

    println!("result: {res}");
    assert!(res.contains("MATCHED\n"));
}

fn bipolar_equal() {
    let mut s = Space::new();

    // note 'idle' MM2-like statement that can be activated by moving it to the exec space
    const SPACE_EXPRS: &str = r#"
(exec 0 (, (Something ($x Y $x Y))) (, MATCHED))

(Something (X $y X $y))

    "#;

    s.load_sexpr(SPACE_EXPRS.as_bytes(), expr!(s, "$"), expr!(s, "_1")).unwrap();

    let mut t0 = Instant::now();
    let steps = s.metta_calculus(1000000000000000); // big number to show the MM2 inference control working
    println!("elapsed {} steps {} size {}", t0.elapsed().as_millis(), steps, s.btm.val_count());

    let mut v = vec![];
    s.dump_all_sexpr(&mut v).unwrap();
    let res = String::from_utf8(v).unwrap();

    println!("result: {res}");
    assert!(res.contains("MATCHED\n"));
}

fn two_positive_equal() {
    let mut s = Space::new();

    const SPACE_EXPRS: &str = r#"
(exec 0 (, (Something $x $x) (Else $y $y)) (, MATCHED))

(Something (foo bar) (foo bar))
(Else (bar baz) (bar baz))
    "#;

    s.load_all_sexpr(SPACE_EXPRS.as_bytes()).unwrap();

    let mut t0 = Instant::now();
    let steps = s.metta_calculus(1000000000000000);
    println!("elapsed {} steps {} size {}", t0.elapsed().as_millis(), steps, s.btm.val_count());

    let mut v = vec![];
    s.dump_all_sexpr(&mut v).unwrap();
    let res = String::from_utf8(v).unwrap();

    println!("result: {res}");
    assert!(res.contains("MATCHED\n"));
}

fn two_positive_equal_crossed() {
    let mut s = Space::new();

    const SPACE_EXPRS: &str = r#"
(exec 0 (, (Something $x $y) (Else $x $y)) (, MATCHED))

(Something (foo bar) (bar baz))
(Else (foo bar) (bar baz))
    "#;

    s.load_all_sexpr(SPACE_EXPRS.as_bytes()).unwrap();

    let mut t0 = Instant::now();
    let steps = s.metta_calculus(1000000000000000);
    println!("elapsed {} steps {} size {}", t0.elapsed().as_millis(), steps, s.btm.val_count());

    let mut v = vec![];
    s.dump_all_sexpr(&mut v).unwrap();
    let res = String::from_utf8(v).unwrap();

    println!("result: {res}");
    assert!(res.contains("MATCHED\n"));
}

fn two_bipolar_equal_crossed() {
    let mut s = Space::new();

    const SPACE_EXPRS: &str = r#"
(exec 0 (, (Something $x $y) (Else $x $y)) (, (MATCHED $x $y)))

(Something (foo $x) (foo $x))
(Else ($x bar) ($x bar))
    "#;

    s.load_all_sexpr(SPACE_EXPRS.as_bytes()).unwrap();

    let mut t0 = Instant::now();
    let steps = s.metta_calculus(1000000000000000);
    println!("elapsed {} steps {} size {}", t0.elapsed().as_millis(), steps, s.btm.val_count());

    let mut v = vec![];
    s.dump_all_sexpr(&mut v).unwrap();
    let res = String::from_utf8(v).unwrap();

    println!("result: {res}");
    assert!(res.contains("(MATCHED (foo bar) (foo bar))\n"));
}

fn logic_query() {
    let mut s = Space::new();

    const SPACE_EXPRS: &str = r#"
(exec 0 (, (axiom $x) (axiom $x)) (, (combined $x)))
(exec 0 (, (axiom (= $lhs $rhs)) (axiom (= $rhs $lhs))) (, (reversed $lhs $rhs)))
    "#;

    const AXIOM_EXPRS: &str = r#"
(= (L $x $y $z) (R $x $y $z))
(= (L 1 $x $y) (R 1 $x $y))
(= (R $x (L $x $y $z) $w) $x)
(= (R $x (R $x $y $z) $w) $x)
(= (R $x (L $x $y $z) $x) (L $x (L $x $y $z) $x))
(= (L $x $y (\ $y $z)) (L $x $y $z))
(= (L $x $y (* $z $y)) (L $x $y $z))
(= (L $x $y (\ $z 1)) (L $x $z $y))
(= (L $x $y (\ $z $y)) (L $x $z $y))
(= (L $x 1 (\ $y 1)) (L $x $y 1))
(= (T $x (L $x $y $z)) $x)
(= (T $x (R $x $y $z)) $x)
(= (T $x (a $x $y $z)) $x)
(= (T $x (\ (a $x $y $z) $w)) (T $x $w))
(= (T $x (* $y $y)) (T $x (\ (a $x $z $w) (* $y $y))))
(= (R (/ 1 $x) $x (\ $x 1)) (\ $x 1))
(= (\ $x 1) (/ 1 (L $x $x (\ $x 1))))
(= (L $x $x $x) (* (K $x (\ $x 1)) $x))
    "#;

    s.load_all_sexpr(SPACE_EXPRS.as_bytes()).unwrap();
    s.load_sexpr(AXIOM_EXPRS.as_bytes(),expr!(s, "$"), expr!(s, "[2] axiom _1")).unwrap();

    let steps = s.metta_calculus(1000000000000000);

    assert_eq!(s.btm.val_count(), 79);
}

fn bc0() {
    let mut s = Space::new();

    const SPACE_EXPRS: &str = r#"
    ((step base)
      (, (goal (: $proof $conclusion)) (kb (: $proof $conclusion)))
      (, (ev (: $proof $conclusion) ) ))

    ((step abs)
      (, (goal (: $proof $conclusion)))
      (, (goal (: $lhs (-> $synth $conclusion)) ) ))

    ((step rev)
      (, (ev (: $lhs (-> $a $r)))  (goal (: $k $r)) )
      (, (goal (: $rhs $a) ) ))

    ((step app)
      (, (ev (: $lhs (-> $a $r)))  (ev (: $rhs $a))  )
      (, (ev (: (@ $lhs $rhs) $r) ) ))

    (exec zealous
            (, ((step $x) $p0 $t0)
               (exec zealous $p1 $t1) )
            (, (exec $x $p0 $t0)
               (exec zealous $p1 $t1) ))
    "#;

    const KB_EXPRS: &str = r#"
    (kb (: a A))
    (kb (: ab (R A B)))
    (kb (: bc (R B C)))
    (kb (: MP (-> (R $p $q) (-> $p $q))))

    (goal (: $proof C))
    "#;

    s.load_all_sexpr(SPACE_EXPRS.as_bytes()).unwrap();
    s.load_all_sexpr(KB_EXPRS.as_bytes()).unwrap();

    let mut t0 = Instant::now();
    let steps = s.metta_calculus(50);
    println!("elapsed {} steps {} size {}", t0.elapsed().as_millis(), steps, s.btm.val_count());

    let mut v = vec![];
    s.dump_all_sexpr(&mut v).unwrap();
    let res = String::from_utf8(v).unwrap();

    println!("result: {res}");
    assert!(res.contains("(ev (: (@ (@ MP bc) (@ (@ MP ab) a)) C))\n"));
}

fn bc1() {
    let mut s = Space::new();

    const SPACE_EXPRS: &str = r#"
    ((step base)
      (, (goal (: $proof $conclusion)) (kb (: $proof $conclusion)))
      (, (ev (: $proof $conclusion) ) ))

    ((step rec)
      (, (goal (: (@ $lhs $rhs) $conclusion)))
      (, (goal (: $lhs (-> $synth $conclusion))) (goal (: $rhs $synth))))

    ((step app)
      (, (ev (: $lhs (-> $a $r)))  (ev (: $rhs $a))  )
      (, (ev (: (@ $lhs $rhs) $r) ) ))

    (exec zealous
            (, ((step $x) $p0 $t0)
               (exec zealous $p1 $t1) )
            (, (exec $x $p0 $t0)
               (exec zealous $p1 $t1) ))
    "#;

    const KB_EXPRS: &str = r#"
    (kb (: a A))
    (kb (: ab (R A B)))
    (kb (: bc (R B C)))
    (kb (: cd (R C D)))
    (kb (: MP (-> (R $p $q) (-> $p $q))))

    (goal (: $proof C))
    "#;

    s.load_all_sexpr(SPACE_EXPRS.as_bytes()).unwrap();
    s.load_all_sexpr(KB_EXPRS.as_bytes()).unwrap();

    let mut t0 = Instant::now();
    let steps = s.metta_calculus(100);
    println!("elapsed {} steps {} size {}", t0.elapsed().as_millis(), steps, s.btm.val_count());

    let mut v = vec![];
    s.dump_all_sexpr(&mut v).unwrap();
    let res = String::from_utf8(v).unwrap();

    println!("result: {res}");
    assert!(res.contains("(ev (: (@ (@ MP cd) (@ (@ MP bc) (@ (@ MP ab) a))) D))\n"));
}

fn bc2() {
    let mut s = Space::new();

    /*
    ((step rec)
      (, (goal (: (@ $lhs $rhs) $conclusion)))
      (, (goal (: $lhs (-> $synth $conclusion))) (goal (: $rhs $synth))))

    ((step rec2)
      (, (goal (: (@ $f $a $b) $conclusion)))
      (, (goal (: $f (-> $syntha $synthb $conclusion))) (goal (: $a $syntha)) (goal (: $b $synthb)) ))
    
     */
    const SPACE_EXPRS: &str = r#"
    ((step base)
      (, (goal (: $proof $conclusion)) (kb (: $proof $conclusion)))
      (, (ev (: $proof $conclusion) ) ))

    ((step abs)
      (, (goal (: $proof $conclusion)))
      (, (goal (: $lhs (-> $synth $conclusion)) ) ))

    ((step rev)
      (, (ev (: $lhs (-> $a $r)))  (goal (: $k $r)) )
      (, (goal (: $rhs $a) ) ))

    ((step abs2)
      (, (goal (: $proof $conclusion)))
      (, (goal (: $lhs (-> $syntha $synthb $conclusion)) ) ))

    ((step rev2)
      (, (ev (: $lhs (-> $a $b $r)))  (goal (: $k $r)) )
      (, (goal (: $ap $a)) (goal (: $bp $b)) ))

    ((step app)
      (, (ev (: $lhs (-> $a $r)))  (ev (: $rhs $a))  )
      (, (ev (: (@ $lhs $rhs) $r) ) ))
      
    ((step app2)
      (, (ev (: $f (-> $a $b $r)))  (ev (: $ap $a)) (ev (: $bp $b))  )
      (, (ev (: (@ $f $ap $bp) $r) ) ))

    (exec zealous
            (, ((step $x) $p0 $t0)
               (exec zealous $p1 $t1) )
            (, (exec $x $p0 $t0)
               (exec zealous $p1 $t1) ))
    "#;

    const KB_EXPRS: &str = r#"
    (kb (: ax-mp (-> $𝜑 (→ $𝜑 $𝜓) $𝜓)))
    (kb (: ax-1 (→ $𝜑 (→ $𝜓 $𝜑))))
    (kb (: ax-2 (→ (→ $𝜑 (→ $𝜓 $𝜒)) (→ (→ $𝜑 $𝜓) (→ $𝜑 $𝜒)))))
    (kb (: ax-3 (→ (→ (¬ $𝜑) (¬ $𝜓)) (→ $𝜓 $𝜑))))

    (kb (: mp2b.1 𝜑))
    (kb (: mp2b.2 (→ 𝜑 𝜓)))
    (kb (: mp2b.3 (→ 𝜓 𝜒)))

    (goal (: $proof 𝜒))
    "#;

    s.load_all_sexpr(SPACE_EXPRS.as_bytes()).unwrap();
    s.load_all_sexpr(KB_EXPRS.as_bytes()).unwrap();

    let mut t0 = Instant::now();
    let steps = s.metta_calculus(30);
    println!("elapsed {} steps {} size {}", t0.elapsed().as_millis(), steps, s.btm.val_count());

    let mut v = vec![];
    // s.dump_all_sexpr(&mut v).unwrap();
    s.dump_sexpr(expr!(s, "[2] ev [3] : $ 𝜒"), expr!(s, "_1"), &mut v);
    let res = String::from_utf8(v).unwrap();

    println!("proof of 𝜒: {res}");
    assert!(res.contains("(@ ax-mp (@ ax-mp mp2b.1 mp2b.2) mp2b.3)\n"));
}

fn bc3() {
    let mut s = Space::new();

    const SPACE_EXPRS: &str = r#"
    ((step (0 base) $ts)
      (, (goal $ts (: $proof $conclusion)) (kb (: $proof $conclusion)))
      (, (ev (: $proof $conclusion) ) ))

    ((step (1 abs) $ts)
      (, (goal $k (: $proof $conclusion)))
      (, (goal (S $ts) (: $lhs (-> $synth $conclusion)) ) ))

    ((step (2 rev) $ts)
      (, (ev (: $lhs (-> $a $r)))  (goal $k (: $k $r)) )
      (, (goal (S $ts) (: $rhs $a) ) ))

    ((step (3 app) $ts)
      (, (ev (: $lhs (-> $a $r)))  (ev (: $rhs $a))  )
      (, (ev (: (@ $lhs $rhs) $r) ) ))

    (exec (clocked Z)
            (, ((step $x $ts) $p0 $t0)
               (exec (clocked $ts) $p1 $t1) )
            (, (exec (a $x) $p0 $t0)
               (exec (clocked (S $ts)) $p1 $t1) ))
    "#;

    const KB_EXPRS: &str = r#"
    (kb (: a A))
    (kb (: ab (R A B)))
    (kb (: bc (R B C)))
    (kb (: MP (-> (R $p $q) (-> $p $q))))

    (goal Z (: $proof C))
    "#;


    // (kb (: a A))
    //     (kb (: ab (-> A B)))
    //
    //     (goal Z (: $proof B))


    // (kb (: b B))
    //     (kb (: ab_c (-> A (-> B C))))
    //     (kb (: uncurry (-> (-> $a (-> $b $c)) (-> (* $a $b) $c))))
    // (kb (: sym (-> (* $a $b) (* $b $a))))
    // (kb (: . (-> (-> $b $c) (-> (-> $a $b) (-> $a $c)))))
    // (kb (: curry (-> (-> (* $a $b) $c) (-> $a (-> $b $c)))))
    //
    // (goal Z (: $proof (-> A C)))


    // P1:  (exec $p (, pat) (, (- temp) (+ x)))
    // add subtracts to SUB space, and remove them at the end
    // could not remove patterns under bindings
    // P2:  (exec $p (, (take pat) ) (, temp x)
    // only remove original patterns
    // P3:  (exec $p (, pat ) (, (subtract pat) (subtract temp)) (, temp x)
    //

    s.load_all_sexpr(SPACE_EXPRS.as_bytes()).unwrap();
    s.load_all_sexpr(KB_EXPRS.as_bytes()).unwrap();


    // let mut t0 = Instant::now();
    // println!("elapsed {} steps {} size {}", t0.elapsed().as_millis(), steps, s.btm.val_count());

    let mut t0 = Instant::now();
    let steps = s.metta_calculus(60);
    println!("elapsed {} steps {} size {}", t0.elapsed().as_millis(), steps, s.btm.val_count());

    let mut v = vec![];
    // s.dump_all_sexpr(&mut v).unwrap();
    s.dump_sexpr(expr!(s, "[2] ev [3] : $ C"), expr!(s, "_1"), &mut v);
    let res = String::from_utf8(v).unwrap();

    println!("proof: {res}");


    // for i in 0..14 {
    //     println!("GEN {i}");
    //     let steps = s.metta_calculus(1);
    //     let mut v = vec![];
    //     s.dump_all_sexpr(&mut v).unwrap();
    //     // s.dump_sexpr(expr!(s, "[2] ev [3] : $ C"), expr!(s, "_1"), &mut v).unwrap();
    //     let res = String::from_utf8(v).unwrap();
    //
    //     println!("result: {res}");
    //
    // }

    // assert!(res.contains("(@ (@ . (@ uncurry ab_c)) (@ (@ curry sym) b))\n"));
}

fn cm0() {
    let mut s = Space::new();
    
    // Follow along https://en.wikipedia.org/wiki/Counter_machine#Program
    
    // non-peano csv version see cm1
    /*
    s.load_csv(INSTRS_CSV.as_bytes(), expr!(s, "$"), expr!(s, "[2] program _1"), b',').unwrap();
    s.load_csv(REGS_CSV.as_bytes(), expr!(s, "[2] $ $"), expr!(s, "[3] state 0 [3] REG _1 _2"), b',').unwrap();
    JZ,2,5\nDEC,2,2INC,3,3\nINC,1,4\nJZ,0,0\nJZ,1,9\nDEC,1,7\nINC,2,8\nJZ,0,5\nH,0,0
     */
    let TO_COPY = 50;

    let SPACE_MACHINE = format!(r#"
    (program Z (JZ 2 (S (S (S (S (S Z))))) ))
    (program (S Z) (DEC 2))
    (program (S (S Z)) (INC 3))
    (program (S (S (S Z))) (INC 1))
    (program (S (S (S (S Z)))) (JZ 0 Z))
    (program (S (S (S (S (S Z))))) (JZ 1 (S (S (S (S (S (S (S (S (S Z)))))))))))
    (program (S (S (S (S (S (S Z)))))) (DEC 1))
    (program (S (S (S (S (S (S (S Z))))))) (INC 2))
    (program (S (S (S (S (S (S (S (S Z)))))))) (JZ 0 (S (S (S (S (S Z)))))))
    (program (S (S (S (S (S (S (S (S (S Z))))))))) H)
    (state Z (REG 0 Z))
    (state Z (REG 1 Z))
    (state Z (REG 2 {}))
    (state Z (REG 3 Z))
    (state Z (REG 4 Z))
    (state Z (IC Z))
    (if (S $n) $x $y $x)
    (if Z $x $y $y)
    (0 != 1) (0 != 2) (0 != 3) (0 != 4)
    (1 != 0) (1 != 2) (1 != 3) (1 != 4)
    (2 != 1) (2 != 0) (2 != 3) (2 != 4)
    (3 != 1) (3 != 2) (3 != 0) (3 != 4)
    (4 != 1) (4 != 2) (4 != 0) (4 != 3)
    
    ((step JZ $ts)
      (, (state $ts (IC $i)) (program $i (JZ $r $j)) (state $ts (REG $r $v)) (if $v (S $i) $j $ni) (state $ts (REG $k $kv)))
      (, (state (S $ts) (IC $ni)) (state (S $ts) (REG $k $kv))))

    ((step INC $ts)
      (, (state $ts (IC $i)) (program $i (INC $r)) (state $ts (REG $r $v)) ($r != $o) (state $ts (REG $o $ov)))
      (, (state (S $ts) (IC (S $i))) (state (S $ts) (REG $r (S $v))) (state (S $ts) (REG $o $ov))))
    
    ((step DEC $ts)
      (, (state $ts (IC $i)) (program $i (DEC $r)) (state $ts (REG $r (S $v))) ($r != $o) (state $ts (REG $o $ov)))
      (, (state (S $ts) (IC (S $i))) (state (S $ts) (REG $r $v)) (state (S $ts) (REG $o $ov))))  

    (exec (clocked Z)
            (, (exec (clocked $ts) $p1 $t1) 
               (state $ts (IC $_))
               ((step $k $ts) $p0 $t0))
            (, (exec ($k $ts) $p0 $t0)
               (exec (clocked (S $ts)) $p1 $t1)))
    "#, peano(TO_COPY));

    s.load_all_sexpr(SPACE_MACHINE.as_bytes()).unwrap();

    let mut t0 = Instant::now();
    let steps = s.metta_calculus(1000000000000000);
    println!("elapsed {} steps {} size {}", t0.elapsed().as_millis(), steps, s.btm.val_count());

    let mut v_ts = vec![];
    s.dump_sexpr(expr!(s, "[3] state $ $"), expr!(s, "_1"), &mut v_ts);
    let last_ts_tmp = String::from_utf8(v_ts).unwrap(); 
    let last_ts = last_ts_tmp.split("\n").max_by_key(|x| x.len()).unwrap();
    let mut v = vec![];
    // s.dump_all_sexpr(&mut v).unwrap();
    s.dump_sexpr(expr!(s, "[3] state $ [3] REG 3 $"), expr!(s, "[2] _1 _2"), &mut v);
    let res = String::from_utf8(v).unwrap();
    
    // println!("{res}");
    assert!(res.contains(format!("({} {})", last_ts, peano(TO_COPY)).as_str()));
}

/*fn match_case() {
    let mut s = Space::new();

    const SPACE_EXPRS: &str = r#"
(unify $x $x)

(exec 0
      (, (Apply $x)
         (Match $c $p $t))
      (, (exec (M $c)
               (, (unify $x $p) (exec (M $c) $Mp $Mt))
               (, (res $t)
                  (- (exec (M $c) $Mp $Mt)) ))))

(Match 0 (foo $x) (Inner Foo $x))
(Match 1 (bar $x) (Inner Bar $x))
(Match 2 $x (Fallback $x))

(Apply (foo $x))
    "#;

    s.load_all_sexpr(SPACE_EXPRS.as_bytes()).unwrap();

    let mut t0 = Instant::now();
    let steps = s.metta_calculus(1000000000000000);
    println!("elapsed {} steps {} size {}", t0.elapsed().as_millis(), steps, s.btm.val_count());

    let mut v = vec![];
    s.dump_all_sexpr(&mut v).unwrap();
    let res = String::from_utf8(v).unwrap();

    println!("result: {res}");
}*/

fn lens_aunt() {
    let mut s = Space::new();
    /*
    Tom x Pam
     |   \
    Liz  Bob
         / \
      Ann   Pat
             |
            Jim
     */
    let SPACE = r#"
    (exec QA (, (aunt $xc $x $y $yt) (data $xc) (exec QA $P $T)
                (parent $p $x) (parent $gp $p) (parent $gp $y)
                (female $y) ($p != $y))
             (, (data $yt) (exec QA $P $T)))

    (data (poi Jim)) (data (poi Ann))
    (aunt (poi $x) $x $y (result ($y aunt of $x)))

    (parent Tom Bob)
    (parent Pam Bob)
    (parent Tom Liz)
    (parent Bob Ann)
    (parent Bob Pat)
    (parent Pat Jim)
    (female Pam) (female Liz) (female Pat) (female Ann)
    (male Tom) (male Bob) (male Jim)

    (Pam == Pam) (Pam != Liz) (Pam != Pat) (Pam != Ann) (Pam != Tom) (Pam != Bob) (Pam != Jim)
    (Liz != Pam) (Liz == Liz) (Liz != Pat) (Liz != Ann) (Liz != Tom) (Liz != Bob) (Liz != Jim)
    (Pat != Pam) (Pat != Liz) (Pat == Pat) (Pat != Ann) (Pat != Tom) (Pat != Bob) (Pat != Jim)
    (Ann != Pam) (Ann != Liz) (Ann != Pat) (Ann == Ann) (Ann != Tom) (Ann != Bob) (Ann != Jim)
    (Tom != Pam) (Tom != Liz) (Tom != Pat) (Tom != Ann) (Tom == Tom) (Tom != Bob) (Tom != Jim)
    (Bob != Pam) (Bob != Liz) (Bob != Pat) (Bob != Ann) (Bob != Tom) (Bob == Bob) (Bob != Jim)
    (Jim != Pam) (Jim != Liz) (Jim != Pat) (Jim != Ann) (Jim != Tom) (Jim != Bob) (Jim == Jim)
    "#;

    s.load_all_sexpr(SPACE.as_bytes()).unwrap();

    let mut t0 = Instant::now();
    let steps = s.metta_calculus(1);
    println!("elapsed {} steps {} size {}", t0.elapsed().as_millis(), steps, s.btm.val_count());

    let mut v = vec![];
    // s.dump_all_sexpr(&mut v).unwrap();
    s.dump_sexpr(expr!(s, "[2] data [2] result $"), expr!(s, "_1"), &mut v);
    let res = String::from_utf8(v).unwrap();

    println!("{res}");
    assert_eq!(res, "(Ann aunt of Jim)\n(Liz aunt of Ann)\n");
}

fn lens_composition() {
    let mut s = Space::new();

    let SPACE = r#"
    (exec LC (, (compose $l0 $l1)
                (lens ($l0 $xc0 $x0 $y0 $yt0))
                (lens ($l1 $x0 $x1 $y1 $y0)) )
             (, (lens (($l0 o $l1) $xc0 $x1 $y1 $yt0))))

    (lens (aunt (poi $x) $x $y (result ($y aunt of $x))))
    (lens (ns (users (adam (experiments $x))) $x $y (users (adam (experiments $y)))))
    (compose ns aunt)
    "#;

    s.load_all_sexpr(SPACE.as_bytes()).unwrap();

    let mut t0 = Instant::now();
    let steps = s.metta_calculus(1);
    println!("elapsed {} steps {} size {}", t0.elapsed().as_millis(), steps, s.btm.val_count());

    let mut v = vec![];
    s.dump_all_sexpr(&mut v).unwrap();
    let res = String::from_utf8(v).unwrap();

    println!("{res}");
    assert!(res.contains("(lens ((ns o aunt) (users (adam (experiments (poi $a)))) $a $b (users (adam (experiments (result ($b aunt of $a)))))))"));
}

fn bench_transitive_no_unify(nnodes: usize, nedges: usize) {
    use rand::{rngs::StdRng, SeedableRng, Rng};
    let mut rng = StdRng::from_seed([0; 32]);
    let mut s = Space::new();

    let mut edges = String::new();

    for k in 0..nedges {
        let i = rng.random_range(0..nnodes);
        let j = rng.random_range(0..nnodes);
        edges.push_str(format!("(edge {i} {j})\n").as_str());
    }

    s.load_all_sexpr(edges.as_bytes()).unwrap();
    println!("constructed {} nodes {} edges", nnodes, nedges);

    let t0 = Instant::now();
    s.interpret(expr!(s, "[4] exec 0 [3] , [3] edge $ $ [3] edge _2 $ [2] , [3] trans _1 _3"));
    println!("trans elapsed {} µs", t0.elapsed().as_micros());

    let t1 = Instant::now();
    s.interpret(expr!(s, "[4] exec 0 [4] , [3] edge $ $ [3] edge _2 $ [3] edge _1 _3 [2] , [4] dtrans _1 _2 _3"));
    println!("detect trans elapsed {} µs", t1.elapsed().as_micros());


    let mut v = vec![];
    s.dump_sexpr(expr!(s, "[3] trans $ $"), expr!(s, "[2] _1 _2"), &mut v);
    let ntrans: usize = v.iter().map(|c| if *c == b'\n' { 1 } else { 0 }).sum();
    v.clear();
    s.dump_sexpr(expr!(s, "[4] dtrans $ $ $"), expr!(s, "[3] _1 _2 _3"), &mut v);
    let ndtrans: usize = v.iter().map(|c| if *c == b'\n' { 1 } else { 0 }).sum();
    println!("trans {} detected trans {}", ntrans, ndtrans);

    // (badbad)
    // constructed 50000 nodes 1000000 edges
    // trans elapsed 17391765 µs
    // detect trans elapsed 11928710 µs
    // trans 19917429 detected trans 8716
}


fn bench_clique_no_unify(nnodes: usize, nedges: usize, max_clique: usize) {
    fn binom_as_f64(n: u64, k: u64) -> f64 {
        if k > n { return 0.0; }
        let k = std::cmp::min(k, n - k);
        let mut res = 1.0f64;
        for i in 1..=k {
            res *= (n - k + i) as f64;
            res /= i as f64;
        }
        res
    }

    fn expected_fraction_kclique_gne(n: u64, e: u64, k: u64) -> f64 {
        assert!(n >= 2, "n >= 2");
        let m = n * (n - 1) / 2; // total possible edges
        assert!(e <= m, "E must be <= C(n,2)");
        let kk = k * (k - 1) / 2; // number of edges inside a k-clique
        if kk == 0 { return 1.0; } // k=0 or 1
        if e < kk { return 0.0; }  // not enough edges to cover a clique
        let mut num = 1.0f64;
        let mut den = 1.0f64;
        for i in 0..kk {
            num *= (e - i) as f64;
            den *= (m - i) as f64;
        }
        num / den
    }

    fn expected_num_kclique_gne(n: u64, e: u64, k: u64) -> f64 {
        binom_as_f64(n, k) * expected_fraction_kclique_gne(n, e, k)
    }

    fn clique_query(k: usize) -> String {
        format!("(exec 0 (,{}) (, ({}-clique{})))",
            (0..k).flat_map(|i| ((i + 1)..k).map(move |j| format!(" (edge $x{} $x{})", i, j))).collect::<String>(),
            k,
            (0..k).map(|i| format!(" $x{}", i)).collect::<String>()
        )
    }

    use rand::{rngs::StdRng, SeedableRng, Rng};
    let mut rng = StdRng::from_seed([0; 32]);
    let mut s = Space::new();

    let mut edges: HashSet<String> = HashSet::new();

    // irreflexive degeneracy ordered graph
    while edges.len() < nedges {
        let i = rng.random_range(0..nnodes);
        let j = rng.random_range(0..nnodes);
        if i == j { continue }
        if i < j { edges.insert(format!("(edge {i} {j})\n")); }
        else { edges.insert(format!("(edge {j} {i})\n")); }
    }

    s.load_all_sexpr(edges.into_iter().collect::<String>().as_bytes()).unwrap();
    println!("constructed {} nodes {} edges", nnodes, nedges);

    for k in 3..(max_clique+1) {
        let query = clique_query(k);
        println!("executing query {}", query);
        let t0 = Instant::now();
        s.load_sexpr(query.as_bytes(), expr!(s, "$"), expr!(s, "_1"));
        s.metta_calculus(1);
        let nkcliques: usize = s.btm.read_zipper_at_path([item_byte(Tag::Arity((k+1) as _))]).val_count();
        println!("found {} {k}-cliques (expected {}) in {} µs", nkcliques, expected_num_kclique_gne(nnodes as _, nedges as _, k as _).round(), t0.elapsed().as_micros());
    }
    // constructed 200 nodes 3600 edges
    // executing query (exec 0 (, (edge $x0 $x1) (edge $x0 $x2) (edge $x1 $x2)) (, (3-clique $x0 $x1 $x2)))
    // found 7824 3-cliques (expected 7770) in 39910 µs
    // executing query (exec 0 (, (edge $x0 $x1) (edge $x0 $x2) (edge $x0 $x3) (edge $x1 $x2) (edge $x1 $x3) (edge $x2 $x3)) (, (4-clique $x0 $x1 $x2 $x3)))
    // found 2320 4-cliques (expected 2260) in 1096909 µs
    // executing query (exec 0 (, (edge $x0 $x1) (edge $x0 $x2) (edge $x0 $x3) (edge $x0 $x4) (edge $x1 $x2) (edge $x1 $x3) (edge $x1 $x4) (edge $x2 $x3) (edge $x2 $x4) (edge $x3 $x4)) (, (5-clique $x0 $x1 $x2 $x3 $x4)))
    // found 102 5-cliques (expected 94) in 24705340 µs
    // executing query (exec 0 (, (edge $x0 $x1) (edge $x0 $x2) (edge $x0 $x3) (edge $x0 $x4) (edge $x0 $x5) (edge $x1 $x2) (edge $x1 $x3) (edge $x1 $x4) (edge $x1 $x5) (edge $x2 $x3) (edge $x2 $x4) (edge $x2 $x5) (edge $x3 $x4) (edge $x3 $x5) (edge $x4 $x5)) (, (6-clique $x0 $x1 $x2 $x3 $x4 $x5)))
    // found 0 6-cliques (expected 1) in <1288009964 µs
}

fn bench_finite_domain(terms: usize) {
    use rand::{rngs::StdRng, SeedableRng, Rng};
    let mut rng = StdRng::from_seed([0; 32]);
    const DS: usize = 64;
    const SYM: [&'static str; 64] = ["0","1","2","3","4","5","6","7","8","9","?","@","A","B","C","D","E","F","G","H","I","J","K","L","M","N","O","P","Q","R","S","T","U","V","W","X","Y","Z","a","b","c","d","e","f","g","h","i","j","k","l","m","n","o","p","q","r","s","t","u","v","w","x","y","z"];
    // const SYM: [&'static str; 64] = ["À", "Á", "Â", "Ã", "Ä", "Å", "Æ", "Ç", "È", "É", "Ê", "Ë", "Ì", "Í", "Î", "Ï", "Ð", "Ñ", "Ò", "Ó", "Ô", "Õ", "Ö", "×", "Ø", "Ù", "Ú", "Û", "Ü", "Ý", "Þ", "ß", "à", "á", "â", "ã", "ä", "å", "æ", "ç", "è", "é", "ê", "ë", "ì", "í", "î", "ï", "ð", "ñ", "ò", "ó", "ô", "õ", "ö", "÷", "ø", "ù", "ú", "û", "ü", "ý", "þ", "ÿ"];
    // const SYM: [&'static str; 64] = ["䷁","䷗","䷆","䷒","䷎","䷣","䷭","䷊","䷏","䷲","䷧","䷵","䷽","䷶","䷟","䷡","䷇","䷂","䷜","䷻","䷦","䷾","䷯","䷄","䷬","䷐","䷮","䷹","䷞","䷰","䷛","䷪","䷖","䷚","䷃","䷨","䷳","䷕","䷑","䷙","䷢","䷔","䷿","䷥","䷷","䷝","䷱","䷍","䷓","䷩","䷺","䷼","䷴","䷤","䷸","䷈","䷋","䷘","䷅","䷉","䷠","䷌","䷫","䷀"];

    fn uop<F : Fn(usize) -> usize>(sym: &str, f: F) -> String {
        let mut s = String::new();
        for x in 0..DS {
            let z = f(x);
            if z == usize::MAX { continue }
            s.push_str(format!("({} {} = {})\n", sym, SYM[x], SYM[z]).as_str());
        }
        s
    }

    fn bop<F : Fn(usize, usize) -> usize>(sym: &str, f: F) -> String {
        let mut s = String::new();
        for x in 0..DS {
            for y in 0..DS {
                let z = f(x, y);
                if z == usize::MAX { continue }
                s.push_str(format!("({} {} {} = {})\n", SYM[x], sym, SYM[y], SYM[z]).as_str());
            }
        }
        s
    }

    let mut s = Space::new();

    let sq = uop("²", |x| (x * x) % DS);
    let sqrt = uop("√", |x| x.isqrt());

    let add = bop("+", |x, y| (x + y) % DS);
    let sub = bop("-", |x, y| ((DS + x) - y) % DS);
    let mul = bop("*", |x, y| (x * y) % DS);
    let div = bop("/", |x, y| if y == 0 { usize::MAX } else { x / y });
    let join = bop("\\/", |x, y| x.max(y));
    let meet = bop("/\\", |x, y| x.min(y));

    let adds = bop("+s", |x, y| if x + y < DS { x + y } else { DS - 1 });
    let muls = bop("*s", |x, y| if x * y < DS { x * y } else { DS - 1 });

    let ops = [sq, sqrt, add, sub, mul, div, join, meet, adds, muls].concat();

    s.load_sexpr(ops.as_bytes(), expr!(s, "$"), expr!(s, "_1"));

    let mut args = String::new(); // e.g. (args ䷽ ䷣ ䷜ ䷣)
    for i in 0..10_000 {
        let x0 = rng.random_range(0..DS);
        let x1 = rng.random_range(0..DS);
        let y0 = rng.random_range(0..DS);
        let y1 = rng.random_range(0..DS);
        args.push_str(format!("(args {} {} {} {})", SYM[x0], SYM[x1], SYM[y0], SYM[y1]).as_str())
    }
    s.load_sexpr(args.as_bytes(), expr!(s, "$"), expr!(s, "_1"));

    s.load_sexpr(r"(exec 0 (, (args $x0 $y0 $x1 $y1) ($x0 /\ $x1 = $xl) ($x0 \/ $x1 = $xh) ($y0 /\ $y1 = $yl) ($y0 \/ $y1 = $yh) ($xh - $xl = $dx) ($yh - $yl = $dy) (² $dx = $dx2) (² $dy = $dy2) ($dx2 + $dy2 = $d2) (√ $d2 = $d)) (, (res $d)))".as_bytes(), expr!(s, "$"), expr!(s, "_1")).unwrap();
    let t0 = Instant::now();
    s.metta_calculus(1);
    let t1 = Instant::now();

    let mut v = vec![];
    // s.dump_all_sexpr(&mut v).unwrap();
    s.dump_sexpr(expr!(s, "[2] res $"), expr!(s, "_1"), &mut v);
    let res = String::from_utf8(v).unwrap();

    println!("{}", s.btm.val_count());
    println!("{res} ({terms} inputs) in {} µs", t1.duration_since(t0).as_micros());
    // (badbad)
    // (10_000 inputs) in 85833 µs
}

#[cfg(all(feature = "nightly"))]
fn json_upaths_smoke() {
    let test = r#"{
"first_name": "John",
"last_name": "Smith",
"is_alive": true,
"age": 27,
"address": {
  "street_address": "21 2nd Street",
  "city": "New York",
  "state": "NY",
  "postal_code": "10021-3100"},
"phone_numbers": [
  {"type": "home", "number": "212 555-1234"},
  {"type": "office", "number": "646 555-4567"}],
"children": ["Catherine", "Thomas", "Trevor"],
"spouse": null}"#;
    let mut cv = vec![];

    let mut s = Space::new();
    // let written = s.load_json(test.as_bytes()).unwrap();
    let written = s.json_to_paths(test.as_bytes(), &mut cv).unwrap();
    // println!("{:?}", pathmap::path_serialization::serialize_paths_(btm.read_zipper(), &mut cv));
    println!("written {written}");
    pathmap::paths_serialization::deserialize_paths(s.btm.write_zipper(), &cv[..], ()).unwrap();

    let mut v = vec![];
    s.dump_all_sexpr(&mut v).unwrap();
    let res = String::from_utf8(v).unwrap();
    println!("res {res}");
    assert_eq!(res, r#"(age 27)
(spouse null)
(address (city New York))
(address (state NY))
(address (postal_code 10021-3100))
(address (street_address 21 2nd Street))
(children (0 Catherine))
(children (1 Thomas))
(children (2 Trevor))
(is_alive true)
(last_name Smith)
(first_name John)
(phone_numbers (0 (type home)))
(phone_numbers (0 (number 212 555-1234)))
(phone_numbers (1 (type office)))
(phone_numbers (1 (number 646 555-4567)))
"#);
}

#[cfg(all(feature = "nightly"))]
fn json_upaths<IPath: AsRef<std::path::Path>, OPath : AsRef<std::path::Path>>(json_path: IPath, upaths_path: OPath) {
    println!("mmapping JSON file {:?}", json_path.as_ref().as_os_str());
    println!("writing out unordered .paths file {:?}", upaths_path.as_ref().as_os_str());
    let json_file = std::fs::File::open(json_path).unwrap();
    let json_mmap = unsafe { memmap2::Mmap::map(&json_file).unwrap() };
    let upaths_file = std::fs::File::create_new(upaths_path).unwrap();
    let mut upaths_bufwriter = std::io::BufWriter::new(upaths_file);

    let mut s = Space::new();
    let t0 = Instant::now();
    let written = s.json_to_paths(&*json_mmap, &mut upaths_bufwriter).unwrap();
    println!("written {written} in {} ms", t0.elapsed().as_millis());
    // (zephy)
    // mmapping JSON file "/home/adam/Downloads/G37S-9NQ.json"
    // writing out unordered .paths file "G37S-9NQ.upaths"
    // Ok(SerializationStats { bytes_out: 1415053, bytes_in: 12346358, path_count: 224769 })
    // written 224769 in 193 ms
    // (badbad)
    // mmapping JSON file "/mnt/data/enwiki-20231220-pages-articles-links/cqls.json"
    // writing out unordered .paths file "/mnt/data/enwiki-20231220-pages-articles-links/cqls.upaths"
    // Ok(SerializationStats { bytes_out: 231708224, bytes_in: 808333425, path_count: 15969490 })
    // written 15969490 in 17441 ms
}

/// Based on Anneline's instantiation of PDDL domains
fn pddl_ts<IPath: AsRef<std::path::Path>>(ts_path: IPath) {
    let mut s = Space::new();
    for mde in std::fs::read_dir(ts_path).unwrap() {
        let de = mde.unwrap();
        let file_name = de.file_name();
        let name = file_name.to_str().unwrap();
        let metta_file = std::fs::File::open(de.path()).unwrap();
        let metta_mmap = unsafe { memmap2::Mmap::map(&metta_file).unwrap() };
        s.load_sexpr(&*metta_mmap, expr!(s, "$"), expr!(s, format!("[2] {} _1", &name[..name.len()-6]).as_str())).unwrap();
    }

    let mut v = vec![];
    s.dump_all_sexpr(&mut v).unwrap();
    let res = String::from_utf8(v).unwrap();

    println!("result: {res}");
    /*
       WIP
     */
}

fn exponential(max_steps: usize) {
    let mut s = Space::new();

    const SPACE_EXPRS: &str = r#"
((step app)
 (, (num $1) )
 (, (num (M $1))
    (num (W $1)) ))

((step app)
 (, (num (M $1))
    (num (W $1)) )
 (, (num (C $1)) ))

(num Z)

(exec metta
      (, ((step $x) $p0 $t0)
         (exec metta $p1 $t1) )
      (, (exec $x $p0 $t0)
         (exec metta $p1 $t1) ))
"#;

    s.load_all_sexpr(SPACE_EXPRS.as_bytes()).unwrap();

    let mut t0 = Instant::now();
    let steps = s.metta_calculus(max_steps);
    println!("elapsed {} steps {} size {}", t0.elapsed().as_millis(), steps, s.btm.val_count());
}

fn exponential_fringe(steps: usize) {
    let mut s = Space::new();

    const SPACE_EXPRS: &str = r#"
((step meet $k)
 (, (num $k $1) (succ $k $sk) )
 (, (num $sk (M $1))
    (num $sk (W $1)) ))

((step join $k)
 (, (num $k (M $1)) (succ $k $sk)
    (num $k (W $1)) )
 (, (num $sk (C $1)) ))

(num 0 Z)

(exec (metta 0)
      (, (exec (metta $k) $p1 $t1) (succ $k $sk)
         ((step $x $k) $p0 $t0) )
      (, (exec (0 $x) $p0 $t0)
         (exec (metta $sk) $p1 $t1) ))
"#;

    let mut SUCCS: String = (0..steps).map(|x| format!("(succ {x} {})\n", x+1)).collect();

    s.load_all_sexpr(SPACE_EXPRS.as_bytes()).unwrap();
    s.load_all_sexpr(SUCCS.as_bytes()).unwrap();

    let mut t0 = Instant::now();
    let steps = s.metta_calculus(1000000000000000);
    println!("elapsed {} steps {} size {}", t0.elapsed().as_millis(), steps, s.btm.val_count());

    // let mut v = vec![];
    // s.dump_all_sexpr(&mut v).unwrap();
    // let res = String::from_utf8(v).unwrap();
    //
    // println!("result: {res}");
}

fn linear_fringe_alternating(steps: usize) {
    let mut s = Space::new();

    const SPACE_EXPRS: &str = r#"
((step meet $k)
 (, (num $k $1) )
 (, (tojoin $k (M $1))
    (tojoin $k (W $1)) ))

((step join $k)
 (, (tojoin $k (M $1)) (succ $k $sk)
    (tojoin $k (W $1)) )
 (, (num $sk (C $1)) ))

(num 0 Z)

(exec (metta 0)
      (, (exec (metta $k) $p1 $t1) (succ $k $sk)
         ((step meet $k) $p0 $t0) ((step join $k) $p2 $t2) )
      (, (exec (0 meet) $p0 $t0) (exec (1 join) $p2 $t2)
         (exec (metta $sk) $p1 $t1) ))
"#;

    let mut SUCCS: String = (0..steps).map(|x| format!("(succ {x} {})\n", x+1)).collect();

    s.load_all_sexpr(SPACE_EXPRS.as_bytes()).unwrap();
    s.load_all_sexpr(SUCCS.as_bytes()).unwrap();

    let mut t0 = Instant::now();
    let steps = s.metta_calculus(1000000000000000);
    println!("elapsed {} steps {} size {}", t0.elapsed().as_millis(), steps, s.btm.val_count());

    // let mut v = vec![];
    // s.dump_all_sexpr(&mut v).unwrap();
    // let res = String::from_utf8(v).unwrap();
    //
    // println!("result: {res}");
}


fn linear_alternating(steps: usize) {
    let mut s = Space::new();

    const SPACE_EXPRS: &str = r#"
((step meet)
 (, (num $1) )
 (, (tojoin (M $1))
    (tojoin (W $1)) ))

((step join)
 (, (tojoin (M $1))
    (tojoin (W $1)) )
 (, (num (C $1)) ))

(num Z)

(exec (metta 0)
      (, (exec (metta $k) $p1 $t1) (succ $k $sk)
         ((step meet) $p0 $t0) ((step join) $p2 $t2) )
      (, (exec (0 meet) $p0 $t0) (exec (1 join) $p2 $t2)
         (exec (metta $sk) $p1 $t1) ))
"#;

    let mut SUCCS: String = (0..steps).map(|x| format!("(succ {x} {})\n", x+1)).collect();

    s.load_all_sexpr(SPACE_EXPRS.as_bytes()).unwrap();
    s.load_all_sexpr(SUCCS.as_bytes()).unwrap();

    let mut t0 = Instant::now();
    let steps = s.metta_calculus(1000000000000000);
    println!("elapsed {} steps {} size {}", t0.elapsed().as_millis(), steps, s.btm.val_count());

    // let mut v = vec![];
    // s.dump_all_sexpr(&mut v).unwrap();
    // let res = String::from_utf8(v).unwrap();
    //
    // println!("result: {res}");
}


fn main() {
    env_logger::init();

    // pddl_ts("/home/adam/Projects/ThesisPython/cache/gripper-strips/transition_systems/");
    exponential(32);
    exponential_fringe(15);
    linear_fringe_alternating(15);
    linear_alternating(15);

    // lookup();
    // positive();
    // negative();
    // bipolar();
    // positive_equal();
    // negative_equal();
    // bipolar_equal();
    //
    // two_positive_equal();
    // two_positive_equal_crossed();
    // two_bipolar_equal_crossed();
    //
    // process_calculus_reverse();
    // logic_query();
    // bc0();
    // bc1();
    // bc2();
    // bc3();
    //
    // cm0();
    // bc0();
    // bc1();

    // lens_aunt();
    // lens_composition();

    bench_transitive_no_unify(50000, 1000000);
    bench_clique_no_unify(200, 3600, 5);
    bench_finite_domain(10_000);
    bench_process_calculus(1000, 200, 200);

    // #[cfg(all(feature = "nightly"))]
    // json_upaths_smoke();
    // #[cfg(all(feature = "nightly"))]
    // json_upaths("/mnt/data/enwiki-20231220-pages-articles-links/cqls.json", "/mnt/data/enwiki-20231220-pages-articles-links/cqls.upaths");
    /*
DESIRED!!!
elapsed 624 steps 32 size 265723
elapsed 1574 steps 46 size 803777
elapsed 1 steps 46 size 63
elapsed 1 steps 46 size 63
constructed 50000 nodes 1000000 edges
trans elapsed 18342529 µs
detect trans elapsed 12773343 µs
trans 19917429 detected trans 8716
constructed 200 nodes 3600 edges
executing query (exec 0 (, (edge $x0 $x1) (edge $x0 $x2) (edge $x1 $x2)) (, (3-clique $x0 $x1 $x2)))
found 7824 3-cliques (expected 7770) in 48841 µs
executing query (exec 0 (, (edge $x0 $x1) (edge $x0 $x2) (edge $x0 $x3) (edge $x1 $x2) (edge $x1 $x3) (edge $x2 $x3)) (, (4-clique $x0 $x1 $x2 $x3)))
found 2320 4-cliques (expected 2260) in 1189748 µs
executing query (exec 0 (, (edge $x0 $x1) (edge $x0 $x2) (edge $x0 $x3) (edge $x0 $x4) (edge $x1 $x2) (edge $x1 $x3) (edge $x1 $x4) (edge $x2 $x3) (edge $x2 $x4) (edge $x3 $x4)) (, (5-clique $x0 $x1 $x2 $x3 $x4)))
found 102 5-cliques (expected 94) in 26444056 µs
42840
0
1
2
3
4
5
6
7
 (10000 inputs) in 87128 µs
200+200 (1000 steps) in 45372051 µs result: (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

unifications 20964581, transitions 1129014058

     */
    return;

    let mut s = Space::new();
    const space: &str = r#"
(exec P0 (, (sudoku p2 input (row ($r $x1 $x2 $x3 $x4 $x5 $x6 $x7 $x8 $x9)))) 
         (, (cell 1 $r $x1) (cell 2 $r $x2) (cell 3 $r $x3)  (cell 4 $r $x4) (cell 5 $r $x5) (cell 6 $r $x6)  (cell 7 $r $x7) (cell 8 $r $x8) (cell 9 $r $x9)  ))

(exec P1 (, (cell $c $r _))
         (, (cell $c $r 1) (cell $c $r 2) (cell $c $r 3)  (cell $c $r 4) (cell $c $r 5) (cell $c $r 6)  (cell $c $r 7) (cell $c $r 8) (cell $c $r 9)  ))

(exec P2 (, (cell $ca $r $va) (cell $cb $r $vb))
         (, (Deduction remaining (cell $ca $r $x) (cell $cb $r $y))))

"#;
    //
    // (exec P2 (, (cell $ca $r $va) (cell $cb $r $vb))
    // (, (Deduction remaining (cell $ca $r X) (cell $cb $r Y))))

    // (exec P3 (, (cell $c $ra $va) (cell $c $rb $vb))
    // (, (Deduction remaining (cell $c $ra X) (cell $c $rb Y))))
    // 
    // 
    // (exec P4 (, (cell $c $ra $va) (cell $c $rb $vb))
    // (, (Deduction remaining (cell $c $ra $x) (cell $c $rb $y))))
    // (block 0 1 1) (block 0 1 2) (block 0 1 3)
    // (block 0 2 1) (block 0 2 2) (block 0 2 3)
    // (block 0 3 1) (block 0 3 2) (block 0 3 3)

    const sudoku_p2: &str = r#"
1 2 3 4 5 6 7 8 9
_ 5 _ _ _ _ 9 _ _
_ _ _ 8 3 1 2 5 _
2 _ 7 _ _ _ 6 1 3
9 _ 6 _ _ 7 _ 3 _
1 2 8 _ _ _ 7 _ _
_ _ _ 2 _ 4 _ 9 6
8 1 _ 7 6 _ _ 2 9
7 3 4 _ 2 8 _ _ 1
_ _ _ 4 1 _ _ _ _"#;
    
    s.load_csv(sudoku_p2.as_bytes(), expr!(s, "$"), expr!(s, "[4] sudoku p2 input [2] row _1"), b' ').unwrap();
    
    s.load_sexpr(space.as_bytes(), expr!(s, "$"), expr!(s, "_1")).unwrap();

    s.metta_calculus(100);
    
    // println!("size {:?}", s.btm.val_count());
    
    let mut v = vec![];
    s.dump_sexpr(expr!(s, "$"), expr!(s, "_1"), &mut v);
    
    println!("{}", String::from_utf8(v).unwrap());
    
    return;
    /*let mut s = Space::new();
    const space: &str = r#"
(= (add (S $x) $y) (S (add $x $y)))
(= (add Z $y) $y)
(= (mul (S (S $x)) $y) (add $y (mul (S $x) $y)))
(= (mul (S Z) $y) $y)
(= (mul Z $y) Z)

(PC (Cat (Point3D 39 9504 34980)))
(PC (Cat (Point3D 39 9504 34980)))
(PC (Cat (Point3D 39 9480 34980)))
(PC (Cat (Point3D 39 4830 34980)))
(PC (Cat (Point3D 39 9504 34980)))
(PC (Cat (Point3D 39 3230 34923)))
(PC (Cat (Point3D 27 3410 34900)))
(PC (Cat (Point3D 27 3410 34964)))
(PC (Cat (Point3D 23 3459 34932)))

"#;

    s.load_sexpr(space.as_bytes(), expr!(s, "$"), expr!(s, "_1")).unwrap();


    let [(t1, _), (t2, _)] = &s.token_bfs(&[], expr!(s, "$"))[..] else { panic!() };
    println!("{:?}", s.token_bfs(&t1[..], expr!(s, "$")));
    println!("{:?}", s.token_bfs(t2, expr!(s, "$")));

    // let mut v = vec![];
    // s.dump_sexpr(expr!(s, "$"), expr!(s, "_1"), &mut v).unwrap();
    //
    // println!("{}", String::from_utf8(v).unwrap());
    return;*/
    /*

    let mut s = Space::new();
    const facts: &str = "0,1\n1,2\n2,3\n3,4\n4,5\n5,0\n5,6\n6,7\n7,8\n8,9\n9,10\n10,7";
    const expected_same_clique: &str = "...";
    const expected_reachable: &str = "...";


    s.load_csv(facts.as_bytes(), expr!(s, "[2] $ $"), expr!(s, "[3] edge _1 _2")).unwrap();

    // (reachable $x $y) :- (edge $x $y)
    // (reachable $x $y) :- (edge $x $z), (reachable $z $y)
    // (same_clique $x $y) :- (reachable $x $y), (reachable $y $x)
    s.datalog(&[
        expr!(s, "[3] -: [2] , [3] edge $ $ [3] reachable _1 _2"),
        expr!(s, "[3] -: [3] , [3] edge $ $ [3] reachable _2 $ [3] reachable _1 _3"),
        expr!(s, "[3] -: [3] , [3] reachable $ $ [3] reachable _2 _1 [3] same_clique _1 _2"),
    ]);

    let mut v = vec![];
    s.dump_sexpr(expr!(s, "$"), expr!(s, "_1"), &mut v).unwrap();

    println!("{}", String::from_utf8(v).unwrap());
    return;
     */
    /*
        const csv_contents: &str = r#"1,2
10,20
10,30"#;

    const sexpr_contents: &str = r#"(useful (Foo 1))
(useless ((- o -) (- o -)))"#;

    let mut s = Space::new();
    // s.load_csv(csv_contents.as_bytes(), expr!(s, "[2] $ $"), expr!(s, "[2] mycsv [3] my precious _2")).unwrap();
    s.load_csv(csv_contents.as_bytes(), expr!(s, "[2] 10 $"), expr!(s, "[2] data [2] mycsv [3] my precious _1")).unwrap();

    s.load_sexpr(sexpr_contents.as_bytes(), expr!(s, "[2] useful $"), expr!(s, "[2] data [2] mysexpr _1")).unwrap();

    let mut v = vec![];
    s.dump_sexpr(expr!(s, "[2] data [2] mycsv $"), expr!(s, "_1"), &mut v).unwrap();

    println!("{}", String::from_utf8(v).unwrap());
    return;
    */
    // println!("{}", mork_bytestring::serialize(&[3, 3, 200, 84, 80, 55, 51, 45, 65, 83, 49, 204, 103, 101, 110, 101, 95, 110, 97, 109, 101, 95, 111, 102, 200, 0, 0, 0, 0, 4, 129, 29, 29, 4, 195, 83, 80, 79, 200, 0, 0, 0, 0, 4, 129, 29, 29, 200]));
    //
    return;
    // let mut s = Space::new();

    // let tree = pathmap::arena_compact::ArenaCompactTree::open_mmap("/run/media/adam/43323a1c-ad7e-4d9a-b3c0-cf84e69ec61a/whole_flybase.tree").unwrap();
    // 
    // let iter_tree_start = Instant::now();
    // let mut rz = tree.read_zipper();
    // let mut npaths = 0usize; 
    // let mut nbytes = 0; 
    // while rz.to_next_val() {
    //     nbytes += rz.path().len();
    //     npaths += 1;
    //     if npaths % 10_000_000 == 0 {
    //         println!("npaths {}", npaths);
    //     }
    // }
    // println!("iterating tree backup {} {} took {}", npaths, nbytes, iter_tree_start.elapsed().as_secs());
    
    // let restore_paths_start = Instant::now();
    // let restored = s.restore_paths("/run/media/adam/43323a1c-ad7e-4d9a-b3c0-cf84e69ec61a/whole_flybase.paths.gz").unwrap();
    // println!("restored paths {:?} {}", restored, restore_paths_start.elapsed().as_secs());
    
    // let everythingf = std::fs::File::open("/run/media/adam/43323a1c-ad7e-4d9a-b3c0-cf84e69ec61a/whole_flybase.jsonl").unwrap();
    // let everythingfs = unsafe { memmap2::Mmap::map(&everythingf).unwrap() };
    // let load_compressed = Instant::now();
    // println!("done {:?} {}", s.load_jsonl(everythingfs.as_ref()).unwrap(), load_compressed.elapsed().as_secs());
    // // done (326728210, 6798095370) 1934s
    // 
    // let backup_paths_start = Instant::now();
    // println!("{:?}", s.backup_paths("/run/media/adam/43323a1c-ad7e-4d9a-b3c0-cf84e69ec61a/whole_flybase.paths.gz").unwrap());
    // println!("paths backup took {}", backup_paths_start.elapsed().as_secs());
    // // SerializationStats { bytes_out: 42_741_214_528, bytes_in: 355_357_500_042, path_count: 6798095370 }
    // //                                                           328_165_118_562
    // // paths backup took 4619s
    // 
    // let backup_tree_start = Instant::now();
    // println!("{:?}", s.backup_tree("/run/media/adam/43323a1c-ad7e-4d9a-b3c0-cf84e69ec61a/whole_flybase.tree").unwrap());
    // println!("tree backup took {}", backup_tree_start.elapsed().as_secs());
    // // tree backup took 3033
    // 
    // let backup_dag_start = Instant::now();
    // println!("{:?}", s.backup("/run/media/adam/43323a1c-ad7e-4d9a-b3c0-cf84e69ec61a/").unwrap());
    // println!("dag backup took {}", backup_dag_start.elapsed().as_secs());


    // let restore_symbols_start = Instant::now();
    // println!("restored symbols {:?}", s.restore_symbols("/dev/shm/combined.symbols.zip").unwrap());
    // println!("symbols backup took {}", restore_symbols_start.elapsed().as_secs());
    // println!("{:?}", s.sm.get_sym(b"SPO"));
    // println!("{:?}", s.sm.get_sym(b"IL9R-207"));
    // let bucket_map::serialization::Tables { to_symbol, to_bytes } = s.sm.reveal_tables();
    // println!("to_symbol.len() = {}; to_bytes.len() = {}", to_symbol.len(), to_bytes.len());
    // println!("to_symbol.first().unwrap().val_count() = {:?}; to_bytes.first().unwrap().val_count() = {:?}", to_symbol.last().unwrap().val_count(), to_bytes.last().unwrap().val_count());

    // for to_symbol_part in to_symbol {
    //     print!("{},", to_symbol_part.val_count());
    // }

    // for to_byte_part in to_bytes {
    //     print!("{},", to_byte_part.val_count());
    // }

    // let mut to_symbol_rz = to_symbol.last().unwrap().read_zipper();
    // while let Some(v) = to_symbol_rz.to_next_val() {
    //     println!("{:?} {:?}", std::str::from_utf8(to_symbol_rz.path()).unwrap_or(format!("{:?}", to_symbol_rz.path()).as_str()), v)
    // }

    // let restore_paths_start = Instant::now();
    // println!("restored paths {:?}", s.restore_paths("/dev/shm/combined_ni.paths.gz").unwrap());
    // println!("paths restore took {}", restore_paths_start.elapsed().as_secs());
    // s.statistics();

    // let load_labels_start = Instant::now();
    // println!("{:?}", s.load_neo4j_node_labels("bolt://localhost:7687", "neo4j", "morkwork").unwrap());
    // println!("loading labels took {}", load_labels_start.elapsed().as_secs());
    // s.statistics();

    // let load_start = Instant::now();
    // println!("{:?}", s.load_neo4j_triples("bolt://localhost:7687", "neo4j", "morkwork").unwrap());
    // println!("loading took {}", load_start.elapsed().as_secs());
    // s.statistics();
    // let mut rz = s.btm.read_zipper_at_path(&[item_byte(Tag::Arity(4)), item_byte(Tag::SymbolSize(3)), b'S', b'P', b'O']);
    // println!("SPO's {}", rz.val_count());
    // rz.to_next_val();
    // println!("{}", mork_bytestring::serialize(rz.origin_path().unwrap()));
    //
    // let property_load_start = Instant::now();
    // println!("{:?}", s.load_neo4j_node_properties("bolt://localhost:7687", "neo4j", "morkwork").unwrap());
    // println!("property loading took {}", property_load_start.elapsed().as_secs());
    // s.statistics();


    // work(&mut s);

    // s.statistics();
    // s.done();
    // let restore_start = Instant::now();
    // s.restore("/dev/shm/");
    // println!("restore took {}", restore_start.elapsed().as_secs());
    // s.statistics();




    // let backup_paths_start = Instant::now();
    // println!("{:?}", s.backup_paths("/dev/shm/combined_ni.paths.gz").unwrap());
    // println!("paths backup took {}", backup_paths_start.elapsed().as_secs());
    //
    // let backup_symbols_start = Instant::now();
    // println!("{:?}", s.backup_symbols("/dev/shm/combined.symbols.zip").unwrap());
    // println!("symbols backup took {}", backup_symbols_start.elapsed().as_secs());

    // let backup_start = Instant::now();
    // s.backup("/dev/shm/combined.remydag");
    // println!("backup took {}", backup_start.elapsed().as_secs());
}

/*
restored paths DeserializationStats { bytes_in: 4061021063, bytes_out: 34621879507, path_count: 978700221 }
paths restore took 135
val count 978700221
add gene name index took 8637 ms
val count 979015756
all_related_to_gene_start 193 µs
res0 count 142
add exon chr index took 32 s
val count 1054962128
add ops index took 91 s
val count 1386253656
transitive_chr1 7691 ms
res1 count 40172978
q0 33295 µs
res2 count 151956

 */