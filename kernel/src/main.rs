use std::collections::HashSet;
// use std::future::Future;
// use std::task::Poll;
use std::time::Instant;
use pathmap::trie_map::BytesTrieMap;
use pathmap::zipper::{Zipper, ZipperAbsolutePath, ZipperIteration, ZipperMoving};
use mork_frontend::bytestring_parser::Parser;
use mork::{expr, prefix, sexpr};
use mork::prefix::Prefix;
use mork::space::{transitions, unifications, writes, Space};
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

fn process_calculus_bench(steps: usize, x: usize, y: usize) {
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
    println!("unifications {}, instructions {}", unsafe { unifications }, unsafe { transitions });
    // (badbad)
    // 200+200 (1000 steps) in 42716559 µs
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
        s.load_sexpr(&*metta_mmap, expr!(s, "$"), expr!(s, format!("[3] U {} _1", &name[..name.len()-6]).as_str())).unwrap();
    }

    let SPACE = r#"
    (exec (action 0) (, (U $d (transition $s (drop $obj $room $gripper) $t))
                        (U $d (value (carry $obj $gripper) T $s))
                        (U $d (value (at-robby $room) T $s))
                        (U $d (value (at $obj $room) T $t))
                        (U $d (value (free $gripper) T $t))
                        (U $d (value (carry $obj) F $t)))
                     (, ((C 0) $d ($s $obj $room $gripper $t))))

    (exec (action 1) (, (U $d (transition $s (move $from $to) $t))
                        (U $d (value (at-robby $from) T $s))
                        (U $d (value (at-robby $from) F $t))
                        (U $d (value (at-robby $to) T $t)))
                     (, ((C 1) $d ($s $from $to $t))))

    (exec (action 2) (, (U $d (transition $s (pick $obj $room $gripper) $t))
                        (U $d (value (at $obj $room) T $s))
                        (U $d (value (at-robby $room) T $s))
                        (U $d (value (free $gripper) T $s))
                        (U $d (value (carry $obj $gripper) T $t))
                        (U $d (value (free $gripper) F $t))
                        (U $d (value (at $obj $room) F $t)))
                     (, ((C 2) $d ($s $obj $room $gripper $t))))
    "#;
    s.load_all_sexpr(SPACE.as_bytes()).unwrap();

    s.metta_calculus(3);

    let mut v = vec![];
    // s.dump_all_sexpr(&mut v).unwrap();
    // s.dump_sexpr(expr!(s, "[3] U p-3-0 $"), expr!(s, "_1"), &mut v);
    s.dump_sexpr(expr!(s, "[3] [2] C $ p-3-0 $"), expr!(s, "[2] _1 _2"), &mut v);
    let res = String::from_utf8(v).unwrap();

    println!("result: {res}");
    /*
       WIP
     */
}

fn stv_roman() {
    let mut s = Space::new();
    let SPACE = r#"
    (exec (step (0 cpu))
      (, (goal (CPU $f $arg $res)) (fun ($f $arg ($b1 $b2) $res)) (fun $b1) (fun $b2))
      (, (ev $res)))

    (fun (mp-formula ((STV $sa $ca) (STV $sb $cb)) ((mul ($sa $sb) $so) (mul ($ca $cb) $co)) (STV $so $co)))

    (goal (CPU mp-formula ((STV 0.5 0.5) (STV 0.5 0.5)) $res))
    "#;
    s.load_all_sexpr(SPACE.as_bytes()).unwrap();
    // let mut math_expr_buf = vec![];
    // std::fs::File::open("/home/adam/Downloads/math_relations.metta").unwrap().read_to_end(&mut math_expr_buf).unwrap();
    // s.load_sexpr(&math_expr_buf[..], expr!(s, "$"), expr!(s, "_1")).unwrap();
    s.load_sexpr("(fun (mul (0.5 0.5) 0.2))".as_bytes(), expr!(s, "$"), expr!(s, "_1")).unwrap();

    s.metta_calculus(1);

    let mut v = vec![];
    s.dump_sexpr(expr!(s, "[2] ev $"), expr!(s, "_1"), &mut v);
    let res = String::from_utf8(v).unwrap();
    println!("result: {res}");
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

fn mm1_forward() {
    // Program: universe, typed constructors, axioms (curried), tiny pipeline, and final assembly.
    const P: &str = r#"
(kb (: ⟨+⟩ (-> ⟨term⟩ (-> ⟨term⟩ ⟨term⟩))))
(kb (: ⟨=⟩ (-> ⟨term⟩ (-> ⟨term⟩ ⟨wff⟩))))
(kb (: ⟨t⟩ ⟨term⟩))
(kb (: ⟨0⟩ ⟨term⟩))

(kb (: ⟨tpl⟩ (-> (: $x ⟨term⟩) (-> (: $y ⟨term⟩)
                      (: (⟨+⟩ $x $y) ⟨term⟩)))))
(kb (: ⟨weq⟩ (-> (: $x ⟨term⟩) (-> (: $y ⟨term⟩)
                      (: (⟨=⟩ $x $y) ⟨wff⟩)))))
(kb (: ⟨wim⟩ (-> (: $P ⟨wff⟩) (-> (: $Q ⟨wff⟩)
                      (: (⟨->⟩ $P $Q) ⟨wff⟩)))))

(kb (: ⟨a2-curry⟩ (-> (: $a ⟨term⟩)
                  (: (⟨=⟩ (⟨+⟩ $a ⟨0⟩) $a) ⟨|-⟩))))
(kb (: ⟨a1-curry⟩ (-> (: $a ⟨term⟩) (-> (: $b ⟨term⟩) (-> (: $c ⟨term⟩)
                  (: (⟨->⟩ (⟨=⟩ $a $b) (⟨->⟩ (⟨=⟩ $a $c) (⟨=⟩ $b $c))) ⟨|-⟩))))))
(kb (: ⟨mp-curry⟩ (-> (: $P ⟨wff⟩) (-> (: $Q ⟨wff⟩)
                  (-> (: $P ⟨|-⟩) (-> (: (⟨->⟩ $P $Q) ⟨|-⟩) (: $Q ⟨|-⟩)))))))

(kb (: ⟨a2⟩ (-> (: $a ⟨term⟩) (: (⟨=⟩ (⟨+⟩ $a ⟨0⟩) $a) ⟨|-⟩))))
(kb (: ⟨a1⟩ (-> (: $a ⟨term⟩) (: $b ⟨term⟩) (: $c ⟨term⟩) (: (⟨->⟩ (⟨=⟩ $a $b) (⟨->⟩ (⟨=⟩ $a $c) (⟨=⟩ $b $c))) ⟨|-⟩))))
(kb (: ⟨mp⟩ (-> (: $P ⟨wff⟩) (: $Q ⟨wff⟩) (: $P ⟨|-⟩) (: (⟨->⟩ $P $Q) ⟨|-⟩) (: $Q ⟨|-⟩))))

(exec (0 lift) (, (kb (: $t $T))) (, (ev (: $t $T))))

(exec (1 tpl-apply)
  (, (ev (: $x ⟨term⟩))
     (ev (: $y ⟨term⟩)))
  (, (ev (: (⟨+⟩ $x $y) ⟨term⟩))))

(exec (1 weq-apply)
  (, (ev (: $a ⟨term⟩))
     (ev (: $b ⟨term⟩)))
  (, (ev (: (⟨=⟩ $a $b) ⟨wff⟩))))

(exec (1 wim-apply)
  (, (ev (: $P ⟨wff⟩))
     (ev (: $Q ⟨wff⟩)))
  (, (ev (: (⟨->⟩ $P $Q) ⟨wff⟩))))

(exec (1 a2-instantiate-t)
  (, (ev (: $a ⟨term⟩)))
  (, (ev (: (⟨=⟩ (⟨+⟩ $a ⟨0⟩) $a) ⟨|-⟩))))

(exec (1 a1-instantiate-PtoQ)
  (, (ev (: $a ⟨term⟩))
     (ev (: $b ⟨term⟩))
     (ev (: $c ⟨term⟩)))
  (, (ev (: (⟨->⟩ (⟨=⟩ $a $b)
               (⟨->⟩ (⟨=⟩ $a $c)
                       (⟨=⟩ $b $c))) ⟨|-⟩))))

(exec (2 derive-P-to-Q-direct3)
  (, (ev (: $P ⟨wff⟩))
     (ev (: $P ⟨|-⟩))
     (ev (: (⟨->⟩ $P $IMP) ⟨|-⟩))
     (ev (: $IMP ⟨wff⟩)))
  (, (ev (: $IMP ⟨|-⟩))))

(exec (3 assemble-final-proof-direct)
  (, (ev (: $P ⟨wff⟩))
     (ev (: $P ⟨|-⟩))
     (ev (: (⟨->⟩ $P $Q) ⟨|-⟩))
     (ev (: $Q ⟨wff⟩)))
  (, (ev (: $Q ⟨|-⟩))))
"#;


    let mut s = Space::new();
    let t0 = Instant::now();
    s.load_all_sexpr(P.as_bytes()).unwrap();

    // Targets (kept identical to mm1())
    let want_ev_term_tplus0    = "(ev (: (⟨+⟩ ⟨t⟩ ⟨0⟩) ⟨term⟩))";
    let want_ev_wff_p          = "(ev (: (⟨=⟩ (⟨+⟩ ⟨t⟩ ⟨0⟩) ⟨t⟩) ⟨wff⟩))";
    let want_ev_wff_q          = "(ev (: (⟨=⟩ ⟨t⟩ ⟨t⟩) ⟨wff⟩))";
    let want_ev_proof_p        = "(ev (: (⟨=⟩ (⟨+⟩ ⟨t⟩ ⟨0⟩) ⟨t⟩) ⟨|-⟩))";
    let want_ev_proof_ptoq     = "(ev (: (⟨->⟩ (⟨=⟩ (⟨+⟩ ⟨t⟩ ⟨0⟩) ⟨t⟩) (⟨=⟩ ⟨t⟩ ⟨t⟩)) ⟨|-⟩))";
    let want_ev_proof_ptoptoq  = "(ev (: (⟨->⟩ (⟨=⟩ (⟨+⟩ ⟨t⟩ ⟨0⟩) ⟨t⟩) (⟨->⟩ (⟨=⟩ (⟨+⟩ ⟨t⟩ ⟨0⟩) ⟨t⟩) (⟨=⟩ ⟨t⟩ ⟨t⟩))) ⟨|-⟩))";
    let want_final_evidence    = "(ev (: (⟨=⟩ ⟨t⟩ ⟨t⟩) ⟨|-⟩)";

    println!("=== MM1 (forward): Proving ⊢ (t = t) ===");

    let mut ticks = 0usize;
    loop {
        ticks += 1;
        let t1 = Instant::now();
        let n = s.metta_calculus(1);
        println!("executing step {} took {} ms (unifications {}, writes {}, transitions {})", ticks, t1.elapsed().as_millis(), unsafe { unifications }, unsafe { writes }, unsafe { transitions });

        if n == 1 { continue } // comment out if you want the analysis at every step

        println!("space size {}", s.btm.val_count());
        let total_t = t0.elapsed();

        let mut tmut = Vec::new();
        // trying to get: (ev (: (⟨=⟩ (⟨+⟩ ⟨t⟩ ⟨0⟩) ⟨t⟩) ⟨|-⟩))
        s.dump_sexpr(
            expr!(s, "[2] ev [3] : [3] ⟨=⟩ $ $ ⟨|-⟩"),  // Pattern
            expr!(s, "[2] ev [3] : [3] ⟨=⟩ _1 _2 ⟨|-⟩"),  // Template: full reconstruction
            &mut tmut
        );

        let result = String::from_utf8(tmut).unwrap();
        println!("Query result (tick {}): {}", ticks, result);

        for line in result.lines() {
            let trimmed = line.trim();
            if trimmed == want_ev_proof_p {
                println!("✅ EXACT MATCH found at tick {}: {}", ticks, trimmed);
                break;
            }
        }

        let mut proof_ptoq_check = Vec::new();
        s.dump_sexpr(
            expr!(s, "[2] ev [3] : [3] ⟨->⟩ [3] ⟨=⟩ [3] ⟨+⟩ ⟨t⟩ ⟨0⟩ ⟨t⟩ [3] ⟨=⟩ ⟨t⟩ ⟨t⟩ ⟨|-⟩"),  // Pattern
            expr!(s, "[2] ev [3] : [3] ⟨->⟩ [3] ⟨=⟩ [3] ⟨+⟩ ⟨t⟩ ⟨0⟩ ⟨t⟩ [3] ⟨=⟩ ⟨t⟩ ⟨t⟩ ⟨|-⟩"),  // Template: return same expression
            &mut proof_ptoq_check
        );

        if !proof_ptoq_check.is_empty() {
            let result = String::from_utf8(proof_ptoq_check).unwrap();
            println!("🎯 Found P→Q proof: {}", result.trim());
        } else {
            println!("P→Q proof not found yet");
        }

        let mut buf = Vec::new();
        s.dump_all_sexpr(&mut buf).unwrap();
        let dump = String::from_utf8_lossy(&buf);

        let line_has = |needle: &str| dump.lines().any(|l| l.trim_start().starts_with(needle));

        let have_tplus0_term  = line_has(want_ev_term_tplus0);
        let have_wff_p_ev     = line_has(want_ev_wff_p);
        let have_wff_q_ev     = line_has(want_ev_wff_q);
        let have_proof_p_ev   = line_has(want_ev_proof_p);
        let have_ptoq_ev      = line_has(want_ev_proof_ptoq);
        let have_ptoptoq_ev   = line_has(want_ev_proof_ptoptoq);
        let have_final        = line_has(want_final_evidence);

        if have_final {
            println!("\n== mm1 (forward): ✅ SUCCESS in {:?} after {} tick(s) ==", total_t, ticks);
            println!("  (+ t 0) : term ............. {}", if have_tplus0_term { "✓" } else { "—" });
            println!("  wff_P (ev) ................. {}", if have_wff_p_ev { "✓" } else { "—" });
            println!("  wff_Q (ev) ................. {}", if have_wff_q_ev { "✓" } else { "—" });
            println!("  proof_P (a2@t, ev) ......... {}", if have_proof_p_ev { "✓" } else { "—" });
            println!("  proof_PtoQ (a1, ev) ........ {}", if have_ptoq_ev { "✓" } else { "—" });
            println!("  proof_PtoPtoQ (a1, ev) ..... {}", if have_ptoptoq_ev { "✓" } else { "—" });

            println!("\n--- Final evidence confirmation ---");
            println!("✅ Successfully derived ⊢ (t = t)");

            println!("\n--- Full Final State Dump ---");
            print!("{dump}");
            break;
        }

        if n == 0 || ticks >= 128 {
            println!("\n== mm1 (forward): — FAILURE in {:?} after {} tick(s) ==", t0.elapsed(), ticks);
            println!("  (+ t 0) : term ............. {}", if have_tplus0_term { "✓" } else { "—" });
            println!("  wff_P (ev) ................. {}", if have_wff_p_ev { "✓" } else { "—" });
            println!("  wff_Q (ev) ................. {}", if have_wff_q_ev { "✓" } else { "—" });
            println!("  proof_P (a2@t, ev) ......... {}", if have_proof_p_ev { "✓" } else { "—" });
            println!("  proof_PtoQ (a1, ev) ........ {}", if have_ptoq_ev { "✓" } else { "—" });
            println!("  proof_PtoPtoQ (a1, ev) ..... {}", if have_ptoptoq_ev { "✓" } else { "—" });

            if !have_final {
                println!("\n❌ Failed to derive ⊢ (t = t)");
            }

            println!("\n--- Full Final State Dump ---");
            print!("{dump}");
            break;
        }
    }
}


use std::ffi::OsStr;
use std::ffi::OsString;
use serde::{Serialize, Deserialize};
use clap::{Args, Parser as CLAParser, Subcommand, ValueEnum};

#[derive(Debug, Serialize, Deserialize, Clone)]
enum Format { MeTTa, JSON, CSV, UPaths, Paths, ACT }

#[derive(Debug, CLAParser)] // requires `derive` feature
#[command(name = "mork")]
#[command(about = "MORK CLI", long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Debug, Subcommand)]
enum Commands {
    #[command(arg_required_else_help = true)]
    Bench {
        #[arg(default_missing_value = "default")]
        only: String,
    },
    Test {
    },
    #[command(arg_required_else_help = true)]
    Run {
        input_path: String,
        #[arg(long, default_value_t = 1000000000000000)]
        steps: usize,
        #[arg(long, default_value_t = 1)]
        instrumentation: usize,
        output_path: Option<String>,
    },
    #[command(arg_required_else_help = true)]
    Convert {
        #[arg(default_missing_value = "metta")]
        input_format: String,
        #[arg(default_missing_value = "metta")]
        output_format: String,
        #[arg(long, short='i', default_value_t = 1)]
        instrumentation: usize,
        input_path: String,
        output_path: Option<String>
    }
}


fn main() {
    env_logger::init();

    // pddl_ts("/home/adam/Projects/ThesisPython/cache/gripper-strips/transition_systems/");
    // stv_roman();
    // mm1_forward();
    // return;

    let args = Cli::parse();

    match args.command {
        Commands::Bench { only } => {
            #[cfg(debug_assertions)]
            println!("WARNING running in debug, if unintentional, build with --release");
            let mut selected: HashSet<&str> = only.split(",").collect();
            if selected.remove("all") { selected.extend(&["transitive", "clique", "finite_domain", "process_calculus", "exponential", "exponential_fringe"]) }
            if selected.remove("default") { selected.extend(&["transitive", "clique", "finite_domain", "process_calculus"]) }

            for b in selected {
                match b {
                    "transitive" => { bench_transitive_no_unify(50000, 1000000); }
                    "clique" => { bench_clique_no_unify(200, 3600, 5); }
                    "finite_domain" => { bench_finite_domain(10_000); }
                    "process_calculus" => { process_calculus_bench(1000, 200, 200); }
                    "exponential" => { exponential(32); }
                    "exponential_fringe" => { exponential_fringe(15); }
                    s => { println!("bench not known: {s}") }
                }
            }
        }
        Commands::Test { .. } => {
            #[cfg(not(debug_assertions))]
            println!("WARNING running in release or -O3, if unintentional, build without --release and with the alternative .cargo rustflags");
            lookup();
            positive();
            negative();
            bipolar();
            positive_equal();
            negative_equal();
            bipolar_equal();

            two_positive_equal();
            two_positive_equal_crossed();
            two_bipolar_equal_crossed();

            process_calculus_reverse();
            logic_query();

            bc0();
            cm0();
        }
        Commands::Run { input_path, steps, instrumentation, output_path } => {
            #[cfg(debug_assertions)]
            println!("WARNING running in debug, if unintentional, build with --release");
            let mut s = Space::new();
            let f = std::fs::File::open(&input_path).unwrap();
            let mmapf = unsafe { memmap2::Mmap::map(&f).unwrap() };
            s.load_all_sexpr(&*mmapf);
            if instrumentation > 0 { println!("loaded {} expressions", s.btm.val_count()) }
            println!("loaded {:?} ; running and outputing to {:?}", &input_path, output_path.as_ref().or(Some(&"stdout".to_string())));
            let t0 = Instant::now();
            let mut performed = s.metta_calculus(steps);
            println!("executing {performed} steps took {} ms (unifications {}, writes {}, transitions {})", t0.elapsed().as_millis(), unsafe { unifications }, unsafe { writes }, unsafe { transitions });
            if instrumentation > 0 { println!("dumping {} expressions", s.btm.val_count()) }
            if output_path.is_none() {
                let mut v = vec![];
                s.dump_all_sexpr(&mut v).unwrap();
                let res = String::from_utf8(v).unwrap();
                println!("result:\n{res}");
            } else {
                let f = std::fs::File::create(&output_path.unwrap()).unwrap();
                let mut w = std::io::BufWriter::new(f);
                s.dump_all_sexpr(&mut w).unwrap();
            }
        }
        Commands::Convert { input_format, output_format, instrumentation, input_path, output_path } => {
            #[cfg(debug_assertions)]
            println!("WARNING running in debug, if unintentional, build with --release");

            let input_path_extension = input_path.rfind(".").map(|i| &input_path[i+1..]);
            if input_path_extension.unwrap_or("") != input_format.as_str() { println!("input format {} does not coincide with the extension {:?}", input_format, input_path_extension); }
            let some_output_path = output_path.unwrap_or_else(|| format!("{}.{}", &input_path[..input_path.len()-input_path_extension.unwrap_or("").len()], output_format));
            let output_path_extension = some_output_path.rfind(".").map(|i| &some_output_path[i+1..]);
            if output_path_extension.unwrap_or("") != output_format.as_str() { println!("output format {} does not coincide with the extension {:?}", output_format, output_path_extension); }
            
            match (input_format.as_str(), output_format.as_str()) {
                ("metta", "metta" | "act" | "paths") => {
                    let mut s = Space::new();
                    let f = std::fs::File::open(&input_path).unwrap();
                    let mmapf = unsafe { memmap2::Mmap::map(&f).unwrap() };
                    s.load_all_sexpr(&*mmapf);
                    println!("done loading in memory");
                    if instrumentation > 0 { println!("dumping {} expressions", s.btm.val_count()) }
                    
                    match output_format.as_str() {
                        "metta" => {
                            let f = std::fs::File::create(&some_output_path).unwrap();
                            let mut w = std::io::BufWriter::new(f);
                            s.dump_all_sexpr(&mut w).unwrap();
                        }
                        "act" => {
                            s.backup_tree(some_output_path);
                        }
                        "paths" => {
                            s.backup_paths(some_output_path);
                        }
                        _ => { unreachable!() }
                    }
                }
                ("paths", "metta" | "act" | "paths") => {
                    let mut s = Space::new();
                    s.restore_paths(&input_path);
                    println!("done loading in memory");
                    if instrumentation > 0 { println!("dumping {} expressions", s.btm.val_count()) }

                    match output_format.as_str() {
                        "metta" => {
                            let f = std::fs::File::create(&some_output_path).unwrap();
                            let mut w = std::io::BufWriter::new(f);
                            s.dump_all_sexpr(&mut w).unwrap();
                        }
                        "act" => {
                            s.backup_tree(some_output_path);
                        }
                        "paths" => {
                            s.backup_paths(some_output_path);
                        }
                        _ => { unreachable!() }
                    }
                }
                #[cfg(all(feature = "nightly"))]
                (Format::JSON, Format::UPaths) => {
                    #[cfg(all(feature = "nightly"))]
                    // json upaths /mnt/data/enwiki-20231220-pages-articles-links/cqls.json /mnt/data/enwiki-20231220-pages-articles-links/cqls.upaths
                    json_upaths(input_path, output_path);
                    
                }
                (_, _) => { panic!("unsupported conversion") }
            }
        }
    }
    return;
}
