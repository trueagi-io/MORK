use mork::{expr, prefix, sexpr};
use mork::space::{transitions, unifications, writes, Space, ACT_PATH};
use mork_frontend::bytestring_parser::Parser;
use mork_expr::{item_byte, Tag};
use std::time::{Duration, Instant};
use pathmap::PathMap;
use pathmap::zipper::{Zipper, ZipperAbsolutePath, ZipperIteration, ZipperMoving};
use std::collections::{BTreeSet, HashSet};
use std::ffi::OsStr;
use std::ffi::OsString;
use std::hash::{Hash, Hasher};
use std::ops::Add;
// use std::future::Future;
// use std::task::Poll;
use itertools::Itertools;
use base64::Engine;
use serde::{Serialize, Deserialize};
use clap::{Args, Parser as CLAParser, Subcommand, ValueEnum};
use clap::builder::TypedValueParser;


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

fn set_from_newlines(input : &str) -> BTreeSet<&str> {
    BTreeSet::from_iter(input.split('\n').filter(|s| !s.is_empty()))
}

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

    s.add_sexpr(space.as_bytes(), expr!(s, "$"), expr!(s, "_1")).unwrap();

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

    s.add_sexpr(space_exprs.as_bytes(), expr!(s, "$"), expr!(s, "_1")).unwrap();

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

fn process_calculus_source_sink_bench(steps: usize, x: usize, y: usize) {
    let mut s = Space::new();

    // note 'idle' MM2-like statement that can be activated by moving it to the exec space
    let space_exprs = format!(r#"
(exec (IC 0 1 {})
               (, (exec (IC $x $y (S $c)) $sp $st)
                  ((exec $x) $p $t))
               (, (exec (IC $y $x $c) $sp $st)
                  (exec (R $x) $p $t)))

((exec 0)
      (I (== (petri (? $channel $payload $body)) $recv)
         (== (petri (! $channel $payload)) $send) )
      (O (+ (petri $body)) (- $recv) (- $send) ))
((exec 1)
      (I (== (petri (| $lprocess $rprocess)) $par) )
      (O (+ (petri $lprocess))
         (+ (petri $rprocess))
         (- $par)
         ))

(petri (? (add $ret) ((S $x) $y) (| (! (add (PN $x $y)) ($x $y))
                                    (? (PN $x $y) $z (! $ret (S $z)))  )  ))
(petri (? (add $ret) (Z $y) (! $ret $y)))
(petri (! (add result) ({} {})))
    "#, peano(steps), peano(x), peano(y));

    s.add_sexpr(space_exprs.as_bytes(), expr!(s, "$"), expr!(s, "_1")).unwrap();

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

    s.add_sexpr(SPACE_EXPRS.as_bytes(), expr!(s, "$"), expr!(s, "_1")).unwrap();

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

    s.add_all_sexpr(SPACE_EXPRS.as_bytes()).unwrap();

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

    s.add_all_sexpr(SPACE_EXPRS.as_bytes()).unwrap();

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

    s.add_all_sexpr(SPACE_EXPRS.as_bytes()).unwrap();

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

    s.add_sexpr(SPACE_EXPRS.as_bytes(), expr!(s, "$"), expr!(s, "_1")).unwrap();

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

    s.add_sexpr(SPACE_EXPRS.as_bytes(), expr!(s, "$"), expr!(s, "_1")).unwrap();

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

    s.add_sexpr(SPACE_EXPRS.as_bytes(), expr!(s, "$"), expr!(s, "_1")).unwrap();

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

    s.add_sexpr(SPACE_EXPRS.as_bytes(), expr!(s, "$"), expr!(s, "_1")).unwrap();

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

    s.add_all_sexpr(SPACE_EXPRS.as_bytes()).unwrap();

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

    s.add_all_sexpr(SPACE_EXPRS.as_bytes()).unwrap();

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

    s.add_all_sexpr(SPACE_EXPRS.as_bytes()).unwrap();

    let mut t0 = Instant::now();
    let steps = s.metta_calculus(1000000000000000);
    println!("elapsed {} steps {} size {}", t0.elapsed().as_millis(), steps, s.btm.val_count());

    let mut v = vec![];
    s.dump_all_sexpr(&mut v).unwrap();
    let res = String::from_utf8(v).unwrap();

    println!("result: {res}");
    assert!(res.contains("(MATCHED (foo bar) (foo bar))\n"));
}

fn roman_disjoin_initial() {
    let mut s = Space::new();

    const SPACE_EXPRS: &str = r#"
(set 1 a) (set 1 b) (set 1 c)
(set 2 d) (set 2 e) (set 2 f)
(set 3 a) (set 3 b)

(neq 1 2) (neq 1 3) (neq 2 3)

(neq Nil a) (neq a Nil)
(neq Nil b) (neq b Nil)
(neq Nil c) (neq c Nil)
(neq Nil d) (neq d Nil)
(neq Nil e) (neq e Nil)
(neq Nil f) (neq f Nil)

(mcmp $e $e $e)
(mcmp $e $f Nil)

(exec 0
    (, (set $a $ae) (set $b $be) (neq $a $b) (mcmp $ae $be $e))
    (, (intersection $a $b $e) ) )

(exec 2
    (, (intersection $a $b Nil) (neq Nil $e2) (intersection $a $b $e2)  )
    (O (- (intersection $a $b Nil) ) ) )
    "#;

    s.add_all_sexpr(SPACE_EXPRS.as_bytes()).unwrap();

    let mut t0 = Instant::now();
    let steps = s.metta_calculus(1000000000000000);
    println!("elapsed {} steps {} size {}", t0.elapsed().as_millis(), steps, s.btm.val_count());

    let mut v = vec![];
    // s.dump_all_sexpr(&mut v).unwrap();
    s.dump_sexpr(expr!(s, "[4] intersection $ $ $"), expr!(s, "[4] intersection _1 _2 _3"), &mut v);
    let res = String::from_utf8(v).unwrap();

    println!("result: {res}");
    assert!(res.contains("(intersection 1 2 Nil)
(intersection 1 3 a)
(intersection 1 3 b)
(intersection 2 3 Nil)
"));
}


fn roman_disjoin_final() {
    let mut s = Space::new();

    const SPACE_EXPRS: &str = r#"
(set 1 a) (set 1 b) (set 1 c)
(set 2 d) (set 2 e) (set 2 f)
(set 3 a) (set 3 b)

(lt 1 2) (lt 1 3) (lt 2 3)

(exec 0 (, (set $a $ea))
        (, (elementOf $ea $a)))

(exec 0 (, (set $a $ea))
        (, (sets $a)))

(exec 0 (, (lt $a $b))
        (, (disjoint $a $b)))

(exec 0 (, (elementOf $ea $a) (elementOf $ea $b) )
        (O (- (disjoint $a $b))))
    "#;

    s.add_all_sexpr(SPACE_EXPRS.as_bytes()).unwrap();

    let mut t0 = Instant::now();
    let steps = s.metta_calculus(1000000000000000);
    println!("elapsed {} steps {} size {}", t0.elapsed().as_millis(), steps, s.btm.val_count());

    let mut v = vec![];
    // s.dump_all_sexpr(&mut v).unwrap();
    s.dump_sexpr(expr!(s, "[3] disjoint $ $"), expr!(s, "[3] disjoint _1 _2"), &mut v);
    let res = String::from_utf8(v).unwrap();

    println!("result: {res}");
    assert!(res.contains("(disjoint 1 2)
(disjoint 2 3)
"));
}

fn func_type_unification() {
    let mut s = Space::new();

    const SPACE_EXPRS: &str = r#"
(a (: $a A))
(b (: f (-> A)))
(exec 0 (, (a (: ($f) A))
           (b (: $f (-> A))) ) (, (c OK)))
    "#;

    s.add_all_sexpr(SPACE_EXPRS.as_bytes()).unwrap();

    let mut t0 = Instant::now();
    let steps = s.metta_calculus(1000000000000000);
    println!("elapsed {} steps {} size {}", t0.elapsed().as_millis(), steps, s.btm.val_count());

    let mut v = vec![];
    s.dump_all_sexpr(&mut v).unwrap();
    let res = String::from_utf8(v).unwrap();

    println!("result: {res}");
    assert!(res.contains("(c OK)\n"));
}

fn top_level_match() {
    let mut s = Space::new();

    const SPACE_EXPRS: &str = r#"
($f)
f
(exec 0 (, ($f) $f) (, OK))
    "#;

    s.add_all_sexpr(SPACE_EXPRS.as_bytes()).unwrap();

    s.btm.iter().for_each(|(p, k)| println!("{p:?}"));

    let mut t0 = Instant::now();
    let steps = s.metta_calculus(1000000000000000);
    println!("elapsed {} steps {} size {}", t0.elapsed().as_millis(), steps, s.btm.val_count());

    let mut v = vec![];
    s.dump_all_sexpr(&mut v).unwrap();
    let res = String::from_utf8(v).unwrap();

    println!("result: {res}");
    assert!(res.contains("OK\n"));
}

fn bench_lr() {
    let mut s = Space::new();

    let GRAMMAR = r#"
    (S → E eof)
    (E → E * B)
    (E → E + B)
    (E → B)
    (B → 0)
    (B → 1)
    "#;

    let PARSER_GENERATOR = r#"
    (move () ($x) ($x) ())
    (move () ($x $y) ($x) ($y)) (move ($x) ($y) ($x $y) ())
    (move () ($x $y $z) ($x) ($y $z)) (move ($x) ($y $z) ($x $y) ($z)) (move ($x $y) ($z) ($x $y $z) ())

    (exec (0 0) (, (grammar ($x → $y)) ) (, (expr $x) (symbol $y) (line Z $x () ($y)) ))
    (exec (0 1) (, (grammar ($x → $y $z)) ) (, (expr $x) (symbol $y) (symbol $z) (line Z $x () ($y $z)) ))
    (exec (0 2) (, (grammar ($x → $y $z $w)) ) (, (expr $x) (symbol $y) (symbol $z) (symbol $w) (line Z $x () ($y $z $w)) ))
    (exec (0 3) (, (expr $x) ) (O (- (symbol $x)) ))
    "#;

    let PARSER = r#"
(0 0 1) (0 1 2) (0 E 3) (0 B 4)
(1 * 4) (1 + 4) (1 0 4) (1 1 4) (1 $ 4)
(2 * 5) (2 + 5) (2 0 5) (2 1 5) (2 $ 5)
(3 * 5) (3 * 6) (3 $ acc)
(4 * 3) (4 + 3) (4 0 3) (4 1 3) (4 $ 3)
(5 0 1) (5 1 2) (5 B 7)
(6 0 1) (6 1 2) (6 B 8)
(7 * 1) (7 + 1) (7 0 1) (7 1 1) (7 $ 1)
(8 * 2) (8 + 2) (8 0 2) (8 1 2) (8 $ 2)
    "#;

    let PARSING = r#"
    (exec 0
    (, (state $s $k) (input $k $c) (parser ($s $c $s')) )
    (, (out $s'))
    )

    (state 0 0)
    "#;

    let INPUT = r#"
    (input 0 1)
    (input 1 +)
    (input 2 1)
    (input 3 $)
    "#;

    // s.load_sexpr(GRAMMAR.as_bytes(), expr!(s, "$"), expr!(s, "[2] grammar _1")).unwrap();
    s.add_sexpr(PARSER.as_bytes(), expr!(s, "$"), expr!(s, "[2] parser _1")).unwrap();
    // s.load_all_sexpr(PARSER.as_bytes()).unwrap();
    s.add_all_sexpr(PARSING.as_bytes()).unwrap();

    let mut t0 = Instant::now();
    let steps = s.metta_calculus(1000000000000000);
    println!("elapsed {} steps {} size {}", t0.elapsed().as_millis(), steps, s.btm.val_count());

    let mut v = vec![];
    s.dump_all_sexpr(&mut v).unwrap();
    // s.dump_sexpr(expr!(s, "[3] state $ [3] REG 3 $"), expr!(s, "[2] _1 _2"), &mut v);
    let res = String::from_utf8(v).unwrap();

    println!("{res}");
}

fn pattern_mining() {
    let mut s = Space::new();

    const SPACE_EXPRS: &str = r#"
(destruct () 0 [0])

(destruct ($x) 0 [1])
(destruct ($x) 1 $x)

(destruct ($x $y) 0 [2])
(destruct ($x $y) 1 $x)
(destruct ($x $y) 2 $y)

(destruct ($x $y $z) 0 [3])
(destruct ($x $y $z) 1 $x)
(destruct ($x $y $z) 2 $y)
(destruct ($x $y $z) 3 $z)

(test (foo 1))

(exec 0 (arg $x
    "#;

    s.add_all_sexpr(SPACE_EXPRS.as_bytes()).unwrap();

    s.btm.iter().for_each(|(p, k)| println!("{p:?}"));

    let mut t0 = Instant::now();
    let steps = s.metta_calculus(1000000000000000);
    println!("elapsed {} steps {} size {}", t0.elapsed().as_millis(), steps, s.btm.val_count());

    let mut v = vec![];
    s.dump_all_sexpr(&mut v).unwrap();
    let res = String::from_utf8(v).unwrap();

    println!("result: {res}");
    assert!(res.contains("OK\n"));
}

fn meta_ana() {
    let mut s = Space::new();

    let input = "(branch (branch (leaf 11) (leaf 12)) (leaf 2))";
    let desired_output = "(value (cons nil R) 2)\n(value (cons (cons nil L) L) 11)\n(value (cons (cons nil L) R) 12)\n";

    let SPACE = r#"
; (coalg $pattern $templates)
; initial step: lift seed into folding context
(tree-to-space lift-tree (coalg (tree $tree) (, (ctx $tree nil) )))
; bulk steps: explode expression in context into two expressions in context (location in the trie)
(tree-to-space explode-tree (coalg (ctx (branch $left $right) $path) (, (ctx $left  (cons $path L))
                                                                        (ctx $right (cons $path R)) )))
; final steps: drop the resulting expressions in context into output results
(tree-to-space drop-tree (coalg (ctx (leaf $value) $path) (, (value $path $value) )))

; prepare the seed in the space
(exec (0 0) (, (tree-example $e)) (, (tmp (tree $e))))

; host the coalgebra in a fixed point rewriting system
(has changed)
(rulify $name (, $p0) (, $t0 ) (, (tmp $p0)) (O (- (tmp $p0)) (+ (tmp $t0)) (+ (has changed)) ))
(rulify $name (, $p0) (, $t0 $t1 ) (, (tmp $p0)) (O (- (tmp $p0)) (+ (tmp $t0)) (+ (tmp $t1)) (+ (has changed)) ))
(exec (1 system) (, (tree-to-space $name (coalg $p $ts)) (rulify $name (, $p) $ts $ruleps $rulets) (has changed) (exec (1 system) $sps $sts) )
                 (O (+ (exec (0 $name) $ruleps $rulets)) (- (has changed)) (+ (exec (1 system) $sps $sts)) ))

; extract the result from the space
(exec (2 0) (, (tmp $value)) (O (+ (space-example $value)) (- (tmp $value)) ))
    "#;

    s.add_sexpr(input.as_bytes(), expr!(s, "$"), expr!(s, "[2] tree-example _1")).unwrap();
    s.add_all_sexpr(SPACE.as_bytes()).unwrap();

    let mut t0 = Instant::now();
    let steps = s.metta_calculus(1000000000000000);
    println!("elapsed {} steps {} size {}", t0.elapsed().as_millis(), steps, s.btm.val_count());

    let mut v = vec![];
    // s.dump_all_sexpr(&mut v).unwrap();
    s.dump_sexpr(expr!(s, "[2] space-example $"), expr!(s, "_1"), &mut v);
    let res = String::from_utf8(v).unwrap();

    println!("{res}");
    assert_eq!(res, desired_output);
}

fn meta_ana_exec() {
    let mut s = Space::new();

    let input = "(branch (branch (branch (leaf 111) (leaf 112)) (leaf 12)) (branch (leaf 21) (leaf 22)))";
    let desired_output = r#"(value (cons (cons nil L) R) 12)
(value (cons (cons nil R) L) 21)
(value (cons (cons nil R) R) 22)
(value (cons (cons (cons nil L) L) L) 111)
(value (cons (cons (cons nil L) L) R) 112)
"#;

    let space = r#"
    T

    (tree-to-space (ctx (branch $left $right) $path) (ctx $left  (cons $path L)))
    (tree-to-space (ctx (branch $left $right) $path) (ctx $right (cons $path R)))

    (ana (tree-example $tree) (ctx $tree nil) $p (tree-to-space $p $t) $t (ctx (leaf $value) $path) (space-example (value $path $value)))

    (exec 0
      (,
        (ana $cx $x $p $cpt $t $y $cy)
        $cx
        $cpt
      )
      (,
        (exec 0
          (, (lookup $x $px $tx) )
          (, (exec (0 $x) $px $tx) )
        )

        (lookup $p
          (, (lookup $t $px $tx) )
          (, (exec (0 $t) $px $tx ) )
        )

        (lookup $y
          (, T)
          (, $cy )
        )
      )
    )
    "#;

    s.add_sexpr(input.as_bytes(), expr!(s, "$"), expr!(s, "[2] tree-example _1")).unwrap();
    s.add_all_sexpr(space.as_bytes()).unwrap();
    let mut t0 = Instant::now();
    let steps = s.metta_calculus(1000000000000000);
    println!("elapsed {} steps {} size {}", t0.elapsed().as_millis(), steps, s.btm.val_count());

    let mut v = vec![];
    // s.dump_all_sexpr(&mut v).unwrap();
    s.dump_sexpr(expr!(s, "[2] space-example $"), expr!(s, "_1"), &mut v);
    let res = String::from_utf8(v).unwrap();

    println!("{res}");
    assert_eq!(res, desired_output);
}

fn bench_tile_puzzle_states() {
    let mut s = Space::new();

    let space = r#"
(move (___ $_2 $_3
       $_4 $_5 $_6
       $_7 $_8 $_9) R ($_2 ___ $_3
                       $_4 $_5 $_6
                       $_7 $_8 $_9))
(move (___ $_2 $_3
       $_4 $_5 $_6
       $_7 $_8 $_9) D ($_4 $_2 $_3
                       ___ $_5 $_6
                       $_7 $_8 $_9))
(move ($_1 ___ $_3
       $_4 $_5 $_6
       $_7 $_8 $_9) L (___ $_1 $_3
                       $_4 $_5 $_6
                       $_7 $_8 $_9))
(move ($_1 ___ $_3
       $_4 $_5 $_6
       $_7 $_8 $_9) R ($_1 $_3 ___
                       $_4 $_5 $_6
                       $_7 $_8 $_9))
(move ($_1 ___ $_3
       $_4 $_5 $_6
       $_7 $_8 $_9) D ($_1 $_5 $_3
                       $_4 ___ $_6
                       $_7 $_8 $_9))
(move ($_1 $_2 ___
       $_4 $_5 $_6
       $_7 $_8 $_9) L ($_1 ___ $_2
                       $_4 $_5 $_6
                       $_7 $_8 $_9))
(move ($_1 $_2 ___
       $_4 $_5 $_6
       $_7 $_8 $_9) D ($_1 $_2 $_6
                       $_4 $_5 ___
                       $_7 $_8 $_9))
(move ($_1 $_2 $_3
       ___ $_5 $_6
       $_7 $_8 $_9) U (___ $_2 $_3
                       $_1 $_5 $_6
                       $_7 $_8 $_9))
(move ($_1 $_2 $_3
       ___ $_5 $_6
       $_7 $_8 $_9) R ($_1 $_2 $_3
                       $_5 ___ $_6
                       $_7 $_8 $_9))
(move ($_1 $_2 $_3
       ___ $_5 $_6
       $_7 $_8 $_9) D ($_1 $_2 $_3
                       $_7 $_5 $_6
                       ___ $_8 $_9))
(move ($_1 $_2 $_3
       $_4 ___ $_6
       $_7 $_8 $_9) U ($_1 ___ $_3
                       $_4 $_2 $_6
                       $_7 $_8 $_9))
(move ($_1 $_2 $_3
       $_4 ___ $_6
       $_7 $_8 $_9) L ($_1 $_2 $_3
                       ___ $_4 $_6
                       $_7 $_8 $_9))
(move ($_1 $_2 $_3
       $_4 ___ $_6
       $_7 $_8 $_9) R ($_1 $_2 $_3
                       $_4 $_6 ___
                       $_7 $_8 $_9))
(move ($_1 $_2 $_3
       $_4 ___ $_6
       $_7 $_8 $_9) D ($_1 $_2 $_3
                       $_4 $_8 $_6
                       $_7 ___ $_9))
(move ($_1 $_2 $_3
       $_4 $_5 ___
       $_7 $_8 $_9) U ($_1 $_2 ___
                       $_4 $_5 $_3
                       $_7 $_8 $_9))
(move ($_1 $_2 $_3
       $_4 $_5 ___
       $_7 $_8 $_9) L ($_1 $_2 $_3
                       $_4 ___ $_5
                       $_7 $_8 $_9))
(move ($_1 $_2 $_3
       $_4 $_5 ___
       $_7 $_8 $_9) D ($_1 $_2 $_3
                       $_4 $_5 $_9
                       $_7 $_8 ___))
(move ($_1 $_2 $_3
       $_4 $_5 $_6
       ___ $_8 $_9) U ($_1 $_2 $_3
                       ___ $_5 $_6
                       $_4 $_8 $_9))
(move ($_1 $_2 $_3
       $_4 $_5 $_6
       ___ $_8 $_9) R ($_1 $_2 $_3
                       $_4 $_5 $_6
                       $_8 ___ $_9))
(move ($_1 $_2 $_3
       $_4 $_5 $_6
       $_7 ___ $_9) U ($_1 $_2 $_3
                       $_4 ___ $_6
                       $_7 $_5 $_9))
(move ($_1 $_2 $_3
       $_4 $_5 $_6
       $_7 ___ $_9) L ($_1 $_2 $_3
                       $_4 $_5 $_6
                       ___ $_7 $_9))
(move ($_1 $_2 $_3
       $_4 $_5 $_6
       $_7 ___ $_9) R ($_1 $_2 $_3
                       $_4 $_5 $_6
                       $_7 $_9 ___))
(move ($_1 $_2 $_3
       $_4 $_5 $_6
       $_7 $_8 ___) U ($_1 $_2 $_3
                       $_4 $_5 ___
                       $_7 $_8 $_6))
(move ($_1 $_2 $_3
       $_4 $_5 $_6
       $_7 $_8 ___) L ($_1 $_2 $_3
                       $_4 $_5 $_6
                       $_7 ___ $_8))

(1 != 2) (1 != 3) (1 != 4) (1 != 5) (1 != 6) (1 != 7) (1 != 8) (2 != 1) (2 != 3) (2 != 4) (2 != 5) (2 != 6) (2 != 7) (2 != 8) (3 != 1) (3 != 2) (3 != 4) (3 != 5) (3 != 6) (3 != 7) (3 != 8) (4 != 1) (4 != 2) (4 != 3) (4 != 5) (4 != 6) (4 != 7) (4 != 8) (5 != 1) (5 != 2) (5 != 3) (5 != 4) (5 != 6) (5 != 7) (5 != 8) (6 != 1) (6 != 2) (6 != 3) (6 != 4) (6 != 5) (6 != 7) (6 != 8) (7 != 1) (7 != 2) (7 != 3) (7 != 4) (7 != 5) (7 != 6) (7 != 8) (8 != 1) (8 != 2) (8 != 3) (8 != 4) (8 != 5) (8 != 6) (8 != 7)
(empty $_1 $_2 $_3 $_4 $_5 $_6 $_7 $_8 1 (___ $_1 $_2 $_3 $_4 $_5 $_6 $_7 $_8) )
(empty $_1 $_2 $_3 $_4 $_5 $_6 $_7 $_8 2 ($_1 ___ $_2 $_3 $_4 $_5 $_6 $_7 $_8) )
(empty $_1 $_2 $_3 $_4 $_5 $_6 $_7 $_8 3 ($_1 $_2 ___ $_3 $_4 $_5 $_6 $_7 $_8) )
(empty $_1 $_2 $_3 $_4 $_5 $_6 $_7 $_8 4 ($_1 $_2 $_3 ___ $_4 $_5 $_6 $_7 $_8) )
(empty $_1 $_2 $_3 $_4 $_5 $_6 $_7 $_8 5 ($_1 $_2 $_3 $_4 ___ $_5 $_6 $_7 $_8) )
(empty $_1 $_2 $_3 $_4 $_5 $_6 $_7 $_8 6 ($_1 $_2 $_3 $_4 $_5 ___ $_6 $_7 $_8) )
(empty $_1 $_2 $_3 $_4 $_5 $_6 $_7 $_8 7 ($_1 $_2 $_3 $_4 $_5 $_6 ___ $_7 $_8) )
(empty $_1 $_2 $_3 $_4 $_5 $_6 $_7 $_8 8 ($_1 $_2 $_3 $_4 $_5 $_6 $_7 ___ $_8) )
(empty $_1 $_2 $_3 $_4 $_5 $_6 $_7 $_8 9 ($_1 $_2 $_3 $_4 $_5 $_6 $_7 $_8 ___) )
(square 1) (square 2) (square 3) (square 4) (square 5) (square 6) (square 7) (square 8) (square 9)
    "#;

    s.add_all_sexpr(space.as_bytes()).unwrap();

    s.add_all_sexpr(r"
(exec 0
  (, ($_1 != $_2)
     ($_2 != $_3) ($_3 != $_1)
     ($_3 != $_4) ($_4 != $_2) ($_4 != $_1)
     ($_4 != $_5) ($_5 != $_3) ($_5 != $_2) ($_5 != $_1)
     ($_5 != $_6) ($_6 != $_4) ($_6 != $_3) ($_6 != $_2) ($_6 != $_1)
     ($_6 != $_7) ($_7 != $_5) ($_7 != $_4) ($_7 != $_3) ($_7 != $_2) ($_7 != $_1)
     ($_7 != $_8) ($_8 != $_6) ($_8 != $_5) ($_8 != $_4) ($_8 != $_3) ($_8 != $_2) ($_8 != $_1)
     (empty $_1 $_2 $_3 $_4 $_5 $_6 $_7 $_8 $x $state)
  )
  (, (state1 $state))
)
".as_bytes()).unwrap();
    let mut t0 = Instant::now();
    let steps = s.metta_calculus(1000000000000000);
    println!("elapsed {} steps {} size {}", t0.elapsed().as_millis(), steps, s.btm.val_count());


    s.add_all_sexpr(r"
((step 0) (, (new $state) (move $state $a $new_state) )
          (O (+ (new_reachable $new_state)) (+ (state2 $state)) (- (new $state)) (- (some todo)) ))

((step 1) (, (new_reachable $state) (state2 $state) )
          (O (- (new_reachable $state)) ))

((step 2) (, (new_reachable $state) )
          (O (+ (new $state)) (+ (some todo)) ))

(new (___ 1  2
       3  4  5
       6  7  8 ))
(some todo)
(exec fixpoint
        (, (some todo) ((step $x) $p0 $t0)
           (exec fixpoint $p1 $t1) )
        (, (exec $x $p0 $t0)
           (exec fixpoint $p1 $t1) ))
".as_bytes()).unwrap();
    let mut t0 = Instant::now();
    let steps = s.metta_calculus(1000000000000000);
    println!("elapsed {} steps {} size {}", t0.elapsed().as_millis(), steps, s.btm.val_count());

    let mut v1 = vec![];
    // s.dump_all_sexpr(&mut v).unwrap();
    s.dump_sexpr(expr!(s, "[2] state1 $"), expr!(s, "_1"), &mut v1);
    let res1 = String::from_utf8(v1).unwrap();

    let mut v2 = vec![];
    // s.dump_all_sexpr(&mut v2).unwrap();
    s.dump_sexpr(expr!(s, "[2] state2 $"), expr!(s, "_1"), &mut v2);
    let res2 = String::from_utf8(v2).unwrap();

    println!("State enumeration {}", res1.as_bytes().into_iter().filter(|c| **c == b'\n').count());
    println!("State exploration {}", res2.as_bytes().into_iter().filter(|c| **c == b'\n').count());
    // println!("{res2}");
    // assert_eq!(res1, res2);
}

fn source_space_two_bipolar_equal_crossed() {
    let mut s = Space::new();

    const SPACE_EXPRS: &str = r#"
(exec 0 (I (BTM (Something $x $y)) (BTM (Else $x $y))) (, (MATCHED $x $y) ))

(Something (foo $x) (foo $x))
(Else ($x bar) ($x bar))
    "#;

    s.add_all_sexpr(SPACE_EXPRS.as_bytes()).unwrap();

    let mut t0 = Instant::now();
    let steps = s.metta_calculus(1000000000000000);
    println!("elapsed {} steps {} size {}", t0.elapsed().as_millis(), steps, s.btm.val_count());

    let mut v = vec![];
    s.dump_all_sexpr(&mut v).unwrap();
    let res = String::from_utf8(v).unwrap();

    println!("result: {res}");
    assert!(res.contains("(MATCHED (foo bar) (foo bar))\n"));
}

fn source_act_two_bipolar_equal_crossed() {
    {
        let mut act_s = Space::new();

        const SPACE_EXPRS: &str = r#"
(Something (foo $x) (foo $x))
(Else ($x bar) ($x bar))
    "#;

        act_s.add_all_sexpr(SPACE_EXPRS.as_bytes()).unwrap();
        act_s.backup_tree(format!("{ACT_PATH}two_bipolar_equal_crossed.act")).unwrap();
    };

    let mut s = Space::new();

    const SPACE_EXPRS: &str = r#"
(exec 0 (I (ACT two_bipolar_equal_crossed (Something $x $y)) (ACT two_bipolar_equal_crossed (Else $x $y))) (, (MATCHED $x $y) ))
    "#;

    s.add_all_sexpr(SPACE_EXPRS.as_bytes()).unwrap();

    let mut t0 = Instant::now();
    let steps = s.metta_calculus(1000000000000000);
    println!("elapsed {} steps {} size {}", t0.elapsed().as_millis(), steps, s.btm.val_count());

    let mut v = vec![];
    s.dump_all_sexpr(&mut v).unwrap();
    let res = String::from_utf8(v).unwrap();

    println!("result: {res}");
    assert!(res.contains("(MATCHED (foo bar) (foo bar))\n"));
}

fn source_space_act_two_bipolar_equal_crossed() {
    {
        let mut act_s = Space::new();

        const SPACE_EXPRS: &str = r#"
(Else ($x bar) ($x bar))
    "#;

        act_s.add_all_sexpr(SPACE_EXPRS.as_bytes()).unwrap();
        act_s.backup_tree(format!("{ACT_PATH}space_two_bipolar_equal_crossed.act")).unwrap();
    };

    let mut s = Space::new();

    const SPACE_EXPRS: &str = r#"
(exec 0 (I (BTM (Something $x $y)) (ACT space_two_bipolar_equal_crossed (Else $x $y))) (, (MATCHED $x $y) ))
(Something (foo $x) (foo $x))
    "#;

    s.add_all_sexpr(SPACE_EXPRS.as_bytes()).unwrap();

    let mut t0 = Instant::now();
    let steps = s.metta_calculus(1000000000000000);
    println!("elapsed {} steps {} size {}", t0.elapsed().as_millis(), steps, s.btm.val_count());

    let mut v = vec![];
    s.dump_all_sexpr(&mut v).unwrap();
    let res = String::from_utf8(v).unwrap();

    println!("result: {res}");
    assert!(res.contains("(MATCHED (foo bar) (foo bar))\n"));
}

fn source_cmp_eq() {
    let mut s = Space::new();

    const SPACE_EXPRS: &str = r#"
(LHS (foo $y))
(RHS ($x bar))
(exec 0 (I (BTM (LHS $x)) (== (RHS $x) $o) ) (, (REM $o) ))
    "#;

    s.add_all_sexpr(SPACE_EXPRS.as_bytes()).unwrap();

    let mut t0 = Instant::now();
    let steps = s.metta_calculus(1000000000000000);
    println!("elapsed {} steps {} size {}", t0.elapsed().as_millis(), steps, s.btm.val_count());

    let mut v = vec![];
    s.dump_all_sexpr(&mut v).unwrap();
    let res = String::from_utf8(v).unwrap();

    println!("result: {res}");
    assert!(res.contains("(REM (RHS ($a bar)))\n"));
}

fn source_cmp_ne() {
    let mut s = Space::new();

    const SPACE_EXPRS: &str = r#"
(VAL X) (VAL Y) (VAL Z)
(exec 0 (I (!= (VAL $x) (VAL $y) ) ) (, (OUT ($x != $y)) ))
    "#;

    s.add_all_sexpr(SPACE_EXPRS.as_bytes()).unwrap();

    let mut t0 = Instant::now();
    let steps = s.metta_calculus(1000000000000000);
    println!("elapsed {} steps {} size {}", t0.elapsed().as_millis(), steps, s.btm.val_count());

    let mut v = vec![];
    // s.dump_all_sexpr(&mut v).unwrap();
    s.dump_sexpr(expr!(s, "[2] OUT $"), expr!(s, "_1"), &mut v);
    let res = String::from_utf8(v).unwrap();

    println!("result: {res}");
    assert!(res.contains("(X != Y)
(X != Z)
(Y != X)
(Y != Z)
(Z != X)
(Z != Y)
"));
}

fn sink_two_bipolar_equal_crossed() {
    let mut s = Space::new();

    const SPACE_EXPRS: &str = r#"
(exec 0 (, (Something $x $y) (Else $x $y)) (O (+ (MATCHED $x $y))))

(Something (foo $x) (foo $x))
(Else ($x bar) ($x bar))
    "#;

    s.add_all_sexpr(SPACE_EXPRS.as_bytes()).unwrap();

    let mut t0 = Instant::now();
    let steps = s.metta_calculus(1000000000000000);
    println!("elapsed {} steps {} size {}", t0.elapsed().as_millis(), steps, s.btm.val_count());

    let mut v = vec![];
    s.dump_all_sexpr(&mut v).unwrap();
    let res = String::from_utf8(v).unwrap();

    println!("result: {res}");
    assert!(res.contains("(MATCHED (foo bar) (foo bar))\n"));
}

fn sink_two_positive_equal_crossed() {
    let mut s = Space::new();

    const SPACE_EXPRS: &str = r#"
(exec 0 (, (Something $x $y) (Else $x $y)) (O (+ MATCHED) (- (Something $x $y))))

(Something (foo bar) (bar baz))
(Else (foo bar) (bar baz))
    "#;

    s.add_all_sexpr(SPACE_EXPRS.as_bytes()).unwrap();

    let mut t0 = Instant::now();
    let steps = s.metta_calculus(1000000000000000);
    println!("elapsed {} steps {} size {}", t0.elapsed().as_millis(), steps, s.btm.val_count());

    let mut v = vec![];
    s.dump_all_sexpr(&mut v).unwrap();
    let res = String::from_utf8(v).unwrap();

    println!("result: {res}");
    assert!(res.contains("MATCHED\n"));
    assert!(!res.contains("(Something (foo bar) (bar baz))\n"));
}

fn sink_add_remove() {
    let mut s = Space::new();

    const SPACE_EXPRS: &str = r#"
A
(exec a (, A) (O (- A) (+ B)))
    "#;

    s.add_all_sexpr(SPACE_EXPRS.as_bytes()).unwrap();

    let mut t0 = Instant::now();
    let steps = s.metta_calculus(1000000000000000);
    println!("elapsed {} steps {} size {}", t0.elapsed().as_millis(), steps, s.btm.val_count());

    let mut v = vec![];
    s.dump_all_sexpr(&mut v).unwrap();
    let res = String::from_utf8(v).unwrap();

    println!("result: {res}");
    assert!(!res.contains("A\n"));
    assert!(res.contains("B\n"));
}

fn sink_remove_many() {
    let mut s = Space::new();

    // language="common lisp"
    const SPACE_EXPRS: &str = r#"
(row 1 2 3)
(col 3 4 5)
(remove (tuple-concat $x $y $z))
(remove (col $x $y $z))
(remove (column-index $x))
(remove (exec $x $y $z $w))
(exec 0 (, (remove $x) $x) (O (- $x)))
    "#;

    s.add_all_sexpr(SPACE_EXPRS.as_bytes()).unwrap();

    let mut t0 = Instant::now();
    let steps = s.metta_calculus(1000000000000000);
    println!("elapsed {} steps {} size {}", t0.elapsed().as_millis(), steps, s.btm.val_count());

    let mut v = vec![];
    s.dump_all_sexpr(&mut v).unwrap();
    let res = String::from_utf8(v).unwrap();

    println!("result: {res}");
}

fn cross_join_tuple() {
    let mut s = Space::new();

    // language="common lisp"
    const SPACE_EXPRS: &str = r#"
(concat (, $x $y $z) (, $a $b) (, $x $y $z $a $b))

(WIKI (, Name EmpId DeptName) (, Harry 3415 Finance))
(WIKI (, Name EmpId DeptName) (, Cheat 3489 Marketing))

(OTHER (, X Y) (, 1 2))
(OTHER (, X Y) (, 10 20))

(exec 0
    (, (WIKI $h0 $v0) (OTHER $h1 $v1) (concat $h0 $h1 $h) (concat $v0 $v1 $v) )
    (, (CROSSJOIN $h $v) )
)
    "#;

    s.add_all_sexpr(SPACE_EXPRS.as_bytes()).unwrap();

    let mut t0 = Instant::now();
    let steps = s.metta_calculus(1000000000000000);
    println!("elapsed {} steps {} size {}", t0.elapsed().as_millis(), steps, s.btm.val_count());

    let mut v = vec![];
    // s.dump_all_sexpr(&mut v).unwrap();
    s.dump_sexpr(expr!(s, "[3] CROSSJOIN $ $"), expr!(s, "_2"), &mut v);
    let res = String::from_utf8(v).unwrap();

    println!("result: {res}");
    assert_eq!(res, r#"(, Cheat 3489 Marketing 1 2)
(, Cheat 3489 Marketing 10 20)
(, Harry 3415 Finance 1 2)
(, Harry 3415 Finance 10 20)
"#)
}


fn cross_join_dict() {
    let mut s = Space::new();

    // language="common lisp"
    const SPACE_EXPRS: &str = r#"

(WIKI header (Name EmpId DeptName))
(WIKI data 0 Name Harry)
(WIKI data 0 EmpId 3415)
(WIKI data 0 DeptName Finance)
(WIKI data 1 Name Chear)
(WIKI data 1 EmpId 3489)
(WIKI data 1 DeptName Marketing)

(OTHER header (X Y))
(OTHER data 0 X 1)
(OTHER data 0 Y 2)
(OTHER data 1 X 10)
(OTHER data 1 Y 20)

(exec 0
    (, (WIKI data $i0 $f0 $v0) (OTHER data $i1 $f1 $v1) )
    (, (CROSSJOIN data ($i0 $i1) $f0 $v0) (CROSSJOIN data ($i0 $i1) $f1 $v1) )
)
    "#;

    s.add_all_sexpr(SPACE_EXPRS.as_bytes()).unwrap();

    let mut t0 = Instant::now();
    let steps = s.metta_calculus(1000000000000000);
    println!("elapsed {} steps {} size {}", t0.elapsed().as_millis(), steps, s.btm.val_count());

    let mut v = vec![];
    s.dump_all_sexpr(&mut v).unwrap();
    // s.dump_sexpr(expr!(s, "[3] CROSSJOIN $ $"), expr!(s, "_2"), &mut v);
    let res = String::from_utf8(v).unwrap();

    println!("result: {res}");
//     assert_eq!(res, r#"(, Cheat 3489 Marketing 1 2)
// (, Cheat 3489 Marketing 10 20)
// (, Harry 3415 Finance 1 2)
// (, Harry 3415 Finance 10 20)
// "#)
}


fn sink_add_remove_var() {
    let mut s = Space::new();

    const SPACE_EXPRS: &str = r#"#
(foo a)
(exec 0
  (, (foo $x))
  (O (- (foo $x))
     (+ (bar $x))))
    "#;

    s.add_all_sexpr(SPACE_EXPRS.as_bytes()).unwrap();

    let mut t0 = Instant::now();
    let steps = s.metta_calculus(1000000000000000);
    println!("elapsed {} steps {} size {}", t0.elapsed().as_millis(), steps, s.btm.val_count());

    let mut v = vec![];
    s.dump_all_sexpr(&mut v).unwrap();
    let res = String::from_utf8(v).unwrap();

    println!("result: {res}");
    assert!(!res.contains("(foo a)\n"));
    assert!(res.contains("(bar a)\n"));
}

fn sink_odd_even_sort() {
    let mut s = Space::new();
    const SPACE_EXPRS: &str = r#"
(lt A B) (lt A C) (lt A D) (lt A E) (lt B C) (lt B D) (lt B E) (lt C D) (lt C E) (lt D E)
(succ 0 1) (succ 1 2) (succ 2 3) (succ 3 4) (succ 4 5)
(parity 0 even) (parity 1 odd) (parity 2 even) (parity 3 odd) (parity 4 even)

(A 0 B)
(A 1 A)
(A 2 E)
(A 3 C)
(A 4 D)

((phase $p)  (, (parity $i $p) (succ $i $si) (A $i $e) (A $si $se) (lt $se $e))
             (O (- (A $i $e)) (- (A $si $se)) (+ (A $i $se)) (+ (A $si $e))))
(phase 0 odd) (phase 1 even)
(exec repeat (, (A $k $_) (phase $kp $phase) ((phase $phase) $p0 $t0))
             (, (exec ($k $kp) $p0 $t0)))
    "#;

    // let mut SUCCS: String = (0..5).map(|x| format!("(succ {x} {})\n", x+1)).collect();
    // s.add_all_sexpr(SUCCS.as_bytes()).unwrap();
    // let mut PARITY: String = (0..5).map(|x| format!("(parity {x} {})\n", if x % 2 == 0 { "even" } else { "odd" })).collect();
    // s.add_all_sexpr(PARITY.as_bytes()).unwrap();
    // let mut ORDER: String = (b'A'..=b'E').flat_map(|x| (b'A'..x).map(move |y| format!("(lt {} {})\n", y as char, x as char))).collect();
    // s.add_all_sexpr(ORDER.as_bytes()).unwrap();

    s.add_all_sexpr(SPACE_EXPRS.as_bytes()).unwrap();

    let mut t0 = Instant::now();
    let steps = s.metta_calculus(1000000000000000);
    println!("elapsed {} steps {} size {}", t0.elapsed().as_millis(), steps, s.btm.val_count());

    let mut v = vec![];
    // s.dump_all_sexpr(&mut v).unwrap();
    s.dump_sexpr(expr!(s, "[3] A $ $"), expr!(s, "_2"), &mut v);
    let res = String::from_utf8(v).unwrap();

    println!("result:\n{res}");
    assert_eq!(res, "A\nB\nC\nD\nE\n");
}

fn sink_head() {
    let mut s = Space::new();

    const SPACE_EXPRS: &str = r#"
(foo 1) (foo 2) (foo 3)
(bar x) (bar y)
(baz P) (baz Q) (baz R)
(exec 0 (, (foo $x) (bar $y) (baz $z)) (O (head 7 (cux $z $y $x))))
    "#;

    s.add_all_sexpr(SPACE_EXPRS.as_bytes()).unwrap();

    let mut t0 = Instant::now();
    let steps = s.metta_calculus(1000000000000000);
    println!("elapsed {} steps {} size {}", t0.elapsed().as_millis(), steps, s.btm.val_count());

    let mut v = vec![];
    s.dump_sexpr(expr!(s, "[4] cux $ $ $"), expr!(s, "[3] _3 _2 _1"), &mut v);
    // s.dump_all_sexpr(&mut v).unwrap();
    let res = String::from_utf8(v).unwrap();

    println!("result: {res}");
    assert_eq!(res, "(1 x P)\n(2 x P)\n(3 x P)\n(1 y P)\n(2 y P)\n(3 y P)\n(1 x Q)\n")
}

fn sink_count_literal() {
    let mut s = Space::new();

    const SPACE_EXPRS: &str = r#"
(foo 1) (foo 2) (foo 3)
(bar x) (bar y)
(baz P) (baz Q) (baz R)
(exec 0 (, (foo $x) (bar $y) (baz $z)) (O (count (all eighteen) 18 (cux $z $y $x))))
(exec 0 (, (foo $x) (bar $y) (baz $z)) (O (count (all sixteen) 16 (cux $z $y $x))))
    "#;

    s.add_all_sexpr(SPACE_EXPRS.as_bytes()).unwrap();

    let mut t0 = Instant::now();
    let steps = s.metta_calculus(1000000000000000);
    println!("elapsed {} steps {} size {}", t0.elapsed().as_millis(), steps, s.btm.val_count());

    let mut v = vec![];
    s.dump_sexpr(expr!(s, "[2] all $"), expr!(s, "_1"), &mut v);
    // s.dump_all_sexpr(&mut v).unwrap();
    let res = String::from_utf8(v).unwrap();

    println!("result: {res}");
    assert_eq!(res, "eighteen\n")
}

fn sink_count_constant() {
    let mut s = Space::new();

    const SPACE_EXPRS: &str = r#"
(foo 1) (foo 2) (foo 3)
(bar x) (bar y)
(baz P) (baz Q) (baz R)
(exec 0 (, (foo $x) (bar $y) (baz $z)) (O (count (all stupid) $k (cux $z $y $x))))
    "#;

    s.add_all_sexpr(SPACE_EXPRS.as_bytes()).unwrap();

    let mut t0 = Instant::now();
    let steps = s.metta_calculus(1000000000000000);
    println!("elapsed {} steps {} size {}", t0.elapsed().as_millis(), steps, s.btm.val_count());

    let mut v = vec![];
    s.dump_sexpr(expr!(s, "[2] all $"), expr!(s, "_1"), &mut v);
    // s.dump_all_sexpr(&mut v).unwrap();
    let res = String::from_utf8(v).unwrap();

    println!("result: {res}");
    assert_eq!(res, "stupid\n")
}

fn sink_count() {
    let mut s = Space::new();

    const SPACE_EXPRS: &str = r#"
(foo 1) (foo 2) (foo 3)
(bar x) (bar y)
(baz P) (baz Q) (baz R)
(exec 0 (, (foo $x) (bar $y) (baz $z)) (O (count (all $k) $k (cux $z $y $x))))
    "#;

    s.add_all_sexpr(SPACE_EXPRS.as_bytes()).unwrap();

    let mut t0 = Instant::now();
    let steps = s.metta_calculus(1000000000000000);
    println!("elapsed {} steps {} size {}", t0.elapsed().as_millis(), steps, s.btm.val_count());

    let mut v = vec![];
    s.dump_sexpr(expr!(s, "[2] all $"), expr!(s, "_1"), &mut v);
    // s.dump_all_sexpr(&mut v).unwrap();
    let res = String::from_utf8(v).unwrap();

    println!("result: {res}");
    assert_eq!(res, "18\n")
}

fn sink_wasm_add() {
    let mut s = Space::new();

    const SPACE_EXPRS: &str = r#"
(wasm add
    (if (i32.and (i32.and
            (i32.eq (i32.load8_u 0 (i32.const 0)) (i32.const 0x02))
            (i32.eq (i32.load8_u 0 (i32.const 1)) (i32.const 0xc4)))
            (i32.eq (i32.load8_u 0 (i32.const 6)) (i32.const 0xc4)))
      (then
        (i32.store 1 (i32.const 0) (i32.const 0xc4))
        (i32.store 1 (i32.const 1) (call 0 (i32.add
            (call 0 (i32.load 0 (i32.const 2)))
            (call 0 (i32.load 0 (i32.const 7))))))
      )
      (else unreachable)
    )
)

(exec 0 (, (wasm add $f)) (,
  (exec 1 (, (xs $i $x) (ys $i $y))
          (O (wasm $f ($x $y))))
))
    "#; // (zs $i $z) $z
    let nargs = 1_000_000;
    s.add_all_sexpr(SPACE_EXPRS.as_bytes()).unwrap();
    let mut args = vec![];
    let options = ["x", "y"];
    for (k, a) in options.iter().enumerate() {
        for i in 0i32..nargs {
            let mut e = vec![item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(2)), a.as_bytes()[0], b's'];
            let is = i.to_string();
            e.push(item_byte(Tag::SymbolSize(is.len() as _)));
            e.extend_from_slice(is.as_bytes());
            e.push(item_byte(Tag::SymbolSize(4)));
            e.extend_from_slice(((options.len() as i32)*i + (k as i32)).to_be_bytes().as_slice());
            s.btm.insert(&e[..], ());
        }
    }
    s.add_all_sexpr(&args[..]).unwrap();

    let mut t0 = Instant::now();
    let steps = s.metta_calculus(1);
    println!("elapsed {} steps {} size {}", t0.elapsed().as_millis(), steps, s.btm.val_count());

    // let mut v = vec![];
    // s.dump_sexpr(expr!(s, "[4] cux $ $ $"), expr!(s, "[3] _3 _2 _1"), &mut v);
    // s.dump_all_sexpr(&mut v).unwrap();
    // let res = String::from_utf8(v).unwrap();

    // println!("result: {res}");
    // assert_eq!(res, "(1 x P)\n(2 x P)\n(3 x P)\n(1 y P)\n(2 y P)\n(3 y P)\n(1 x Q)\n")
}

fn bench_sink_odd_even_sort(elements: usize) {
    let mut s = Space::new();
    const SPACE_EXPRS: &str = r#"
((phase $p)  (, (parity $i $p) (succ $i $si) (A $i $e) (A $si $se) (lt $se $e))
             (O (- (A $i $e)) (- (A $si $se)) (+ (A $i $se)) (+ (A $si $e))))
(phase 0 odd) (phase 1 even)
(exec repeat (, (A $k $_) (phase $kp $phase) ((phase $phase) $p0 $t0))
             (, (exec ($k $kp) $p0 $t0)))
    "#;
    let mut arr: Vec<_> = (0..elements).map(|i| { let mut hs = std::hash::DefaultHasher::new(); i.hash(&mut hs); base64::engine::general_purpose::STANDARD_NO_PAD.encode((hs.finish() as u32).to_be_bytes()) }).collect();
    let mut ARRAY: String = (0..elements).map(|x| format!("(A {x} {})\n", arr[x])).collect();
    // println!("array {ARRAY}");
    s.add_all_sexpr(ARRAY.as_bytes()).unwrap();
    let mut SUCCS: String = (0..elements).map(|x| format!("(succ {x} {})\n", x+1)).collect();
    s.add_all_sexpr(SUCCS.as_bytes()).unwrap();
    let mut PARITY: String = (0..elements).map(|x| format!("(parity {x} {})\n", if x % 2 == 0 { "even" } else { "odd" })).collect();
    s.add_all_sexpr(PARITY.as_bytes()).unwrap();
    arr.sort();
    let arr_ptr = &arr;
    let mut ORDER: String = (0..elements).flat_map(|x| (0..x).map(move |y| format!("(lt {} {})\n", arr_ptr[y], arr_ptr[x]))).collect();
    s.add_all_sexpr(ORDER.as_bytes()).unwrap();
    s.add_all_sexpr(SPACE_EXPRS.as_bytes()).unwrap();

    let mut t0 = Instant::now();
    let steps = s.metta_calculus(1000000000000000);
    println!("elapsed {} steps {} size {}", t0.elapsed().as_millis(), steps, s.btm.val_count());

    let mut v = vec![];
    // s.dump_all_sexpr(&mut v).unwrap();
    s.dump_sexpr(expr!(s, "[3] A $ $"), expr!(s, "_2"), &mut v);
    let res = String::from_utf8(v).unwrap();

    // println!("result:\n{res}");
    assert_eq!(res[..res.len()-1], arr.iter().map(|i| i.to_string()).join("\n"));
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

    s.add_all_sexpr(SPACE_EXPRS.as_bytes()).unwrap();
    s.add_sexpr(AXIOM_EXPRS.as_bytes(),expr!(s, "$"), expr!(s, "[2] axiom _1")).unwrap();

    let steps = s.metta_calculus(1000000000000000);

    assert_eq!(s.btm.val_count(), 79);
}

fn bench_logic_query() {
    use std::io::Read;
    let mut s = Space::new();

    let mut expr_buf = vec![];
    std::fs::File::open("resources/big.metta").unwrap().read_to_end(&mut expr_buf).unwrap();
    s.add_all_sexpr(&expr_buf[..]).unwrap();

    let mut t0 = Instant::now();
    s.add_all_sexpr(b"(exec 0 (, (axiom $x) (axiom $x)) (, (combined $x)))").unwrap();
    s.metta_calculus(1);
    println!("combined elapsed {} ms size {}", t0.elapsed().as_millis(), s.btm.val_count());

    let mut t1 = Instant::now();
    s.add_all_sexpr(b"(exec 0 (, (axiom (= $lhs $rhs)) (axiom (= $rhs $lhs))) (, (reversed $lhs $rhs)))").unwrap();
    s.metta_calculus(1);
    println!("reversed elapsed {} ms size {}", t1.elapsed().as_millis(), s.btm.val_count());
    
    // yikes, this is much slower than the old bidirectional transition in `server`?
    // combined elapsed 236156 ms size 1677208
    // reversed elapsed 435670 ms size 3348972
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

    s.add_all_sexpr(SPACE_EXPRS.as_bytes()).unwrap();
    s.add_all_sexpr(KB_EXPRS.as_bytes()).unwrap();

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

    s.add_all_sexpr(SPACE_EXPRS.as_bytes()).unwrap();
    s.add_all_sexpr(KB_EXPRS.as_bytes()).unwrap();

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

    s.add_all_sexpr(SPACE_EXPRS.as_bytes()).unwrap();
    s.add_all_sexpr(KB_EXPRS.as_bytes()).unwrap();

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

    s.add_all_sexpr(SPACE_EXPRS.as_bytes()).unwrap();
    s.add_all_sexpr(KB_EXPRS.as_bytes()).unwrap();


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

fn bench_cm0(to_copy: usize) {
    let mut s = Space::new();
    
    // Follow along https://en.wikipedia.org/wiki/Counter_machine#Program
    
    // non-peano csv version see cm1
    /*
    s.load_csv(INSTRS_CSV.as_bytes(), expr!(s, "$"), expr!(s, "[2] program _1"), b',').unwrap();
    s.load_csv(REGS_CSV.as_bytes(), expr!(s, "[2] $ $"), expr!(s, "[3] state 0 [3] REG _1 _2"), b',').unwrap();
    JZ,2,5\nDEC,2,2INC,3,3\nINC,1,4\nJZ,0,0\nJZ,1,9\nDEC,1,7\nINC,2,8\nJZ,0,5\nH,0,0
     */
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
    "#, peano(to_copy));

    s.add_all_sexpr(SPACE_MACHINE.as_bytes()).unwrap();

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
    assert!(res.contains(format!("({} {})", last_ts, peano(to_copy)).as_str()));
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

    s.add_all_sexpr(SPACE_EXPRS.as_bytes()).unwrap();

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

    s.add_all_sexpr(SPACE.as_bytes()).unwrap();

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

    s.add_all_sexpr(SPACE.as_bytes()).unwrap();

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

    s.add_all_sexpr(edges.as_bytes()).unwrap();
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

    s.add_all_sexpr(edges.into_iter().collect::<String>().as_bytes()).unwrap();
    println!("constructed {} nodes {} edges", nnodes, nedges);

    for k in 3..(max_clique+1) {
        let query = clique_query(k);
        println!("executing query {}", query);
        let t0 = Instant::now();
        s.add_sexpr(query.as_bytes(), expr!(s, "$"), expr!(s, "_1"));
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

    s.add_sexpr(ops.as_bytes(), expr!(s, "$"), expr!(s, "_1"));

    let mut args = String::new(); // e.g. (args ䷽ ䷣ ䷜ ䷣)
    for i in 0..10_000 {
        let x0 = rng.random_range(0..DS);
        let x1 = rng.random_range(0..DS);
        let y0 = rng.random_range(0..DS);
        let y1 = rng.random_range(0..DS);
        args.push_str(format!("(args {} {} {} {})", SYM[x0], SYM[x1], SYM[y0], SYM[y1]).as_str())
    }
    s.add_sexpr(args.as_bytes(), expr!(s, "$"), expr!(s, "_1"));

    s.add_sexpr(r"(exec 0 (, (args $x0 $y0 $x1 $y1) ($x0 /\ $x1 = $xl) ($x0 \/ $x1 = $xh) ($y0 /\ $y1 = $yl) ($y0 \/ $y1 = $yh) ($xh - $xl = $dx) ($yh - $yl = $dy) (² $dx = $dx2) (² $dy = $dy2) ($dx2 + $dy2 = $d2) (√ $d2 = $d)) (, (res $d)))".as_bytes(), expr!(s, "$"), expr!(s, "_1")).unwrap();
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

#[cfg(all(feature = "nightly"))]
fn jsonl_upaths<IPath: AsRef<std::path::Path>, OPath : AsRef<std::path::Path>>(jsonl_path: IPath, upaths_path: OPath) {
    println!("mmapping JSONL file {:?}", jsonl_path.as_ref().as_os_str());
    println!("writing out unordered .paths file {:?}", upaths_path.as_ref().as_os_str());
    let json_file = std::fs::File::open(jsonl_path).unwrap();
    let json_mmap = unsafe { memmap2::Mmap::map(&json_file).unwrap() };
    let upaths_file = std::fs::File::create_new(upaths_path).unwrap();
    let mut upaths_bufwriter = std::io::BufWriter::new(upaths_file);

    let mut s = Space::new();
    let t0 = Instant::now();
    let (lines, written) = s.jsonl_to_paths(&*json_mmap, &mut upaths_bufwriter).unwrap();
    println!("written {written} ({lines} lines) in {} ms", t0.elapsed().as_millis());
    // (zephy)
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
        s.add_sexpr(&*metta_mmap, expr!(s, "$"), expr!(s, format!("[3] U {} _1", &name[..name.len()-6]).as_str())).unwrap();
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
    s.add_all_sexpr(SPACE.as_bytes()).unwrap();

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
    s.add_all_sexpr(SPACE.as_bytes()).unwrap();
    // let mut math_expr_buf = vec![];
    // std::fs::File::open("/home/adam/Downloads/math_relations.metta").unwrap().read_to_end(&mut math_expr_buf).unwrap();
    // s.add_sexpr(&math_expr_buf[..], expr!(s, "$"), expr!(s, "_1")).unwrap();
    s.add_sexpr("(fun (mul (0.5 0.5) 0.2))".as_bytes(), expr!(s, "$"), expr!(s, "_1")).unwrap();

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

    s.add_all_sexpr(SPACE_EXPRS.as_bytes()).unwrap();

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

    s.add_all_sexpr(SPACE_EXPRS.as_bytes()).unwrap();
    s.add_all_sexpr(SUCCS.as_bytes()).unwrap();

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

    s.add_all_sexpr(SPACE_EXPRS.as_bytes()).unwrap();
    s.add_all_sexpr(SUCCS.as_bytes()).unwrap();

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

    s.add_all_sexpr(SPACE_EXPRS.as_bytes()).unwrap();
    s.add_all_sexpr(SUCCS.as_bytes()).unwrap();

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
(kb (: (+) (-> (term) (-> (term) (term)))))
(kb (: (=) (-> (term) (-> (term) (wff)))))
(kb (: (t) (term)))
(kb (: (0) (term)))

(kb (: (tpl) (-> (: $x (term)) (-> (: $y (term))
                      (: ((+) $x $y) (term))))))
(kb (: (weq) (-> (: $x (term)) (-> (: $y (term))
                      (: ((=) $x $y) (wff))))))
(kb (: (wim) (-> (: $P (wff)) (-> (: $Q (wff))
                      (: ((->) $P $Q) (wff))))))

(kb (: (a2-curry) (-> (: $a (term))
                  (: ((=) ((+) $a (0)) $a) (|-)))))
(kb (: (a1-curry) (-> (: $a (term)) (-> (: $b (term)) (-> (: $c (term))
                  (: ((->) ((=) $a $b) ((->) ((=) $a $c) ((=) $b $c))) (|-)))))))
(kb (: (mp-curry) (-> (: $P (wff)) (-> (: $Q (wff))
                  (-> (: $P (|-)) (-> (: ((->) $P $Q) (|-)) (: $Q (|-))))))))

(kb (: (a2) (-> (: $a (term)) (: ((=) ((+) $a (0)) $a) (|-)))))
(kb (: (a1) (-> (: $a (term)) (: $b (term)) (: $c (term)) (: ((->) ((=) $a $b) ((->) ((=) $a $c) ((=) $b $c))) (|-)))))
(kb (: (mp) (-> (: $P (wff)) (: $Q (wff)) (: $P (|-)) (: ((->) $P $Q) (|-)) (: $Q (|-)))))

(exec (0 lift) (, (kb (: $t $T))) (, (ev (: $t $T))))

(exec (1 tpl-apply)
  (, (ev (: $x (term)))
     (ev (: $y (term))))
  (, (ev (: ((+) $x $y) (term)))))

(exec (1 weq-apply)
  (, (ev (: $a (term)))
     (ev (: $b (term))))
  (, (ev (: ((=) $a $b) (wff)))))

(exec (1 wim-apply)
  (, (ev (: $P (wff)))
     (ev (: $Q (wff))))
  (, (ev (: ((->) $P $Q) (wff)))))

(exec (1 a2-instantiate-t)
  (, (ev (: $a (term))))
  (, (ev (: ((=) ((+) $a (0)) $a) (|-)))))

(exec (1 a1-instantiate-PtoQ)
  (, (ev (: $a (term)))
     (ev (: $b (term)))
     (ev (: $c (term))))
  (, (ev (: ((->) ((=) $a $b)
               ((->) ((=) $a $c)
                       ((=) $b $c))) (|-)))))

(exec (2 derive-P-to-Q-direct3)
  (, (ev (: $P (wff)))
     (ev (: $P (|-)))
     (ev (: ((->) $P $IMP) (|-)))
     (ev (: $IMP (wff))))
  (, (ev (: $IMP (|-)))))

(exec (3 assemble-final-proof-direct)
  (, (ev (: $P (wff)))
     (ev (: $P (|-)))
     (ev (: ((->) $P $Q) (|-)))
     (ev (: $Q (wff))))
  (, (ev (: $Q (|-)))))
"#;


    let mut s = Space::new();
    let t0 = Instant::now();
    s.add_all_sexpr(P.as_bytes()).unwrap();

    // Targets (kept identical to mm1())
    let want_ev_term_tplus0    = "(ev (: ((+) (t) (0)) (term)))";
    let want_ev_wff_p          = "(ev (: ((=) ((+) (t) (0)) (t)) (wff)))";
    let want_ev_wff_q          = "(ev (: ((=) (t) (t)) (wff)))";
    let want_ev_proof_p        = "(ev (: ((=) ((+) (t) (0)) (t)) (|-)))";
    let want_ev_proof_ptoq     = "(ev (: ((->) ((=) ((+) (t) (0)) (t)) ((=) (t) (t))) (|-)))";
    let want_ev_proof_ptoptoq  = "(ev (: ((->) ((=) ((+) (t) (0)) (t)) ((->) ((=) ((+) (t) (0)) (t)) ((=) (t) (t)))) (|-)))";
    let want_final_evidence    = "(ev (: ((=) (t) (t)) (|-))";

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
        // trying to get: (ev (: ((=) ((+) (t) (0)) (t)) (|-)))
        s.dump_sexpr(
            expr!(s, "[2] ev [3] : [3] (=) $ $ (|-)"),  // Pattern
            expr!(s, "[2] ev [3] : [3] (=) _1 _2 (|-)"),  // Template: full reconstruction
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
            expr!(s, "[2] ev [3] : [3] (->) [3] (=) [3] (+) (t) (0) (t) [3] (=) (t) (t) (|-)"),  // Pattern
            expr!(s, "[2] ev [3] : [3] (->) [3] (=) [3] (+) (t) (0) (t) [3] (=) (t) (t) (|-)"),  // Template: return same expression
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

fn mm2_bc() {
    // Program: universe, typed constructors, axioms (curried), tiny pipeline, and final assembly.
    const P: &str = r#"
  (kb (: (+) (-> (term) (term) (term))))
  (kb (: (=) (-> (term) (term) (wff))))
  (kb (: (t) (term)))
  (kb (: (0) (term)))
  (kb (: tt (: (t) (term))))

  (kb (: (a2-curry) (-> (: $a (term)) (: ((=) ((+) $a (0)) $a) (|-)))))

  (kb (: (tpl) (-> (: $x (term)) (: $y (term)) (: ((+) $x $y) (term)))))
  (kb (: (weq) (-> (: $x (term)) (: $y (term)) (: ((=) $x $y) (wff)))))
  (kb (: (wim) (-> (: $P (wff)) (: $Q (wff)) (: ((->) $P $Q) (wff)))))
  (kb (: (a2) (-> (: $a (term)) (: ((=) ((+) $a (0)) $a) (|-)))))
  (kb (: (a1) (-> (: $t (term)) (: $r (term)) (: $s (term)) (: ((->) ((=) $t $r) ((->) ((=) $t $s) ((=) $r $s))) (|-)))))
  (kb (: (mp) (-> (: $P (wff)) (: $Q (wff)) (: $P (|-)) (: ((->) $P $Q) (|-)) (: $Q (|-)))))

  (exec (0 lift) (, (kb (: $t $T))) (, (ev (: $t $T))))
((step (0 base))
    (, (goal (: $proof $conclusion)) (kb (: $proof $conclusion)))
    (,
      (ev (: $proof $conclusion))
      (debug base (: $proof $conclusion) found in kb)))

  ((step (1 abs-curry2))
      (, (goal (: $proof $conclusion)))
      (,
        (goal (: $lhs (-> $synth (: $proof $conclusion)) ))
        (debug abs-curry2 (: $proof $conclusion) made (: $lhs (-> $synth (: $proof $conclusion))))))

  ((step (2 rev2-typed))
    (, (ev (: $lhs (-> (: $arg1 $T1) (: $arg2 $T2) $R)))
      (goal (: $_ $R)))
    (, (goal (: $arg1 $T1))
      (goal (: $arg2 $T2))
      (debug rev2-typed need (: $arg1 $T1) and (: $arg2 $T2))))

((step (2 rev2))
    (, (ev (: $name (-> (: $b1 $b2) (: $c1 $c2) (: $d1 $d2))))
       (goal (: $d1 $d2)))
    (, (goal (: $b1 $b2))
       (goal (: $c1 $c2))
       (debug rev2-cl (goal (: $d1 $d2)) )))

  (exec bc
      (, ((step $x) $premises0 $conclusions0)
         (exec bc $premises1 $conclusions1) )
      (, (exec $x $premises0 $conclusions0)
         (exec bc $premises1 $conclusions1) ))

  (goal (: ((=) (t) (0)) (wff)))
    "#;


    let mut s = Space::new();
    let t0 = Instant::now();
    s.add_all_sexpr(P.as_bytes()).unwrap();

    // Targets (kept identical to mm1())
    let want_ev_term_tplus0    = "(ev (: ((+) (t) (0)) (term)))";
    let want_ev_wff_p          = "(ev (: ((=) ((+) (t) (0)) (t)) (wff)))";
    let want_ev_wff_q          = "(ev (: ((=) (t) (t)) (wff)))";
    let want_ev_proof_p        = "(ev (: ((=) ((+) (t) (0)) (t)) (|-)))";
    let want_ev_proof_ptoq     = "(ev (: ((->) ((=) ((+) (t) (0)) (t)) ((=) (t) (t))) (|-)))";
    let want_ev_proof_ptoptoq  = "(ev (: ((->) ((=) ((+) (t) (0)) (t)) ((->) ((=) ((+) (t) (0)) (t)) ((=) (t) (t)))) (|-)))";
    let want_final_evidence    = "(ev (: ((=) (t) (t)) (|-))";

    println!("=== MM2 (bc): Proving ⊢ (t = t) ===");

    let mut ticks = 0usize;
    loop {
        ticks += 1;
        let t1 = Instant::now();
        let n = s.metta_calculus(1);
        println!("executing step {} ({}) took {} ms (unifications {}, writes {}, transitions {})", ticks, n, t1.elapsed().as_millis(), unsafe { unifications }, unsafe { writes }, unsafe { transitions });

        // if n == 1 { continue } // comment out if you want the analysis at every step

        println!("space size {}", s.btm.val_count());
        let total_t = t0.elapsed();

        let mut buf = Vec::new();
        s.dump_all_sexpr(&mut buf).unwrap();
        // s.dump_all_sexpr(&mut buf).unwrap();
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
            println!("\n== mm2 (bc): ✅ SUCCESS in {:?} after {} tick(s) ==", total_t, ticks);
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

        if n == 0 || ticks >= 7 {
            println!("\n== mm2 (bc): — FAILURE in {:?} after {} tick(s) ==", t0.elapsed(), ticks);
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

fn mm2_bc_v3() {
    // MM2 Backward Chainer: Proving t = t via reflexivity
    // Strategy: Use a1 and a2 axioms with two MP steps
    const P: &str = r#"
  ;; Type signatures for constructors
  (kb (: (+) (-> (term) (term) (term))))  ;; Addition operator
  (kb (: (=) (-> (term) (term) (wff))))   ;; Equality predicate
  (kb (: (t) (term)))                      ;; Constant t
  (kb (: (0) (term)))                      ;; Constant 0
  (kb (: tt (: (t) (term))))               ;; Named proof that t is a term

  ;; Type constructors (used to build wffs and terms)
  (kb (: (tpl) (-> (: $x (term)) (: $y (term)) (: ((+) $x $y) (term)))))
  (kb (: (weq) (-> (: $x (term)) (: $y (term)) (: ((=) $x $y) (wff)))))
  (kb (: (wim) (-> (: $P (wff)) (: $Q (wff)) (: ((->) $P $Q) (wff)))))

  ;; Axioms
  (kb (: (a2) (-> (: $a (term)) (: ((=) ((+) $a (0)) $a) (|-)))))  ;; a + 0 = a
  (kb (: (a1) (-> (: $t (term)) (: $r (term)) (: $s (term))
                  (: ((->) ((=) $t $r) ((->) ((=) $t $s) ((=) $r $s))) (|-)))))  ;; Transitivity

  ;; Modus Ponens inference rule
  (kb (: (mp) (-> (: $P (wff)) (: $Q (wff)) (: $P (|-)) (: ((->) $P $Q) (|-)) (: $Q (|-)))))

  ;; Priority 00: Initial lifting from KB to evidence
  (exec (0000 lift-kb-to-ev)
    (, (kb (: $t $T)))
    (, (ev (: $t $T))))

  ;; Priority 04b: Special MP for contracting P→(P→Q) with P to get P→Q
  ; thread 'main' (1910560) panicked at kernel/src/space.rs:146:124:
  ; index out of bounds: the len is 0 but the index is 0
  ((step (0400 mp-contraction))
    (, (goal (: ((->) $P $Q) (|-)))
      (ev (: $P (|-)))
      (ev (: ((->) $P ((->) $P $Q)) (|-))))
    (, (goal (: $P (wff)))
      (goal (: $Q (wff)))
      (exec (04000 complete-mp-contraction)
        (, (ev (: $P (wff)))
            (ev (: $Q (wff)))
            (ev (: $P (|-)))
            (ev (: ((->) $P ((->) $P $Q)) (|-))))
        (, (ev (: ((->) $P $Q) (|-)))
            (debug mp-contraction completed ((->) $P $Q))))
      (debug mp-contraction trying to prove ((->) $P $Q))))

  ;; same error
  ; ((step (0400 mp-contraction))
    ; (, (goal (: ((->) $P $Q) (|-)))
      ; (ev (: $P (|-)))
      ; (ev (: ((->) $P ((->) $P $Q)) (|-))))
    ; (, (goal (: $P (wff)))
      ; (goal (: $Q (wff)))
      ; (exec (04000 complete-mp-contraction)
        ; (, (ev (: $P (wff)))
            ; (ev (: $Q (wff)))
            ; (ev (: $P (|-)))
            ; (ev (: ((->) $P ((->) $P $Q)) (|-))))
        ; (, (ev (: ((->) $P $Q) (|-)))))))

  ;; Priority 05: Backward chain MP (most specific case)
  ((step (0501 backchain-mp))
    (, (ev (: $name (-> (: $a $Ta) (: $b $Tb) (: $c $Tc) (: $d $Td) (: $result $Tr))))
       (goal (: $result $Tr)))
    (, (goal (: $a $Ta))
       (goal (: $b $Tb))
       (goal (: $c $Tc))
       (goal (: $d $Td))
       (exec (05010 complete-mp)
         (, (ev (: $a $Ta))
            (ev (: $b $Tb))
            (ev (: $c $Tc))
            (ev (: $d $Td))
            (ev (: $name (-> (: $a $Ta) (: $b $Tb) (: $c $Tc) (: $d $Td) (: $result $Tr)))))
         (, (ev (: $result $Tr))
            (debug completed-mp ($name args) -> (: $result $Tr))))
       (debug backchain-mp (: $result $Tr) needs four args)))

;; Remove the old 0501 rule and potentially 0600 if this works better



  ;; Main backward chaining executor
  (exec bc
      (, ((step $x) $premises0 $conclusions0)
         (exec bc $premises1 $conclusions1))
      (, (exec $x $premises0 $conclusions0)
         (exec bc $premises1 $conclusions1)))

  ;; Goal: Prove t = t
  (goal (: ((=) (t) (t)) (|-)))
    "#;


    let mut s = Space::new();
    let t0 = Instant::now();
    s.add_all_sexpr(P.as_bytes()).unwrap();

    println!("=== MM2 (bc v3): Proving ⊢ (t = t) ===");

    let mut ticks = 0usize;
    let multiplier = 5;
    loop {
        ticks += multiplier;
        let t1 = Instant::now();
        let n = s.metta_calculus(multiplier);
        println!("executing step {} ({}) took {} ms (unifications {}, writes {}, transitions {})",
                 ticks, n, t1.elapsed().as_millis(),
                 unsafe { unifications }, unsafe { writes }, unsafe { transitions });

        println!("space size {}", s.btm.val_count());

        let mut buf = Vec::new();
        s.dump_all_sexpr(&mut buf).unwrap();
        let dump = String::from_utf8_lossy(&buf);

        // if n == 0 || ticks >= 50 {
        //     println!("\n== mm2 (bc v3): — ran for {:?} and {} tick(s) ==", t0.elapsed(), ticks);
        //     add_mm2_demo0_query_diagnostics(&mut s, ticks);
        //     add_mm2_demo0_diagnostics(&mut s, ticks);
        //     println!("\n--- Full Final State Dump ---");
        //     print!("{dump}");
        //     break;
        // }
    }
}

fn parse_csv() {
    let csv_input = "10,123,foo\n11,321,bar\n";
    let reconstruction = "(0 10 123 foo)\n(1 11 321 bar)\n";
    let mut s = Space::new();
    assert_eq!(s.load_csv(csv_input.as_bytes(), expr!(s, "$"), expr!(s, "_1"), b',').unwrap(), 2);
    let mut res = Vec::<u8>::new();
    s.dump_sexpr(expr!(s, "$"), expr!(s, "_1"),&mut res);
    assert_eq!(reconstruction, String::from_utf8(res).unwrap());
}

fn parse_json() {
    let json_input = r#"{"first_name": "John", "last_name": "Smith", "is_alive": true, "age": 27, "address": {"street_address": "21 2nd Street", "city": "New York", "state": "NY", "postal_code": "10021-3100"}, "phone_numbers": [{"type": "home", "number": "212 555-1234"}, {"type": "office", "number": "646 555-4567"}], "children": ["Catherine", "Thomas", "Trevor"], "spouse": null}"#;

    let mut s = Space::new();
    s.load_json(json_input.as_bytes());

    let mut v = vec![];
    s.dump_all_sexpr(&mut v).unwrap();
    let res = String::from_utf8(v).unwrap();
    
    println!("{}", res);
    assert_eq!(set_from_newlines(SEXPRS0), set_from_newlines(res.as_str()));
}

const SEXPRS0: &str = r#"(first_name John)
(last_name Smith)
(is_alive true)
(age 27)
(address (street_address 21 2nd Street))
(address (city New York))
(address (state NY))
(address (postal_code 10021-3100))
(phone_numbers (0 (type home)))
(phone_numbers (0 (number 212 555-1234)))
(phone_numbers (1 (type office)))
(phone_numbers (1 (number 646 555-4567)))
(children (0 Catherine))
(children (1 Thomas))
(children (2 Trevor))
(spouse null)
"#;


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
        #[arg(default_value = "default")]
        only: String,
    },
    Test {
    },
    #[command(arg_required_else_help = true)]
    Run {
        input_paths: Vec<String>,
        #[arg(long, default_value_t = 1000000000000000)]
        steps: usize,
        #[arg(long, default_value_t = 1)]
        instrumentation: usize,
        #[arg(long, short = 'o')]
        output_path: Option<String>,
        #[arg(long, short = 'p')]
        query_pattern: Option<String>,
        #[arg(long, short = 't')]
        query_template: Option<String>,
        #[arg(long, default_value_t = 0)]
        timeout: u64,
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
    // mm2_bc();
    // sink_add_remove();
    // bench_cm0(50);
    // tile_puzzle();
    // sink_odd_even_sort();
    // cross_join();
    // cross_join_dict();
    process_calculus_source_sink_bench(100, 20, 20);
    return;

    let args = Cli::parse();

    match args.command {
        Commands::Bench { only } => {
            #[cfg(debug_assertions)]
            println!("WARNING running in debug, if unintentional, build with --release");
            let mut selected: BTreeSet<&str> = only.split(",").collect();
            if selected.remove("default") { selected.extend(&["counter_machine", "transitive", "clique", "finite_domain", "process_calculus", "tile_puzzle_states"]) }
            if selected.remove("all") { selected.extend(&["counter_machine", "transitive", "clique", "finite_domain", "process_calculus", "exponential", "exponential_fringe", "odd_even_sort", "logic_query", "tile_puzzle_states"]) }
            if selected.remove("sinks") { selected.extend(&["odd_even_sort"]) }

            for b in selected {
                println!("=== benchmarking {} ===", b);
                match b {
                    "counter_machine" => { bench_cm0(50); }
                    "transitive" => { bench_transitive_no_unify(50000, 1000000); }
                    "clique" => { bench_clique_no_unify(200, 3600, 5); }
                    "finite_domain" => { bench_finite_domain(10_000); }
                    "process_calculus" => { process_calculus_bench(1000, 200, 200); }
                    "exponential" => { exponential(32); }
                    "exponential_fringe" => { exponential_fringe(15); }
                    "odd_even_sort" => { bench_sink_odd_even_sort(2000); }
                    "logic_query" => { bench_logic_query() }
                    "tile_puzzle_states" => { bench_tile_puzzle_states() }
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
            // func_type_unification(); // failing!
            top_level_match();

            process_calculus_reverse();
            logic_query();
            meta_ana();
            meta_ana_exec();

            bc0();

            source_space_two_bipolar_equal_crossed();
            source_act_two_bipolar_equal_crossed();
            source_space_act_two_bipolar_equal_crossed();
            source_cmp_eq();
            source_cmp_ne();

            sink_two_bipolar_equal_crossed();
            sink_two_positive_equal_crossed();
            sink_odd_even_sort();
            sink_add_remove();
            sink_add_remove_var();
            sink_head();
            sink_count_literal();
            sink_count_constant();
            sink_count();

            parse_csv();
            parse_json();
        }
        Commands::Run { input_paths, steps, instrumentation, output_path, query_pattern, query_template, timeout } => {
            #[cfg(debug_assertions)]
            println!("WARNING running in debug, if unintentional, build with --release");
            let mut s = Space::new();
            for input_path in &input_paths {
                let f = std::fs::File::open(input_path).unwrap();
                let mmapf = unsafe { memmap2::Mmap::map(&f).unwrap() };
                s.add_all_sexpr(&*mmapf);
            }
            if instrumentation > 0 { println!("loaded {} expressions", s.btm.val_count()) }
            println!("loaded {:?} ; running and outputing to {:?}", &input_paths, output_path.as_ref().or(Some(&"stdout".to_string())));
            let timeout_duration = if timeout > 0 { Some(Duration::from_secs(timeout)) } else { None };
            let t0 = Instant::now();
            let mut performed = 0;
            while performed < steps {
                if let Some(td) = timeout_duration {
                    if t0.elapsed() >= td {
                        break;
                    }
                }
                let p = s.metta_calculus(1);
                performed += p;
                if p == 0 {
                    break;
                }
            }
            println!("executing {performed} steps took {} ms (unifications {}, writes {}, transitions {})", t0.elapsed().as_millis(), unsafe { unifications }, unsafe { writes }, unsafe { transitions });
            if instrumentation > 0 { println!("dumping {} expressions", s.btm.val_count()) }
            let query_pattern_expr = query_pattern.as_ref().map(|p| expr!(s, p));
            let query_template_expr = query_template.unwrap_or("_1".to_string());
            if output_path.is_none() {
                let mut v = vec![];
                if let Some(pat) = query_pattern_expr {
                    s.dump_sexpr(pat, expr!(s, &query_template_expr), &mut v);
                } else {
                    s.dump_all_sexpr(&mut v).unwrap();
                }
                let res = String::from_utf8(v).unwrap();
                println!("result:\n{res}");
            } else {
                let f = std::fs::File::create(&output_path.unwrap()).unwrap();
                let mut w = std::io::BufWriter::new(f);
                if let Some(pat) = query_pattern_expr {
                    s.dump_sexpr(pat, expr!(s, &query_template_expr), &mut w);
                } else {
                    s.dump_all_sexpr(&mut w).unwrap();
                }
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
                    s.add_all_sexpr(&*mmapf);
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
                ("json", "upaths") => {
                    #[cfg(all(feature = "nightly"))]
                    // json upaths /mnt/data/enwiki-20231220-pages-articles-links/cqls.json /mnt/data/enwiki-20231220-pages-articles-links/cqls.upaths
                    json_upaths(input_path, some_output_path);
                }
                ("jsonl", "upaths") => {
                    #[cfg(all(feature = "nightly"))]
                    jsonl_upaths(input_path, some_output_path);
                }
                (_, _) => { panic!("unsupported conversion") }
            }
        }
    }
    return;
}
