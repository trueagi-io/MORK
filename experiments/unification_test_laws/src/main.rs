use std::{fmt::Write, num::NonZero, path::PathBuf};

use mork::expr;
use rand::random;
use unification_test_laws::{unify_with_mork_unifier, convert_and_add_line_numbers_big_metta, results_to_single_file};
// explore this later
// https://github.com/trueagi-io/MORK/blob/old_main/benchmarks/logic-query/src/main.rs

fn main() {
    let manifest = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let axioms = std::fs::read_to_string(manifest.join("tmp/big_.metta")).unwrap();

    // this first section is our source of truth
    let convert_big_metta        = !true;
    let run_mork_unifier         = !true;
    let run_prolog_unifier       = !true;
    let collect_results_and_diff =  true;

    // here we configure the tests for queries in the space
    let run_in_mork_space        =  true;
    let run_in_mork_space_config = RunInMorkSpace {
        whole_set                : !true,
        identity_assertion       : !true,
        iterate_left             :  true,
        iterate_right            :  true,
        // this takes a __very__  long time to compute (on my computer, 20 saturated threads, ~18 hours)
        iterate_left_right       : !true,

        axioms   : &axioms,
        manifest : &manifest,
    };

    // prep big.metta to enumerate axioms
    if convert_big_metta {
        convert_and_add_line_numbers_big_metta();
    }

    // run mork unifier
    if run_mork_unifier {
        unify_with_mork_unifier();
    }


    // run prolog unifier
    if run_prolog_unifier {
        let manifest = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let tmp_dir = manifest.join("tmp");

        let prolog_exit_status = std::process::Command::new("swipl")
            .current_dir(&tmp_dir)
            .args(["-O","-g","['../axiom_unify.prolog'], write_all_results_concurrent, halt."])
            .spawn().unwrap().wait();
        // println!("SWI Prolog status {:?}", prolog_exit_status);
    }

    // collect results
    if collect_results_and_diff {
        results_to_single_file(&["mork", "prolog"]);

        let mork   = [env!("CARGO_MANIFEST_DIR"), "/tmp/mork/all_results.metta"].into_iter().collect::<String>();
        let prolog = [env!("CARGO_MANIFEST_DIR"), "/tmp/prolog/all_results.metta"].into_iter().collect::<String>();


        if let Ok(proc) = &std::process::Command::new("diff").args([&mork, &prolog]).output()
        {
            let diff =  core::str::from_utf8(&proc.stdout).unwrap();
            println!("{}", diff.len());
            println!("\nMORK-PROLOG\nBEGIN DIFF\n{}END DIFF", diff);
            if diff.len() > 0 { println!("EXPRESSION UNIFIER IS BROKEN"); return;}
        }
    }


    // What follows are tests for queries in the space.
    // if MORK expression and Prolog are not in agreement, then the following is a waste of time.
    assert!(collect_results_and_diff);

    if run_in_mork_space {
        run_in_mork_space_config.run();
    }

    // collect results
    if collect_results_and_diff {
        let results_dir = |dir| [env!("CARGO_MANIFEST_DIR"), "/tmp/", dir, "/all_results.metta"].into_iter().collect::<String>();
        let mork        = results_dir("mork");

        results_to_single_file(
        &["whole_set"
        , "iterate_left"
        , "iterate_right"
        , "iterate_left_right"
        ]);
        
        let diff_proc = |dir| std::process::Command::new("diff").args([&mork, &results_dir(dir)]).output();
        if let Ok(proc) = diff_proc("whole_set")
        {
            let diff =  core::str::from_utf8(&proc.stdout).unwrap();
            println!("\nMORK-MORK_SPACE_WHOLE_SET\nBEGIN DIFF\n{}END DIFF", diff);
        }
        if let Ok(proc) = diff_proc("iterate_left")
        {
            let diff =  core::str::from_utf8(&proc.stdout).unwrap();
            println!("\nMORK-MORK_SPACE_ITERATE_LEFT\nBEGIN DIFF\n{}END DIFF", diff);
        }
        if let Ok(proc) = diff_proc("iterate_right")
        {
            let diff =  core::str::from_utf8(&proc.stdout).unwrap();
            println!("\nMORK-MORK_SPACE_ITERATE_RIGHT\nBEGIN DIFF\n{}END DIFF", diff);
        }
        if let Ok(proc) = diff_proc("iterate_left_right")
        {
            let diff =  core::str::from_utf8(&proc.stdout).unwrap();
            println!("\nMORK-MORK_SPACE_ITERATE_LEFT_RIGHT\nBEGIN DIFF\n{}END DIFF", diff);
        }
    }
}






struct RunInMorkSpace<'a> {
    whole_set            : bool,
    identity_assertion   : bool,
    iterate_left         : bool,
    iterate_right        : bool,
    // this takes a __very__  long time to compute (on my computer, 20 saturated threads, ~18 hours)
    iterate_left_right   : bool,
    axioms               : &'a str,
    manifest             : &'a std::path::Path
}

/// This is primarily a means to avoid overwriting previos results by accident when a run goes poorly.
/// Results will be added to a "<dir_name>_WIP" folder. When update is called, the files in <dir_name> are archived to "<dir_name>_OLD", and the WIP folder gets move to "<dir_name>"
struct ResultsWIPControl {
    outdir       : std::path::PathBuf,
    old_outdir   : std::path::PathBuf,
    tmp_outdir   : std::path::PathBuf,
    results      : std::path::PathBuf,
    unifications : std::path::PathBuf,
}
impl ResultsWIPControl {
    fn new(folder : PathBuf) -> Self {
        let mut old_outdir = folder.clone();
        old_outdir.as_mut_os_string().push("_OLD");

        let mut tmp_outdir = folder.clone();
        tmp_outdir.as_mut_os_string().push("_WIP");
        let results = tmp_outdir.join("results");
        let unifications = tmp_outdir.join("unifications");

        std::fs::create_dir_all(&results).unwrap();
        std::fs::create_dir_all(&unifications).unwrap();

        Self { outdir: folder, old_outdir, tmp_outdir, results, unifications  }
    }
    fn result_file(&self, filename : &str) -> std::fs::File {
        std::fs::File::create(self.results.join(filename)).unwrap()
    }
    fn unifications_file(&self, filename : &str) -> std::fs::File {
        std::fs::File::create(self.unifications.join(filename)).unwrap()
    }
    /// This is explictly __NOT__ a destructor.
    fn update_results(self) {
        let Self { outdir, old_outdir, tmp_outdir, results, unifications } = self;
        std::fs::create_dir_all(&outdir).unwrap();

        std::fs::remove_dir_all(&old_outdir);
        std::fs::create_dir_all(&old_outdir).unwrap();
        std::fs::rename(&outdir, old_outdir).unwrap();

        std::fs::remove_dir_all(&outdir);
        std::fs::create_dir_all(&outdir).unwrap();
        std::fs::rename(tmp_outdir, outdir).unwrap();
    }

}

impl RunInMorkSpace<'_> {
    fn results_wip_control(&self, dir_name : &str) -> ResultsWIPControl {
        let mut folder = self.manifest.join("tmp");
        folder.push(dir_name);
        ResultsWIPControl::new(folder)
    }
    fn identity_assertion_run(&self) {
        let mut s = mork::space::Space::new();
        println!("\nINDENTY ONLY");
        s.add_all_sexpr(self.axioms.as_bytes()).unwrap();;

        s.add_all_sexpr(b"(exec 0 (, (line $n (axiom $x))
                                     (line $n (axiom $x))
                                  )
                                  (O (+     (unifies $n $n)  )
                                     (count (unifications $c) $c ($n $m))
                                  )
                          )").unwrap();
        s.metta_calculus(10000000);

        let mut w = String::new();
        // s.dump_sexpr(expr!(s,"[3] unifies $ $"), expr!(s,"[3] unifies _1 _2"),  unsafe { w.as_mut_vec() });
        s.dump_sexpr(expr!(s,"[2] unifications $"), expr!(s,"[2] unifications _1"),  unsafe { w.as_mut_vec() });
        core::assert_eq!(&w, "(unifications 100001)\n");
    }

    fn whole_set_run(&self) {
        println!("\nWHOLE SET");

        let outdir       = self.manifest.join("tmp/whole_set");
        let results      = outdir.join("results");
        let unifications = outdir.join("unifications");
        std::fs::create_dir_all(&results);
        std::fs::create_dir_all(&unifications);

        let mut s = mork::space::Space::new();

        s.add_all_sexpr(self.axioms.as_bytes()).unwrap();;

        s.add_all_sexpr(b"(exec 0 (, (line $n (axiom $x))
                                     (line $m (axiom $x))
                                  )
                                  (, (unifies $n $m) )
                          )").unwrap();
        s.add_all_sexpr(b"(exec 1 (, (unifies $n $m) ) (O (count (unifications $n $c) $c ($n $m))) )");
        s.metta_calculus(10000000);

        let mut outfile  = std::fs::File::create(results.join(format!("axioms_all.metta"))).unwrap();
        let mut outfile_ = std::fs::File::create(unifications.join(format!("axioms_all.metta"))).unwrap();
        s.dump_sexpr(expr!(s,"[3] unifies $ $"), expr!(s,"[3] unifies _1 _2"),  &mut outfile);
        s.dump_sexpr(expr!(s,"[3] unifications $ $"), expr!(s,"[3] unifications _1 _2"),  &mut outfile_ );
    }

    // construct execs for each `n` where `n` is the right hand side argument.
    fn iterate_left_run(&self) {

        self.iterate_runs_multithreaded_boilerplate("iterate_left", "", &|iteration|{
            use std::io::Write;
            let mut additions = String::new();
            write!(unsafe { additions.as_mut_vec() }, "(n {}) ", iteration);
            additions.write_str(
                "(exec 0 (, (n $n) )
                         (,  (exec 0 (, (line $n (axiom $x)) (line $m (axiom $x)) )
                                     (, (unifies $n $m) )
                             )
                         )
                 )"
            );
            additions
        });
    }

    // construct execs for each `m` where `m` is the right hand side argument.
    fn iterate_right_run(&self) {

        self.iterate_runs_multithreaded_boilerplate("iterate_right", "", &|iteration| {
            use std::io::Write;
            let mut additions = String::new();
            write!(unsafe { additions.as_mut_vec() }, "(m {}) ", iteration);
            additions.write_str(
                "(exec 0 (, (m $m) )
                         (,  (exec 0 (, (line $n (axiom $x)) (line $m (axiom $x)) )
                                     (, (unifies $n $m) )
                             )
                         )
                 )"
            );
            additions
        });
    }

    /// construct individual execs for each `n` and `m` pair
    /// 
    /// Avoid running this if possible, it's crazy slow. 
    /// This takes a __very__  long time to compute (on my computer, 20 saturated threads, ~18 hours)
    /// 
    /// Runnig it however did show that expression unification is working correctly.
    /// If this test fails then fix expression unification/application first!
    fn iterate_left_right_run(&self) {
        let mut ms = String::new();
        let range_r = [0, 100001];
        for each_r in range_r[0]..=range_r[1] {
            use std::io::Write;
            write!(unsafe { ms.as_mut_vec() }, "(m {}) ", each_r);
        }
        self.iterate_runs_multithreaded_boilerplate("iterate_left_right", &ms, &|iteration| {
            use std::io::Write;
            let mut additions = String::new();
            write!(unsafe { additions.as_mut_vec() }, "(n {}) ", iteration);
            additions.write_str(
                "(exec 0 (, (n $n) (m $m) )
                         (,  (exec 0 (, (line $n (axiom $x)) (line $m (axiom $x)) )
                                     (, (unifies $n $m) )
                             )
                         )
                 )"
            );
            additions
        });

    }

    /// for_each_iteration is expected to generate `(unifies $n $m)` values.
    /// 
    /// iteration here is actually done by filtering
    fn iterate_runs_multithreaded_boilerplate(&self, task : &str, forall_runs_sexpr_additions : &str, for_each_iteration : &(impl Fn(usize)->String + Sync) ) {
        let mut s = mork::space::Space::new();
        
        println!("\n{}", task);
        
        s.add_all_sexpr(self.axioms.as_bytes()).unwrap();;
        let wip_control = self.results_wip_control(task);
        s.add_all_sexpr(forall_runs_sexpr_additions.as_bytes());

        std::thread::scope(|scope_|{
            let mut threads = Vec::<(usize, std::thread::ScopedJoinHandle<()>)>::with_capacity(2001);
            let max_threads = (std::thread::available_parallelism().unwrap_or(NonZero::<usize>::new(2).unwrap()).get()).max(2) - 1 ;

            let mut i = 0;
            for iteration in 0..=100001 {
                while threads.len() == max_threads {
                    if threads[i].1.is_finished() {
                        let (l,t) = threads.swap_remove(i);
                        t.join().unwrap();
                        print!("{} JOINED {:?} [ ", task, l);

                        // this shows what other thread/iterations are still running
                        for each in &threads {
                            print!("{:?} ", each.0);
                        }
                        println!("]");
                    }
                    i = (i+1) % max_threads;
                }


                let wip_control_ref = &wip_control;
                let axioms       = &self.axioms;
                let s_inner      = s.btm.clone();
                let mut s        = mork::space::Space::new();

                s.btm = s_inner;

                threads.push((iteration, scope_.spawn(move||{
                    let mut filename  = &format!("axiom_{}.metta", iteration);
                    let mut outfile   = wip_control_ref.result_file(filename);
                    let mut outfile_  = wip_control_ref.unifications_file(filename);

                    let sexpr = for_each_iteration(iteration);
                    s.add_all_sexpr(sexpr.as_bytes());

                    s.add_all_sexpr(b"(exec 1 (, (unifies $n $m) ) (O (count (unifications $n $c) $c $m)) )");
                    s.metta_calculus(10000000);

                    s.dump_sexpr(expr!(s,"[3] unifies $ $"),      expr!(s,"[3] unifies _1 _2"),      &mut outfile);
                    s.dump_sexpr(expr!(s,"[3] unifications $ $"), expr!(s,"[3] unifications _1 _2"), &mut outfile_);

                })));

            }
            for (l,t) in threads {
                t.join();
                println!("{} JOINED {:?}", task, l);
            }
        });

        // we do this only at the end to protect against early closing of files
        wip_control.update_results();
    }


    fn run(&self) {
        let &RunInMorkSpace { whole_set, identity_assertion, iterate_left, iterate_left_right: generate_iteration, axioms, manifest, iterate_right } = self;
        let mut s = mork::space::Space::new();
        macro_rules! load_axioms {() => {  s.add_all_sexpr(self.axioms.as_bytes()).unwrap();  };}

        // try the whole set with a single thread
        if whole_set {
            self.whole_set_run();
        }
        // try only identity, where right and left hand sides are equal.
        if identity_assertion {
            self.identity_assertion_run();
        }
        // this iterates the left hand side, while querying the right hand side
        if iterate_left {
            self.iterate_left_run();
        }
        // this iterates the right hand side, while querying the right hand side
        if iterate_right {
            self.iterate_right_run();
        }
        // try iterating the left and right arguments, __vey expensive__
        if generate_iteration {
            self.iterate_left_right_run();
        }
    }
}
