use std::num::NonZero;

use mork::expr;
use rand::random;
use unification_test_laws::{unify_with_mork_unifier, convert_and_add_line_numbers_big_metta, results_to_single_file};
// https://github.com/trueagi-io/MORK/blob/old_main/benchmarks/logic-query/src/main.rs
fn main() {

    let convert_big_metta        = !true;
    let run_in_mork_space        =  true;
    let generate_iteration       =  true; // this takes a __very__  long time to compute (on my computer, 20 saturated threads, ~18 hours)
    let run_mork_unifier         = !true;
    let run_prolog_unifier       = !true;
    let collect_results_and_diff =  true;

    // prep big.metta to enumerate axioms
    if convert_big_metta {
        convert_and_add_line_numbers_big_metta();
    }


    let mut s = mork::space::Space::new();
    if run_in_mork_space {
        let mut s = mork::space::Space::new();
        
    
        let manifest = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        // let results  = manifest.join("tmp/mork_space/results");
        // std::fs::create_dir_all(&results);

        let axioms = std::fs::read_to_string(manifest.join("tmp/big_.metta")).unwrap();


        macro_rules! clear_space {() => {  
                s.btm = pathmap::PathMap::new();
                // s.add_all_sexpr(b"(exec 0   (, $x)   (O (- $x) ) )");
            };
        }
        macro_rules! load_axioms {() => {  s.add_all_sexpr(axioms.as_bytes()).unwrap();  };}

        // // try the whole set
        // {
        //     println!("\nWHOLE SET");
        //     load_axioms!();

        //     s.add_all_sexpr(b"(exec 0 (, (line $n (axiom $x)) 
        //                                  (line $m (axiom $x)) 
        //                               )
        //                               (O (+     (unifies $n $m)  )
        //                                  (count (unifications $c) $c ($n $m))
        //                               )
        //                       )").unwrap();
        //     s.metta_calculus(10000000);
            
        //     let mut w = String::new();
        //     // s.dump_sexpr(expr!(s,"[3] unifies $ $"), expr!(s,"[3] unifies _1 _2"),  unsafe { w.as_mut_vec() });
        //     s.dump_sexpr(expr!(s,"[2] unifications $"), expr!(s,"[2] unifications _1"),  unsafe { w.as_mut_vec() });

        //     println!("{}", w);

        //     clear_space!();        
        // }

        // try only identity
        {
            println!("\nINDENTY ONLY");
            load_axioms!();

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

            clear_space!();        
        }

        // try iterating the left argument
        {
            println!("\nITERATE LEFT");

            let outdir = manifest.join("tmp/iterated_left");
            let tmp_outdir = manifest.join("tmp/iterated_left_WIP");
            let results = tmp_outdir.join("results");
            let unifications = tmp_outdir.join("unifications");
            std::fs::create_dir_all(&results);
            std::fs::create_dir_all(&unifications);

            load_axioms!();
            

            std::thread::scope(|scope_|{
                let mut threads = Vec::<((usize,usize), std::thread::ScopedJoinHandle<()>)>::with_capacity(2001);
                let max_threads = (std::thread::available_parallelism().unwrap_or(NonZero::<usize>::new(2).unwrap()).get()).max(2) - 1 ;

                let overlap = 1;
                
                let mut i = 0;
                for iteration in 0..=100001+1 {
                    while threads.len() == max_threads {
                        if threads[i].1.is_finished() {
                            let (l,t) = threads.swap_remove(i);
                            t.join().unwrap();
                            print!("ITERATED_LEFT JOINED {:?} [ ", l);
                            for each in &threads {
                                print!("{:?} ", each.0);
                            }
                            println!("]");
                        }
                        i = (i+1) % max_threads;
                    }
                
                    let results      = &results;
                    let unifications = &unifications;
                    let axioms       = &axioms;
                    let s_inner      = s.btm.clone();
                    let mut s        = mork::space::Space::new();
                
                    s.btm = s_inner;
                
                    threads.push(((iteration, iteration+1), scope_.spawn(move||{                        
                        let mut outfile  = std::fs::File::create(results.join(format!("axioms_{}-{}.metta", iteration, iteration+overlap))).unwrap();
                        let mut outfile_ = std::fs::File::create(unifications.join(format!("axioms_{}-{}.metta", iteration, iteration+overlap))).unwrap();
                        
                        // load_axioms!();
                        let range = [iteration, iteration+overlap];
        
                        let mut ns = String::with_capacity(10);
                        for each in range[0]..=range[1] {
                            use std::io::Write;
                            write!(unsafe { ns.as_mut_vec() }, "(n {}) ", each);   
                        }
                        s.add_all_sexpr(ns.as_bytes());
                        s.add_all_sexpr(b"(exec 0 (, (n $n) ) 
                                                  (, 
                                                      (exec 0 (, (line $n (axiom $x)) 
                                                                 (line $m (axiom $x)) 
                                                              )
                                                              (, (unifies $n $m)
                                                              )
                                                      )
                                                  )
                                          )
                        ");
                        s.add_all_sexpr(b"(exec 1 (, (unifies $n $m) ) (O (count (unifications $c) $c ($n $m))) )");
        
        
                        s.metta_calculus(10000000);
        
                        s.dump_sexpr(expr!(s,"[3] unifies $ $"), expr!(s,"[3] unifies _1 _2"),  &mut outfile);
                        s.dump_sexpr(expr!(s,"[2] unifications $"), expr!(s,"[2] unifications _1"), &mut outfile_ );
        
                    })));
                    
                    }

                    for (l,t) in threads {
                        t.join();
                        println!("ITERATED_LEFT JOINED {:?}", l);
                    }
                });
                clear_space!();        
                // we do this only at the end to protect against early closing of files

                std::fs::rename(tmp_outdir, outdir);
return;
   
        }

        // try iterating the left and right arguments
        if generate_iteration {
            load_axioms!();

            println!("\nITERATE LEFT AND RIGHT");
            
            let outdir = manifest.join("tmp/iterated_left_right");
            let tmp_outdir = manifest.join("tmp/iterated_left_right_WIP");
            let results = tmp_outdir.join("results");
            let unifications = tmp_outdir.join("unifications");
            std::fs::create_dir_all(&results);
            std::fs::create_dir_all(&unifications);

            let mut ms = String::new();
            let range_r = [0, 100001];
            for each_r in range_r[0]..=range_r[1] {
                use std::io::Write;
                write!(unsafe { ms.as_mut_vec() }, "(m {}) ", each_r);
            }
            s.add_all_sexpr(ms.as_bytes());

            std::thread::scope(|scope_|{
                let mut threads = Vec::<((usize,usize), std::thread::ScopedJoinHandle<()>)>::with_capacity(2001);
                let max_threads = (std::thread::available_parallelism().unwrap_or(NonZero::<usize>::new(2).unwrap()).get()).max(2) - 1 ;

                // this dictates how many lines will be processed per thread, the execs are still done idividually.
                let factor = 1;

                let mut i = 0;
                for iteration in 0..=(100001/factor)+1 {
                    while threads.len() == max_threads {
                        if threads[i].1.is_finished() {
                            let (l,t) = threads.swap_remove(i);
                            t.join().unwrap();
                            print!("ITERATED_LEFT_RIGHT JOINED {:?} [ ", l);
                            for each in &threads {
                                print!("{:?} ", each.0);
                            }
                            println!("]");
                        }
                        i = (i+1) % max_threads;
                    }

                    let results      = &results;
                    let unifications = &unifications;
                    let axioms       = &axioms;
                    let s_inner      = s.btm.clone();
                    let mut s        = mork::space::Space::new();

                    s.btm = s_inner;

                    threads.push(((iteration*factor, (iteration+1)*factor-1), scope_.spawn(move||{
                    
                    
                        let mut outfile  = std::fs::File::create(results.join(format!("axioms_{}-{}.metta", iteration*factor, (iteration+1)*factor - 1))).unwrap();
                        let mut outfile_ = std::fs::File::create(unifications.join(format!("axioms_{}-{}.metta", iteration*factor, (iteration+1)*factor - 1))).unwrap();
                    
                        let mut ns = String::with_capacity(factor * 10);

                        for i in 0..factor {
                            use std::io::Write;
                            let v = unsafe { ns.as_mut_vec() };
                            write!(v,"(n {})\n", (iteration*factor)+i);

                        }
                        s.add_all_sexpr(ns.as_bytes());
                        s.add_all_sexpr(b"(exec 0 (, (n $n) (m $m) ) 
                                                  (, 
                                                      (exec 0 (, (line $n (axiom $x)) 
                                                                 (line $m (axiom $x)) 
                                                              )
                                                              (, (unifies $n $m)
                                                              )
                                                      )
                                                  )
                                          )");
                        s.add_all_sexpr(b"(exec 1 (, (unifies $n $m) ) (O (count (unifications $n $c) $c $m)) )");
                    
                    
                    
                        s.metta_calculus(10000000);
                    
                        s.dump_sexpr(expr!(s,"[3] unifies $ $"), expr!(s,"[3] unifies _1 _2"),  &mut outfile);
                        s.dump_sexpr(expr!(s,"[3] unifications $ $"), expr!(s,"[3] unifications _1 _2"), &mut outfile_);
                    
                    })));

                }
                for (l,t) in threads {
                    t.join();
                    println!("ITERATED_LEFT_RIGHT JOINED {:?}", l);
                }
            });

            // we do this only at the end to protect against early closing of files
            std::fs::rename(tmp_outdir, outdir);
        
            clear_space!();
        }



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
        results_to_single_file();

        let mork   = [env!("CARGO_MANIFEST_DIR"), "/tmp/mork/all_results.metta"].into_iter().collect::<String>();      
        let mork_iterated_left_right   = [env!("CARGO_MANIFEST_DIR"), "/tmp/iterated_left_right/all_results.metta"].into_iter().collect::<String>();      
        let prolog = [env!("CARGO_MANIFEST_DIR"), "/tmp/prolog/all_results.metta"].into_iter().collect::<String>();      


        if let Ok(proc) = &std::process::Command::new("diff").args([&mork, &prolog]).output()
        {
            let diff =  core::str::from_utf8(&proc.stdout).unwrap();
            println!("\nMORK-PROLOG\nBEGIN DIFF\n{}END DIFF", diff);
        }

        if let Ok(proc) = &std::process::Command::new("diff").args([&mork, &mork_iterated_left_right]).output()
        {
            let diff =  core::str::from_utf8(&proc.stdout).unwrap();
            println!("\nMORK-MORK_SPACE_ITERATED_LEFT_RIGHT\nBEGIN DIFF\n{}END DIFF", diff);
        }


    }
}


