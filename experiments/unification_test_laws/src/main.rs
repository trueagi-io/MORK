use mork::expr;
use rand::random;
use unification_test_laws::{unify_with_mork_unifier, convert_and_add_line_numbers_big_metta, results_to_single_file};

fn main() {

    let convert_big_metta        =  true;
    let run_mork_unifier         =  true;
    let run_in_mork_space        =  true;
    let run_prolog_unifier       =  true;
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

        // try the whole set
        {
            println!("\nWHOLE SET");
            load_axioms!();

            s.add_all_sexpr(b"(exec 0 (, (line $n (axiom $x)) 
                                         (line $m (axiom $x)) 
                                      )
                                      (O (+     (combined $n $m)  )
                                         (count (unifications $c) $c ($n $m))
                                      )
                              )").unwrap();
            s.metta_calculus(10000000);
            
            let mut w = String::new();
            // s.dump_sexpr(expr!(s,"[3] combined $ $"), expr!(s,"[3] combined _1 _2"),  unsafe { w.as_mut_vec() });
            s.dump_sexpr(expr!(s,"[2] unifications $"), expr!(s,"[2] unifications _1"),  unsafe { w.as_mut_vec() });

            println!("{}", w);

            clear_space!();        
        }

        // try only identity
        {
            println!("\nINDENTY ONLY");
            load_axioms!();

            s.add_all_sexpr(b"(exec 0 (, (line $n (axiom $x)) 
                                         (line $n (axiom $x)) 
                                      )
                                      (O (+     (combined $n $n)  )
                                         (count (unifications $c) $c ($n $m))
                                      )
                              )").unwrap();
            s.metta_calculus(10000000);

            let mut w = String::new();
            // s.dump_sexpr(expr!(s,"[3] combined $ $"), expr!(s,"[3] combined _1 _2"),  unsafe { w.as_mut_vec() });
            s.dump_sexpr(expr!(s,"[2] unifications $"), expr!(s,"[2] unifications _1"),  unsafe { w.as_mut_vec() });

            println!("{}", w);

            clear_space!();        
        }

        // try iterating the left argument
        {
            println!("\nITERATE LEFT");
            load_axioms!();

            let range = [0, 5001];
            // let range = [99975, 100001];
            // let range = [99974, 99976];

            let mut ns = String::with_capacity((range[1]-range[0]+1) * (5 + f64::log10(range[1] as f64).trunc() as usize));
            for each in range[0]..=range[1] {
                use std::io::Write;
                write!(unsafe { ns.as_mut_vec() }, "(n {}) ", each);   
            }
            s.add_all_sexpr(ns.as_bytes());
            // s.add_all_sexpr(b"(exec 0 (, (line $n (axiom $y)) ) 
            s.add_all_sexpr(b"(exec 0 (, (n $n) ) 
                                      (, 
                                          (exec 0 (, (line $n (axiom $x)) 
                                                     (line $m (axiom $x)) 
                                                  )
                                                  (, (combined $n $m)
                                                  )
                                          )
                                      )
                              )
            ");
            s.add_all_sexpr(b"(exec 1 (, (combined $n $m) ) (O (count (unifications $c) $c ($n $m))) )");



            s.metta_calculus(10000000);

            let mut w = String::new();
            // s.dump_sexpr(expr!(s,"[3] combined $ $"), expr!(s,"[3] combined _1 _2"),  unsafe { w.as_mut_vec() });
            s.dump_sexpr(expr!(s,"[2] unifications $"), expr!(s,"[2] unifications _1"),  unsafe { w.as_mut_vec() });

            println!("{}", w);

            clear_space!();        
        }

        // keep this temporarily
        return;
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
        let prolog = [env!("CARGO_MANIFEST_DIR"), "/tmp/prolog/all_results.metta"].into_iter().collect::<String>();      


        let proc = 
        &std::process::Command::new("diff")
            .args([&mork, &prolog]).output().unwrap();
        let diff =  core::str::from_utf8(&proc.stdout).unwrap();
        println!("BEGIN DIFF\n{}END DIFF", diff)
    }

}