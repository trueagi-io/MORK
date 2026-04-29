use unification_test_laws::{unify_with_mork_unifier, convert_and_add_line_numbers_big_metta, results_to_single_file};

fn main() {

    let convert_big_metta        = !true;
    let run_mork_unifier         =  true;
    let run_prolog_unifier       = !true;
    let collect_results_and_diff =  true;

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