use std::io::Read;
use std::{fs::read_dir, io::Write};
use std::num::NonZeroUsize;
use std::os::unix::ffi::OsStrExt;
use std::path;

use mork_expr::{ExprZipper, Unifiable, apply_e};

// Here we generate two files that are the big.metta files but with line numbers.
// it makes one mm2 file, and one prolog file at the same time.
pub fn convert_and_add_line_numbers_big_metta() {
    use std::{io::{Read, Write}};

    let mut in_buffer = Vec::new();

    let workspace = std::path::PathBuf::from(env!("CARGO_WORKSPACE_DIR"));
    let path = workspace.join("kernel/resources/big.metta");
    let mut f = std::fs::File::open(path).unwrap();
    
    
    f.read_to_end(&mut in_buffer);
    drop(f);

    let mut i = 0;
    let mut line = 0;
    let mut last_newline_pos = 0;

    let mut out_buffer = Vec::new();
    let mut metta_out_buffer = Vec::new();

    out_buffer.extend_from_slice(b"line(");
    write!(out_buffer,"{},",line);
    metta_out_buffer.extend_from_slice(b"(line ");
    write!(metta_out_buffer,"{} ",line);

    let mut line_byte_index = 0;
    let mut metta_last_newline_pos = 0;
    loop {
        if i == in_buffer.len() {break;}

        match in_buffer[i] {
            b'(' => {
                out_buffer.push(b'\'');
                let mut j = i+1;
                while in_buffer[j] != b' ' {
                    if let b'\\' = in_buffer[j] {
                        out_buffer.push(b'\\');
                    };
                    out_buffer.push(in_buffer[j]);
                    j += 1;
                }
                out_buffer.extend_from_slice(b"\'(");
                i=j+1;
            },
            b' ' => {
                out_buffer.push(b',');
                i+=1;
            }
            b'$' => {
                // to supress singleton variable warnings in prolog, we append "_0" to the variables
                out_buffer.extend_from_slice(b"_0");

                out_buffer.push(in_buffer[i+1].to_ascii_uppercase());
                i+=2;
            }
            b'\n' => {
                out_buffer.extend_from_slice(b").\n");
                last_newline_pos = out_buffer.len();
                

                metta_out_buffer.extend_from_slice(&in_buffer[line_byte_index..i]);
                metta_out_buffer.extend_from_slice(b")\n");
                metta_last_newline_pos = metta_out_buffer.len();
                
                i+=1;
                line+=1;
                line_byte_index = i+1;

                out_buffer.extend_from_slice(b"line(");
                write!(out_buffer,"{},",line);
                write!(metta_out_buffer,"(line {} (", line);
            }
            b')' => {
                out_buffer.push(b')');
                i+=1;
            }
            _ => {
                out_buffer.push(b'\'');
                let mut j = i+1;
                while !matches!(in_buffer[j], b' ' | b')') {
                    j += 1;
                }
                out_buffer.extend_from_slice(&in_buffer[i..j]);
                out_buffer.push(b'\'');         
                i=j;
            }
        }
    }

    out_buffer.truncate(last_newline_pos);
    metta_out_buffer.truncate(metta_last_newline_pos);

    let manifest = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let tmp_path = manifest.join("tmp");

    std::fs::create_dir_all(&tmp_path).unwrap();

    let mut out_file = std::fs::File::create(tmp_path.join("big_.prolog")).unwrap();
    out_file.write_all(&out_buffer).unwrap();
    drop(out_file);

    let mut metta_out_file = std::fs::File::create(tmp_path.join("big_.metta")).unwrap();
    metta_out_file.write_all(&metta_out_buffer).unwrap();
    drop(metta_out_file);
}


pub fn unify_with_mork_unifier() {
    let mut s = mork::space::Space::new();
    
    let manifest = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let results  = manifest.join("tmp/mork/results");

    std::fs::create_dir_all(&results);

    let axioms = std::fs::read_to_string(manifest.join("tmp/big_.metta")).unwrap();

    // this needs to be generous in size.
    let mut expr_block = Vec::with_capacity(axioms.len()*2);
    unsafe { expr_block.set_len(expr_block.capacity()) };
    let mut offset   = 0;
    let mut expr_pos = Vec::new();
    
    for each in axioms.split('\n') {
        if each.len() == 0 {break;}
        expr_pos.push(offset);
        let e = s.parse_sexpr(each.as_bytes(), (&mut expr_block[offset..]).as_mut_ptr()).unwrap();
        offset += e.1;
    }
    expr_pos.push(offset);

    let threads_max = std::thread::available_parallelism().unwrap_or(unsafe { NonZeroUsize::new_unchecked(1) }).get();

    let range  = 0..expr_pos.len()-1;

    std::fs::create_dir_all(&results);

    let signal = std::sync::atomic::AtomicBool::new(true);
    std::thread::scope(|s|{
        let (tx,rx) = std::sync::mpsc::channel::<std::cmp::Reverse<(usize, String)>>();
        let mut cycles_file = std::fs::File::create(manifest.join("tmp/cycles.mm2")).unwrap();

        // this thread is collecting found cycles.
        // unlike the later code, it only constructs one file.
        let signal = &signal;
        let cycles_collection = s.spawn(move || {
            let mut queue = std::collections::binary_heap::BinaryHeap::new();
            let mut next = 0;
            loop {
                let r = rx.try_recv();
                if let Ok(r) = r {
                    queue.push(r);
                } 
                if let Some(std::cmp::Reverse((n,_))) = queue.peek() && n == &next {
                    next += 1;
                    let top = queue.pop().unwrap();
                    cycles_file.write_all(top.0.1.as_bytes());
                    cycles_file.flush();
                    continue;
                }
                if !signal.load(std::sync::atomic::Ordering::Acquire) && queue.is_empty() { break }
            }
            cycles_file.flush();
        });

        let mut threads = Vec::new();
        
        for each in range.clone()
        {
            let expr_block = &*expr_block;
            let expr_pos   = &*expr_pos;
            let results    = &results;
            let tx_clone   = tx.clone();

            fn line_and_expr<'a, 'b>(expr_block: &'a[u8], expr_pos: &[usize], nth : usize) -> (&'a [u8],mork_expr::Expr) {
                // (line 0 ....)
                // [3]<4>line<n>...
                // 6 bytes down
                const HEADER : &[u8]= {
                    &[ mork_expr::item_byte(mork_expr::Tag::Arity(3))
                    ,  mork_expr::item_byte(mork_expr::Tag::SymbolSize(4))
                    ,  b'l'
                    ,  b'i'
                    ,  b'n'
                    ,  b'e'
                    ]
                };

                const NUM_TAG_POS : usize = HEADER.len();
                const NUM_POS     : usize = NUM_TAG_POS+1;

                let e      = mork_expr::Expr{ ptr : (&expr_block[expr_pos[nth]..expr_pos[nth+1]]).as_ptr().cast_mut() };
                let e_span = unsafe { e.span().as_ref() }.unwrap();
                
                let mork_expr::Tag::SymbolSize(n_l) =  mork_expr::byte_item(e_span[NUM_TAG_POS]) else {panic!()};
                
                let e_line_num = &e_span[NUM_POS..NUM_POS+n_l as usize];    
                let e_         = mork_expr::Expr{ ptr : unsafe { e.ptr.add(NUM_POS+n_l as usize) } };

                (e_line_num, e_)
            }
            threads.push((each, s.spawn(move ||{
                let mut out_string = String::with_capacity(32);
                let mut cycles_out_string = String::with_capacity(32);
            
                let (e_l_line_str, e_l_) = line_and_expr(expr_block, expr_pos, each);
                

                let mut stack       : Vec<(u8, u8)>                                 = Vec::new();
                let mut assignments : Vec<(u8, u8)>                                 = Vec::new();
                let mut expr_env    : Vec<(mork_expr::ExprEnv, mork_expr::ExprEnv)> = Vec::new();
                for each_other in 0..expr_pos.len() - 1 {
                    use std::fmt::Write;
                    let (e_r_line_str, e_r_) = line_and_expr(expr_block, expr_pos, each_other);
                    match mork_expr::unifiable_reuse_state(e_l_, e_r_, &mut expr_env, &mut stack, &mut assignments) {
                        Unifiable::Unifies => { unsafe { writeln!(out_string,"(unifies {} {})", core::str::from_utf8_unchecked(e_l_line_str), core::str::from_utf8_unchecked(e_r_line_str)) }; }
                        Unifiable::Cycles  => { unsafe { writeln!(cycles_out_string,"(cycles {} {})", core::str::from_utf8_unchecked(e_l_line_str), core::str::from_utf8_unchecked(e_r_line_str)) }; }
                         _ => {}
                    }
                 }

                const FILE_NAME_PREFIX : &[u8] = b"axiom_";
                const FILE_EXTENSION   : &[u8] = b".metta";

                let     dir_path_bytes = results.as_os_str().as_bytes();
                let mut path           = [0;300];
                let mut path_len       = 0;

                for each in [dir_path_bytes, b"/", FILE_NAME_PREFIX, e_l_line_str, FILE_EXTENSION] {
                    path[path_len..path_len+each.len()].copy_from_slice(each);
                    path_len += each.len();
                }

                let mut out_file = std::fs::File::create(core::str::from_utf8(&path[0..path_len]).unwrap()).unwrap();

                std::io::Write::write_all(&mut out_file,out_string.as_bytes()).unwrap();

                tx_clone.send(std::cmp::Reverse((each, cycles_out_string)));

            })));

            // we keep the number of live threads bounded
            let mut choice = 0;
            while threads.len() >= threads_max {
                if threads[choice].1.is_finished() {
                    let (n, t) = threads.remove(choice);
                    let _ = t.join().unwrap();
                    println!("JOINED : {}", n);
                    break;
                }
                choice = (choice+1) % threads_max; 
            }
        }

        // close off the remaining threads
        for (n,t) in threads {
            let _ = t.join().unwrap();
            println!("JOINED : {}", n);
        }
        signal.store(false, std::sync::atomic::Ordering::Release);
        cycles_collection.join();
    });
}



/// collectes the results of the unifications into a single file for each tmp result folder.
pub fn results_to_single_file(tmp_folders : &[&str]) -> std::io::Result<()> {
    use std::{io::{Read, Write}};
    let mut collect = Vec::new();

    let manefest = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));

    let tmp = manefest.join("tmp");

    for unifier in tmp_folders {
        let dir_path = tmp.join(unifier);
        let results_dir = dir_path.join("results");
        for each in std::fs::read_dir(results_dir)? {
            let file = each.unwrap();
            let f_name = file.file_name();
            let name = f_name.to_str().unwrap();
            assert!(name.starts_with("axiom_") || name.starts_with("axioms_"));
            assert!(name.ends_with(".metta"));

            let contents = std::fs::read_to_string(file.path()).unwrap();

            for each in  contents.split_terminator('\n') {
                let strip_parens = &each[1..each.len()-1];
                let mut tokens = strip_parens.split_ascii_whitespace();
                let Some("unifies") = tokens.next() else {panic!()};
                let left  : usize = tokens.next().unwrap().parse::<usize>().unwrap();
                let right : usize = tokens.next().unwrap().parse::<usize>().unwrap();
                collect.push([left,right]);
            };
        }

        collect.sort_by(|[l0,l1],[r0,r1]| l0.cmp(r0).then(l1.cmp(r1)));
        collect.dedup();

        let out_path = dir_path.join("all_results.metta");
        println!("!! {:?}", out_path);
        
        let mut out_file = std::fs::File::create(out_path).unwrap();
        for [l,r] in &collect {
            write!(out_file, "(unifies {} {})\n", l,r).unwrap()
        }



        collect.push([usize::MAX,usize::MAX]);
        let out_path_counts = dir_path.join("all_results_counts.metta");
        let mut out_file_counts = std::fs::File::create(out_path_counts).unwrap();
        collect.iter().fold((None, 0), |(cur,count),&[line_left,line_right]| {
            if Some(line_left) == cur {
                (cur, count+1)
            } 
            else {
                if let Some(line) = cur {
                    write!(out_file_counts, "(unifies-count {} {})\n", line,count).unwrap();
                } 
                (Some(line_left), 1)
            }
        });
        collect.pop(/* remove dummy */);

        collect.clear();
        out_file.flush().unwrap();

    }
    Ok(())
}




/// this a slightly modified version of `esults_to_single_file`, but for the cycles instead of unifications.
pub fn cycles_to_single_file(tmp_folders : &[&str]) -> std::io::Result<()> {
    use std::{io::{Read, Write}};
    let mut collect = Vec::new();

    let manefest = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));

    let tmp = manefest.join("tmp");

    for unifier in tmp_folders {
        let dir_path = tmp.join(unifier);
        let results_dir = dir_path.join("results");
        for each in std::fs::read_dir(results_dir)? {
            let file = each.unwrap();
            let f_name = file.file_name();
            let name = f_name.to_str().unwrap();
            assert!(name.starts_with("axiom_") || name.starts_with("axioms_"));
            assert!(name.ends_with(".metta"));

            let contents = std::fs::read_to_string(file.path()).unwrap();

            for each in  contents.split_terminator('\n') {
                let strip_parens = &each[1..each.len()-1];
                let mut tokens = strip_parens.split_ascii_whitespace();
                let Some("cycles") = tokens.next() else {panic!()};
                let left  : usize = tokens.next().unwrap().parse::<usize>().unwrap();
                let right : usize = tokens.next().unwrap().parse::<usize>().unwrap();
                collect.push([left,right]);
            };
        }

        collect.sort_by(|[l0,l1],[r0,r1]| l0.cmp(r0).then(l1.cmp(r1)));
        collect.dedup();

        let out_path = dir_path.join("all_cycles.metta");
        println!("!! {:?}", out_path);
        
        let mut out_file = std::fs::File::create(out_path).unwrap();
        for [l,r] in &collect {
            write!(out_file, "(cycles {} {})\n", l,r).unwrap()
        }


        collect.push([usize::MAX,usize::MAX]);
        let out_path_counts = dir_path.join("all_cycles_counts.metta");
        let mut out_file_counts = std::fs::File::create(out_path_counts).unwrap();
        collect.iter().fold((None, 0), |(cur,count),&[line_left,line_right]| {
            if Some(line_left) == cur {
                (cur, count+1)
            } 
            else {
                if let Some(line) = cur {
                    write!(out_file_counts, "(cycles-count {} {})\n", line,count).unwrap();
                } 
                (Some(line_left), 1)
            }
        });
        collect.pop(/* remove dummy */);

        collect.clear();
        out_file.flush().unwrap();

    }
    Ok(())
}




#[test]
fn hit_cycles() {
    let mut s = mork::space::Space::new();
    let manefest = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));

    let mut buf = String::new();
    let big_metta = std::fs::File::open(manefest.join("tmp/big_.metta")).unwrap().read_to_string(&mut buf);

    s.add_all_sexpr(buf.as_bytes());

    s.add_all_sexpr(b"(exec 0 (, (line 1 $a) (line $m $a)) (, (unifies 1 $m)))");
    s.metta_calculus(1000000000);



}