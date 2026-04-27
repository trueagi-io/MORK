use std::fs::read_dir;
use std::num::NonZeroUsize;
use std::fmt::Write;
use std::os::unix::ffi::OsStrExt;
use std::path;

use mork_expr::{ExprZipper, apply_e};

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

    let mut outputs = Vec::with_capacity(expr_pos.len()-1);
    for each in 0..expr_pos.len() - 1 {
        outputs.push(String::new());
    }


    let range  = 0..expr_pos.len()-1;

    std::fs::create_dir_all(&results);

    std::thread::scope(|s|{

        let mut threads = Vec::new();
        
        for each in range.clone()
        {
            let expr_block = &*expr_block;
            let expr_pos = &*expr_pos;
            let results = &results;

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
            
                let (e_l_line_str, e_l_) = line_and_expr(expr_block, expr_pos, each);
                
                let mut buffer = [0_u8;1024];
                let mut ez     = mork_expr::ExprZipper::new(mork_expr::Expr{ptr : (&mut buffer).as_mut_ptr()});
                let mut stack       : Vec<(u8, u8)> = vec![];
                let mut assignments : Vec<(u8, u8)> = vec![];
                for each_other in 0..expr_pos.len() - 1 {

                    let (e_r_line_str, e_r_) = line_and_expr(expr_block, expr_pos, each_other);
                
                    ez.reset();
                    // if e_l_.unifiable(e_r_) {
                    // if e_l_.unify(e_r_, &mut ez).is_ok() {
                    if 'inlined : {
                        let this = e_l_;
                        let other = e_r_;
                        // let o: &mut ExprZipper = &mut ez;
                        let mut s = vec![(mork_expr::ExprEnv::new(0, this), mork_expr::ExprEnv::new(1, other))];

                        match mork_expr::unify(s) {
                            Ok(bindings) => {
                                let mut void   = std::io::sink();
                                let mut snk    = mork_expr::item_sink(&mut void);
                                let mut cycled = std::collections::BTreeMap::<(u8, u8), u8>::new();
                                stack.clear();
                                assignments.clear();
                                apply_e(0, 0, 0, this, &bindings, &mut std::pin::pin!(snk), &mut cycled, &mut stack, &mut assignments);

                                // the unify __function__ does not do full occurs check, this enforces it __after__ apply, making the unify __method__ cycle safe
                                if !cycled.is_empty() {
                                    break 'inlined Err(mork_expr::UnificationFailure::Occurs(cycled.first_key_value().unwrap().0.clone(), 
                                        /* admittedly, this value is here only to satisfy the signature, the previous code assumed that errors can't happen past this point */ 
                                        mork_expr::ExprEnv::new(1, other))
                                    );
                                }

                                Ok(())
                            }
                            Err(f) => Err(f)
                        }
                    }.is_ok() {
                        unsafe { writeln!(out_string,"(unifies {} {})", core::str::from_utf8_unchecked(e_l_line_str), core::str::from_utf8_unchecked(e_r_line_str)) };
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

                out_string
            })));

            // we keep the number of live threads bounded
            let mut choice = 0;
            while threads.len() >= threads_max {
                if threads[choice].1.is_finished() {
                    let (n, t) = threads.remove(choice);
                    let unifications = t.join().unwrap();
                    outputs[n] = unifications;
                    println!("JOINED : {}", n);
                    break;
                }
                choice = (choice+1) % threads_max; 
            }
        }

        // close off the remaining threads
        for (n,t) in threads {
            let unifications = t.join().unwrap();
            outputs[n] = unifications;
            println!("JOINED : {}", n);
        }
    });
}




pub fn results_to_single_file() -> std::io::Result<()> {
    use std::{io::{Read, Write}};
    let mut collect = Vec::new();

    let manefest = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));

    let tmp = manefest.join("tmp");
    
    for unifier in ["mork", "prolog"] {
        let dir_path = tmp.join(unifier);
        let results_dir = dir_path.join("results");
        for each in std::fs::read_dir(results_dir)? {
            let file = each.unwrap();
            let f_name = file.file_name();
            let name = f_name.to_str().unwrap();
            assert!(name.starts_with("axiom_"));
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

        let out_path = dir_path.join("all_results.metta");
        let mut out_file = std::fs::File::create(out_path).unwrap();
        for [l,r] in &collect {
            write!(out_file, "(unifies {} {})\n", l,r).unwrap()
        }

        collect.clear();
        out_file.flush().unwrap();

    }
    Ok(())
}
