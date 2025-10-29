
#[inline]fn id<T>(t:T)->T {t}

mod data;
mod relational_algebra {
    use std::{io::Write, sync::atomic::AtomicU64};

    use mork::space::{self, Space};
    use pathmap::{morphisms::Catamorphism, zipper::{ZipperIteration, ZipperMoving}};

    use crate::utils;


    const TRIPLES : &str =
"
(monster orc)
(monster ogre)
(monster ghost)
(monster slime)
(monster dragon)
(monster centaur)
(monster skeleton)

(animal cat)
(animal dog)
(animal horse)
(animal human)
(animal mouse)

((feet 2) human)
((feet 4) horse)
((feet 4) cat)
((feet 4) dog)
((feet 4) mouse)
((feet 0) slime)
((feet 2) ogre)
((feet 2) skeleton)
((feet 2) orc)
((feet 4) centaur)

";

const BASIC_UNION : &str =
"
(($l \\/ $r) $l)
(($l \\/ $r) $r)
(exec ((monster \\/ animal) 0) (, ((monster \\/ animal) $t) 
                                  ($t $x)
                               )
                               (, ((monster \\/ animal) $x)
                               )
)
";

const BASIC_UNION_2 : &str = "
(exec ((monster \\/ animal) 0) (, (monster $x)
                               )
                               (, ((monster \\/ animal) $x)
                               )
)
(exec ((monster \\/ animal) 0) (, (animal $x)
                               )
                               (, ((monster \\/ animal) $x)
                                  ((monster \\/ animal) (hey $x))
                               )
)
";

const BASIC_INTERSECTION : &str =
"
(exec (((feet _) /\\ animal) 0)  (, ((feet $f) $x) 
                                    (animal $x)
                                 )
                                 (, (((feet $f) /\\ animal) $x)
                                 )
)
";
const BASIC_DIFFERENCE : &str =
"
(exec (((feet 2) \\ monster) 0) (, ((feet 2) $x) (monster $y)
                                )
                                (O (+ (((feet 2) \\ monster) $x))
                                   (- (((feet 2) \\ monster) $y))
                                )
)
";
const BASIC_CARTESIAN_PRODUCT : &str =
"
(exec ((monster x animal) 0) (, (monster $x) 
                                (animal $y)
                             )
                             (, ((monster x animal) ($x x $y))
                             )
)
";
const BASIC_PROJECTION : &str =
"
(exec (proj_out <- (monster x animal)) (, ((monster x animal) ($x x $y)) 
                                       )
                                       (, (proj_out (animal $y))
                                       )
)
";
const BASIC_RENAME : &str =
"
(exec (enemy <- monster) (, (monster $x) 
                         )
                         (, (enemy $x)
                         )
)
";

const WIKIPEDIA_EXAMPLE : &str =
"
; wikipedia example

(WIKI (, Name EmpId DeptName) (, Harry   3415 Finance))
(WIKI (, Name EmpId DeptName) (, Sally   2241 Sales  ))
(WIKI (, Name EmpId DeptName) (, George  3401 Finance))
(WIKI (, Name EmpId DeptName) (, Harriet 2202 Sales  ))
(WIKI (, Name EmpId DeptName) (, Tim     2241 Finance))

(WIKI (, DeptName Manager) (, Sales      Harriet))
(WIKI (, DeptName Manager) (, Production Charles))
";

fn code_concat_exec_clear_leading_pred_all<W : Write>(mut s : &mut W, pred : &[u8])->std::io::Result<()>{
    s.write_all(b"\n")?;
    for each in 1..MAX_ARITY_GEN {
        code_concat_exec_clear_leading_pred(s, pred, each)?;
    }
    s.write_all(b"\n")
}
fn code_concat_exec_clear_leading_pred_many<W : Write>(mut s : &mut W, pred_arity : &[(&[u8], u8)])->std::io::Result<()>{
    for &(pred, arity) in  pred_arity {
        code_concat_exec_clear_leading_pred(s, pred, arity)?;
    }
    Ok(())
}
fn code_concat_exec_clear_leading_pred<W : Write>(mut s : &mut W, pred : &[u8], total_arity : u8)->std::io::Result<()>{
    core::assert!(0 < total_arity && total_arity <= MAX_ARITY);
    let remaining = total_arity - 1;

    write_all_many(s,&[b"(exec () \n  (, (", &pred])?;
    for each in 0..remaining {
        if each !=0 && each%12 == 0 {
            s.write_all(b"\n       ")?;
        }
        write_all_many(s, &[b" $", &ascii_dec(each)])?;
    }
    
    write_all_many(s,&[b"\n     )\n  )\n  (O (- ( ", &pred])?;
    
    for each in 0..remaining {
        if each%12 == 0 {
            s.write_all(b"\n         ")?;
        }
        write_all_many(s, &[b" $", &ascii_dec(each)])?;
    }
    
    s.write_all(b"\n        )\n  )  )\n)\n")
}


fn write_all_many<W : Write>(mut s : &mut W, slices : &[&dyn AsRef<[u8]>])->std::io::Result<()> {
    for each in slices {
        s.write_all(each.as_ref())?;
    }
    Ok(())
}



fn ascii_dec(u : u8)->[u8;3]{
    [b'0'+u/100, b'0'+(u%100)/10, b'0'+u%10]
}
fn code_concat_project_col<W : Write>(mut s : &mut W)->std::io::Result<()> {
    s.write(b"\n")?;



    for each in 0..MAX_ARITY_GEN {
        write_all_many(s, &[
            b"\n(column-index ",
            &ascii_dec(each),
            b")\n",
        ])?;

    }
    s.write(b"\n")?;

    for tup in 0..MAX_ARITY_GEN {
        for col in 0..tup {
            write_all_many(s
                , &[b"(col ", &ascii_dec(col), b"\n  (,",]
            );
            for i in 0..tup {
                if i%12 == 0 && i != 0 {
                   s.write_all(b"\n    ")?;
                }
                write_all_many(s, &[b" $", &ascii_dec(i)])?;
            }
            write_all_many(s, &[b"\n  )\n  $",&ascii_dec(col),b"\n)\n",]);
        } 
    }
    s.flush()

}

const MAX_ARITY : u8 = 63;
const MAX_ARITY_GEN : u8 = {
    let gen_ = 63;
    core::assert!(gen_ <= MAX_ARITY);
    gen_
};
fn code_concat_tuple_concat<W : Write>(mut s : &mut W)->std::io::Result<()> {
    s.write_all(b"\n")?;
    for prod_arity in 0..MAX_ARITY_GEN /* including the , */ {
        for left_arity in 0..prod_arity {
            let right_arity = prod_arity-left_arity;

            let vars =|s:&mut W,arity_side,side_literal| {
                for each in 0..arity_side {
                    if each%12 == 0 && each != 0 {
                       s.write_all(b"\n    ")?;
                    }
                    write_all_many(s,
                        &[ b" $", &[side_literal], &ascii_dec(each)]
                    )?;
                }
                std::io::Result::Ok(())
            };

            // product
            s.write_all(b"(tuple-concat\n  (,")?;
            vars(s,left_arity,b'l')?;
            vars(s,right_arity, b'r')?;

            // left
            s.write_all(b"\n  )\n  (,")?;
            vars(s,left_arity, b'l')?;

            // right
            s.write_all(b"\n  )\n  (,")?;
            vars(s,right_arity, b'r')?;
            s.write_all(b")\n)\n")?;
        }
    }
    s.flush()
}

const WIKIPEDIA_CONCAT : &str = 
"
(exec (wikipedia tuple-concat) (, (WIKI $attr_l $val_l)
                                  (WIKI $attr_r $val_r)  
                                  (tuple-concat $attr_prod $attr_l $attr_r)
                                  (tuple-concat $val_prod  $val_l  $val_r )
                               )
                               (, (WIKI-CONCAT $attr_prod $val_prod)
                               )
)
";

const WIKIPEDIA_PROJECT : &str = "
(exec (wikipedia_project) (, (WIKI $attrs $vals)
                             
                             (col $Name $attrs Name)
                             (col $Name $vals  $name)
                             
                             (col $DeptName $attrs DeptName)
                             (col $DeptName $vals  $dept_name)

                          ) 
                          (, (WIKI-PROJ (, $Name $Dept) (, $name $dept_name))
                          )
)
";

const CLEAR : &str = 
"
(exec () (, $x
         )
         (O (- $x)
         )
)
";

    #[test]
    fn test(){
        let mut s = Space::new();

        for each in TRIPLES.split('\n') {
            s.add_sexpr(each.as_bytes(), mork::expr!(s,"$"), mork::expr!(s,"_1"));
        }
        println!();

        // s.add_sexpr(BASIC_UNION            .as_bytes(), mork::expr!(s,"$"), mork::expr!(s,"$"));
        // s.add_sexpr(BASIC_UNION_2          .as_bytes(), mork::expr!(s,"$"), mork::expr!(s,"$"));
        // s.add_sexpr(BASIC_INTERSECTION     .as_bytes(), mork::expr!(s,"$"), mork::expr!(s,"$"));
        // s.add_sexpr(BASIC_DIFFERENCE       .as_bytes(), mork::expr!(s,"$"), mork::expr!(s,"$"));
        // s.add_sexpr(BASIC_CARTESIAN_PRODUCT.as_bytes(), mork::expr!(s,"$"), mork::expr!(s,"$"));
        // s.add_sexpr(BASIC_PROJECTION       .as_bytes(), mork::expr!(s,"$"), mork::expr!(s,"$"));
        // s.add_sexpr(BASIC_RENAME           .as_bytes(), mork::expr!(s,"$"), mork::expr!(s,"$"));
        
        s.metta_calculus(10);
        

        println!();
        let mut tup_lenses = Vec::new();
        code_concat_project_col(&mut tup_lenses);
        code_concat_tuple_concat(&mut tup_lenses);
        s.add_sexpr(&tup_lenses, mork::expr!(s,"$"), mork::expr!(s,"$"));

        s.add_sexpr(WIKIPEDIA_EXAMPLE.as_bytes(), mork::expr!(s,"$"), mork::expr!(s,"$"));
        s.add_sexpr(WIKIPEDIA_CONCAT .as_bytes(), mork::expr!(s,"$"), mork::expr!(s,"$"));
        s.add_sexpr(WIKIPEDIA_PROJECT.as_bytes(), mork::expr!(s,"$"), mork::expr!(s,"$"));

        s.metta_calculus(10);

        let mut clear_flat = Vec::new();
        code_concat_exec_clear_leading_pred_many(
            &mut clear_flat, 
            &[(b"tuple-concat", 4),
              (b"col"         , 4),
              (b"column-index", 2),
              (b"exec"        , 4),
            ]
        );

        s.add_sexpr(&clear_flat, mork::expr!(s,"$"), mork::expr!(s,"$"));
        s.metta_calculus(MAX_ARITY_GEN as usize);
        clear_flat.clear();

        s.add_sexpr(&clear_flat, mork::expr!(s,"$"), mork::expr!(s,"$"));
        s.metta_calculus(10);
        
        // crate::utils::print_space(&s);
        crate::utils::print_sexpr_space(&s);



        let mut stdout = std::io::stdout();
        // code_concat_flat_product(
        //     &mut stdout
        //     );
        // code_concat_exec_clear_leading_pred(&mut stdout, b"tuple-concat");
        // code_concat_project_col(&mut stdout);
        stdout.flush();
        drop(stdout);

    }
}
pub(crate) mod utils;


fn main() {
    println!("Hello, world!");
}

