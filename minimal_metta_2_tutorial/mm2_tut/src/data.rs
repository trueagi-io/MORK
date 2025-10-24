use std::{ffi::os_str::Display, fmt::Debug};

use pathmap::zipper::{ZipperIteration, ZipperMoving, ZipperReadOnlyIteration};

const EX_01 : &str = 
r#"
; A comment, everything after this til the next newline is ignored by the parser.

true
2
"abc def"
$x
(abc def) 
(abc (d e f))
($x $x)
(a "
" b)

; ; the following is too big
; (
;   00 01 02 03 04 05 06 07 08 09
;   10 11 12 13 14 15 16 17 18 19
;   20 21 22 23 24 25 26 27 28 29
;   30 31 32 33 34 35 36 37 38 39
;   40 41 42 43 44 45 46 47 48 49
;   50 51 52 53 54 55 56 57 58 59
;   60 61 62 63
; )

; ; ; the following is too big
; ( ($x00 $x01 $x02 $x03 $x04 $x05 $x06 $x07 $x08 $x09)
;   ($x10 $x11 $x12 $x13 $x14 $x15 $x16 $x17 $x18 $x19)
;   ($x20 $x21 $x22 $x23 $x24 $x25 $x26 $x27 $x28 $x29)
;   ($x30 $x31 $x32 $x33 $x34 $x35 $x36 $x37 $x38 $x39)
;   ($x40 $x41 $x42 $x43 $x44 $x45 $x46 $x47 $x48 $x49)
;   ($x50 $x51 $x52 $x53 $x54 $x55 $x56 $x57 $x58 $x59)
;   ($x60 $x61 $x62 $x63 $x64 ____ ____ ____ ____ ____)
; )

; ; here are 100 nested parentheses
; (((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((())))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
"#;


#[test]
fn raw_representation() {

    #[derive(Debug)]
    enum ExprRepr { Tag(mork_expr::Tag), Byte(u8)  }

    struct PrettyExpr<'a> { pub expr: &'a[ExprRepr], pub chars : bool, pub hex : bool}
    impl std::fmt::Display for PrettyExpr<'_> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            debug_expr_repr_slice(f, self.expr, true, true)
        }
    }

    fn debug_expr_repr(mut f : &mut core::fmt::Formatter<'_>, er : &ExprRepr, chars : bool, hex : bool) -> std::fmt::Result {
        match er {
            ExprRepr::Tag(tag) => 
                match tag {
                    mork_expr::Tag::NewVar        => write!(f,"$"),
                    mork_expr::Tag::VarRef(r)     => write!(f,"&{}",r),
                    mork_expr::Tag::SymbolSize(s) => write!(f,"<{}>",s),
                    mork_expr::Tag::Arity(a)      => write!(f,"[{}]",a),
                },
            ExprRepr::Byte(byte) => { 
                    write!(f,"{{")?;
                    if chars {write!(f,"{:?}",*byte as char)?}
                    if hex   {write!(f,"x{:0>2x}",byte)?}
                    write!(f,"}}")
                  }
        }
    }
    fn debug_expr_repr_slice(mut f : &mut core::fmt::Formatter<'_>, expr : &[ExprRepr], chars : bool, hex : bool) -> std::fmt::Result {
        for (i, each) in expr.iter().enumerate() {

            debug_expr_repr(f, each, chars, hex)?;
            if i+1 < expr.len() {
                write!(f, " ")?
            }
        }
        Ok(())
    }
    


    let mut s = mork::space::Space::new();

    s.add_all_sexpr(EX_01.as_bytes());

    let mut rz = s.btm.read_zipper();


    let mut v   = Vec::new();
    let mut raw = Vec::new();
    while rz.to_next_val() {
        let mut expr = Vec::new();
        let path = rz.path();
        let e = mork_expr::Expr { ptr : path.as_ptr() as *mut _};
        let mut ez = mork_expr::ExprZipper::new(e);

        raw.push(path.to_vec());
        
        loop {
            let tag = ez.tag();

            expr.push(ExprRepr::Tag(tag));
            unsafe { 
                if let mork_expr::Tag::SymbolSize(len) = tag {
                    let mut start = ez.subexpr().ptr.add(1);
                    let end   = start.add(len as usize);
                    while start != end {
                        expr.push(ExprRepr::Byte(*start));
                        start = start.add(1)
                    }
                } 
            }
            if !ez.next() {break;}
        }
        v.push(expr);
    }


    for each in raw {
        println!("{:?}", each)
    }
    println!();
    for each in v {
        println!("{}", PrettyExpr { expr: &each , chars : true, hex : true});
        println!("{:?}", each);
    }

}
