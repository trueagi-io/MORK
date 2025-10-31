use mork::space::Space;
 use mork_expr::Tag;
use pathmap::zipper::{ZipperIteration, ZipperMoving};



#[derive(Debug)]
pub(crate) enum ExprRepr { Tag(mork_expr::Tag), Byte(u8)  }

pub(crate) fn expr_to_expr_repr(e : mork_expr::Expr) -> Vec<ExprRepr>{
        let mut ez = mork_expr::ExprZipper::new(e);
        let mut expr = Vec::new();
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
        expr
}

#[repr(u8)]
pub(crate)enum PrettyExprSym {
    Chars   = 1<<0,
    Hex     = 1<<1,
    Curlies = 1<<2,
    Sym     = 0,
}

pub(crate) struct PrettyExpr<'a> { pub expr: &'a[ExprRepr], pub options : u8}
impl<'a> Default for PrettyExpr<'a> {
    fn default() -> Self {
        use PrettyExprSym as S;
        Self { expr: &[], options : S::Sym as u8}
    }
}
impl std::fmt::Display for PrettyExpr<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        debug_expr_repr_slice(f, self.expr, self.options)
    }
}

pub(crate) fn debug_expr_repr(mut f : &mut core::fmt::Formatter<'_>, er : &ExprRepr, options : u8) -> std::fmt::Result {
    use PrettyExprSym as S;
    match er {
        ExprRepr::Tag(tag) => 
            match tag {
                mork_expr::Tag::NewVar        => write!(f,"$"),
                mork_expr::Tag::VarRef(r)     => write!(f,"&{}",r),
                mork_expr::Tag::SymbolSize(s) => {
                    if options != S::Sym as u8 {  
                        write!(f,"<{}>",s)?;
                    }; 
                    Ok(())
                },
                mork_expr::Tag::Arity(a)      => write!(f,"[{}]",a),
            },
        ExprRepr::Byte(byte) => {
                if options == S::Sym    as u8      { write!(f,"{}",*byte as char)? ; return Ok(())}
                if options & S::Curlies as u8 == 1 { write!(f,"{{")?;                }
                if options & S::Chars   as u8 == 1 { write!(f,"{:?}",*byte as char)? }
                if options & S::Hex     as u8 == 1 { write!(f,"x{:0>2x}",byte)?      }
                if options & S::Curlies as u8 == 1 { write!(f,"}}")?                 }
                Ok(())
              }
    }
}
pub(crate) fn debug_expr_repr_slice(mut f : &mut core::fmt::Formatter<'_>, expr : &[ExprRepr], options : u8) -> std::fmt::Result {
    let mut was_raw = false;
    for (i, each) in expr.iter().enumerate() {
        let is_raw = matches!(each,ExprRepr::Byte(_));
        if was_raw && !is_raw {
            write!(f, " ")?
        }

        if options != PrettyExprSym::Sym as u8 {
        }
        debug_expr_repr(f, each, options)?;
        if !is_raw {
            if options != PrettyExprSym::Sym as u8 
            || !matches!(each, ExprRepr::Tag(mork_expr::Tag::SymbolSize(_)))
            {
                write!(f, " ")?
            }
            
        }
        was_raw = is_raw        
    }
    Ok(())
}

pub(crate) fn print_space(s:&Space) {
    print_space_at_prefix(s, &[]);
}
pub(crate) fn print_space_at_prefix(s:&Space, p:&[u8]) {
    let mut rz = s.btm.read_zipper_at_borrowed_path(p);

    while rz.to_next_val() {
        let path = rz.path();
        let p = crate::utils::expr_to_expr_repr(
            mork_expr::Expr { ptr: path.as_ptr() as *mut _ }
        );
        let e = crate::utils::PrettyExpr{expr:&p, ..Default::default()};
        println!("{}",e)
    }
}

pub(crate) fn print_sexpr_space(s : &Space) {
    use std::io::Write;

    let mut v = std::io::stdout();
    s.dump_all_sexpr(&mut v);
    v.flush();
    drop(v);
}