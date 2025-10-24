


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

pub(crate) struct PrettyExpr<'a> { pub expr: &'a[ExprRepr], pub chars : bool, pub hex : bool}
impl std::fmt::Display for PrettyExpr<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        debug_expr_repr_slice(f, self.expr, true, true)
    }
}

pub(crate) fn debug_expr_repr(mut f : &mut core::fmt::Formatter<'_>, er : &ExprRepr, chars : bool, hex : bool) -> std::fmt::Result {
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
pub(crate) fn debug_expr_repr_slice(mut f : &mut core::fmt::Formatter<'_>, expr : &[ExprRepr], chars : bool, hex : bool) -> std::fmt::Result {
    for (i, each) in expr.iter().enumerate() {

        debug_expr_repr(f, each, chars, hex)?;
        if i+1 < expr.len() {
            write!(f, " ")?
        }
    }
    Ok(())
}

