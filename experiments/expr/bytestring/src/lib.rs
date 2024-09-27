use std::fmt::{Debug, format, Formatter, Write};
use std::{mem, ops};
use std::ops::ControlFlow;
use smallvec::SmallVec;
use std::ptr::slice_from_raw_parts;

#[derive(Copy, Clone, Debug)]
pub struct Breadcrumb {
    parent: u32,
    arity: u8,
    seen: u8,
}

#[derive(Copy, Clone, Debug)]
pub enum Tag {
    NewVar,
    VarRef(u8),
    SymbolSize(u8),
    Arity(u8),
}

pub const fn item_byte(b: Tag) -> u8 {
    match b {
        Tag::NewVar => { 0b1100_0000 | 0 }
        Tag::SymbolSize(s) => { debug_assert!(s > 0 && s < 64); 0b1100_0000 | s }
        Tag::VarRef(i) => { debug_assert!(i < 64); 0b1000_0000 | i }
        Tag::Arity(a) => { debug_assert!(a < 64); 0b0000_0000 | a }
    }
}

pub fn byte_item(b: u8) -> Tag {
    if b == 0b1100_0000 { return Tag::NewVar; }
    else if (b & 0b1100_0000) == 0b1100_0000 { return Tag::SymbolSize(b & 0b0011_1111) }
    else if (b & 0b1100_0000) == 0b1000_0000 { return Tag::VarRef(b & 0b0011_1111) }
    else if (b & 0b1100_0000) == 0b0000_0000 { return Tag::Arity(b & 0b0011_1111) }
    else { panic!("reserved {}", b) }
}

pub const fn maybe_byte_item(b: u8) -> Result<Tag, u8> {
    if b == 0b1100_0000 { return Ok(Tag::NewVar); }
    else if (b & 0b1100_0000) == 0b1100_0000 { return Ok(Tag::SymbolSize(b & 0b0011_1111)) }
    else if (b & 0b1100_0000) == 0b1000_0000 { return Ok(Tag::VarRef(b & 0b0011_1111)) }
    else if (b & 0b1100_0000) == 0b0000_0000 { return Ok(Tag::Arity(b & 0b0011_1111)) }
    else { return Err(b) }
}

// pub fn str_item(ptr: *mut u8) -> (usize, Result<Tag, &[u8]>) {
//     let offset = 0;
//     loop {
//         match unsafe { *ptr.byte_add(offset) } {
//             '[' => {
//                 offset += 1;
//                 let i: u8 = match unsafe { *ptr.byte_add(offset) } {
//                     '0' => 0, '1' => 1, '2' => 2, '3' => 3, '4' => 4,
//                     '5' => 5, '6' => 6, '7' => 7, '8' => 8, '9' => 9,
//                     _ => { panic!() }
//                 };
//                 offset += 1;
//                 i = match unsafe { *ptr.byte_add(offset) } {
//                     '0' => 10*i + 0, '1' => 10*i + 1, '2' => 10*i + 2, '3' => 10*i + 3, '4' => 10*i + 4,
//                     '5' => 10*i + 5, '6' => 10*i + 6, '7' => 10*i + 7, '8' => 10*i + 8, '9' => 10*i + 9,
//                     ']' => { return (offset, Ok(Tag::Arity(i))); },
//                     _ => { panic!() }
//                 };
//                 offset += 1;
//                 match unsafe { *ptr.byte_add(offset) } {
//                     ']' => { return (offset, Ok(Tag::Arity(i))); },
//                     _ => { panic!() }
//                 };
//             }
//             '(' => {
//                 offset += 1;
//                 let i: u8 = match unsafe { *ptr.byte_add(offset) } {
//                     '0' => 0, '1' => 1, '2' => 2, '3' => 3, '4' => 4,
//                     '5' => 5, '6' => 6, '7' => 7, '8' => 8, '9' => 9,
//                     _ => { panic!() }
//                 };
//                 offset += 1;
//                 i = match unsafe { *ptr.byte_add(offset) } {
//                     '0' => 10*i + 0, '1' => 10*i + 1, '2' => 10*i + 2, '3' => 10*i + 3, '4' => 10*i + 4,
//                     '5' => 10*i + 5, '6' => 10*i + 6, '7' => 10*i + 7, '8' => 10*i + 8, '9' => 10*i + 9,
//                     ')' => { return (offset, Ok(Tag::SymbolSize(i))); },
//                     _ => { panic!() }
//                 };
//                 offset += 1;
//                 match unsafe { *ptr.byte_add(offset) } {
//                     ')' => { return (offset, Ok(Tag::SymbolSize(i))); },
//                     _ => { panic!() }
//                 };
//             }
//         }
//     }
// }

#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Expr {
    pub ptr: *mut u8,
}

#[derive(Clone, Debug)]
pub enum ExtractFailure {
    IntroducedVar(),
    RecurrentVar(u8),
    RefSymbolEarlyMismatch(u8, u8, u8),
    RefSymbolMismatch(u8, Vec<u8>, Vec<u8>),
    RefTypeMismatch(u8, Tag, Tag),
    RefExprEarlyMismatch(u8, u8, u8),
    RefExprMismatch(u8, Vec<u8>, Vec<u8>),
    ExprEarlyMismatch(u8, u8),
    SymbolEarlyMismatch(u8, u8),
    SymbolMismatch(Vec<u8>, Vec<u8>),
    TypeMismatch(Tag, Tag)
}
use ExtractFailure::*;

macro_rules! traverse {
    ($t1:ty, $t2:ty, $x:expr, $new_var:expr, $var_ref:expr, $symbol:expr, $zero:expr, $add:expr, $finalize:expr) => {{
        struct AnonTraversal {}
        impl Traversal<$t1, $t2> for AnonTraversal {
            #[inline(always)] fn new_var(&mut self, offset: usize) -> $t2 { ($new_var)(offset) }
            #[inline(always)] fn var_ref(&mut self, offset: usize, i: u8) -> $t2 { ($var_ref)(offset, i) }
            #[inline(always)] fn symbol(&mut self, offset: usize, s: &[u8]) -> $t2 { ($symbol)(offset, s) }
            #[inline(always)] fn zero(&mut self, offset: usize, a: u8) -> $t1 { ($zero)(offset, a) }
            #[inline(always)] fn add(&mut self, offset: usize, acc: $t1, sub: $t2) -> $t1 { ($add)(offset, acc, sub) }
            #[inline(always)] fn finalize(&mut self, offset: usize, acc: $t1) -> $t2 { ($finalize)(offset, acc) }
        }

        execute_loop(&mut AnonTraversal{}, $x, 0).1
    }};
}

macro_rules! traverseh {
    ($t1:ty, $t2:ty, $t3:ty, $x:expr, $v0:expr, $new_var:expr, $var_ref:expr, $symbol:expr, $zero:expr, $add:expr, $finalize:expr) => {{
        struct AnonTraversal{ v: $t3 }
        impl Traversal<$t1, $t2> for AnonTraversal {
            #[inline(always)] fn new_var(&mut self, offset: usize) -> $t2 { ($new_var)(&mut self.v, offset) }
            #[inline(always)] fn var_ref(&mut self, offset: usize, i: u8) -> $t2 { ($var_ref)(&mut self.v, offset, i) }
            #[inline(always)] fn symbol(&mut self, offset: usize, s: &[u8]) -> $t2 { ($symbol)(&mut self.v, offset, s) }
            #[inline(always)] fn zero(&mut self, offset: usize, a: u8) -> $t1 { ($zero)(&mut self.v, offset, a) }
            #[inline(always)] fn add(&mut self, offset: usize, acc: $t1, sub: $t2) -> $t1 { ($add)(&mut self.v, offset, acc, sub) }
            #[inline(always)] fn finalize(&mut self, offset: usize, acc: $t1) -> $t2 { ($finalize)(&mut self.v, offset, acc) }
        }

        let mut traversal = AnonTraversal{ v: $v0 };
        let result = execute_loop(&mut traversal, $x, 0).1;
        (traversal.v, result)
    }};
}

impl Expr {
    pub fn span(self) -> *const [u8] {
        let mut ez = ExprZipper::new(self);
        loop {
            if !ez.next() {
                return ez.finish_span();
            }
        }
    }

    pub fn size(self) -> usize {
        traverse!(usize, usize, self, |_| 1, |_, _| 1, |_, _| 1, |_, _| 1, |_, x, y| x + y, |_, x| x)
    }

    pub fn leaves(self) -> usize {
        traverse!(usize, usize, self, |_| 1, |_, _| 1, |_, _| 1, |_, _| 0, |_, x, y| x + y, |_, x| x)
    }

    pub fn expressions(self) -> usize {
        traverse!(usize, usize, self, |_| 0, |_, _| 0, |_, _| 0, |_, _| 1, |_, x, y| x + y, |_, x| x)
    }

    pub fn symbols(self) -> usize {
        traverse!(usize, usize, self, |_| 0, |_, _| 0, |_, _| 1, |_, _| 0, |_, x, y| x + y, |_, x| x)
    }

    pub fn newvars(self) -> usize {
        traverse!(usize, usize, self, |_| 1, |_, _| 0, |_, _| 0, |_, _| 0, |_, x, y| x + y, |_, x| x)
    }

    pub fn references(self) -> usize {
        traverse!(usize, usize, self, |_| 0, |_, _| 1, |_, _| 0, |_, _| 0, |_, x, y| x + y, |_, x| x)
    }

    pub fn variables(self) -> usize {
        traverse!(usize, usize, self, |_| 1, |_, _| 1, |_, _| 0, |_, _| 0, |_, x, y| x + y, |_, x| x)
    }

    pub fn max_arity(self) -> Option<u8> {
        traverse!(u8, Option<u8>, self, |_| None, |_, _| None, |_, _| None, |_, a| a, |_, x, y: Option<u8>| u8::max(x, y.unwrap_or(0)), |_, x| Some(x))
    }

    pub fn has_unbound(self) -> bool {
        // Doesn't work for some odd reason
        // std::panic::catch_unwind(|| traverseh!((), (), u8, self, 0,
        //     |c: &mut u8, _| { *c += 1; }, |c: &mut u8, _, r| { if r >= *c { panic!(); } }, |_, _, _| (), |_, _, _| (), |_, _, _, _| (), |_, _, _| ())
        // ).is_err()
        // traverseh!(ops::ControlFlow<(), ()>, ops::ControlFlow<(), ()>, u8, self, 0,
        //     |c: &mut u8, _| { *c += 1; ControlFlow::Continue(()) }, |c: &mut u8, _, r| { if r >= *c { ControlFlow::Break(()) } else { ControlFlow::Continue(()) } }, |_, _, _| ControlFlow::Continue(()), |_, _, _| ControlFlow::Continue(()), |_, _, l, r| { r?; l }, |_, _, l| l).1.is_break()
        traverseh!(bool, bool, u8, self, 0,
            |c: &mut u8, _| { *c += 1; false }, |c: &mut u8, _, r| r >= *c, |_, _, _| false, |_, _, _| false, |_, _, x, y| x || y, |_, _, x| x).1
    }

    pub fn prefix(self) -> Result<*const [u8], *const [u8]> {
        use ControlFlow::*;
        match traverse!(ControlFlow<usize, usize>, ControlFlow<usize, usize>, self,
            |o| Break(o), |o, _| Break(o), |o, _| Continue(o), |o, _| Continue(o), |_, a, n| { a?; n }, |_, a| a) {
            Break(offset) => { Ok(slice_from_raw_parts(self.ptr, offset)) } // proper prefix
            Continue(offset) => { Err(slice_from_raw_parts(self.ptr, offset)) } // full expr
        }
    }
    
    pub fn substitute(self, substitutions: &[Expr], oz: &mut ExprZipper) -> *const [u8] {
        let mut ez = ExprZipper::new(self);
        let mut var_count = 0;
        loop {
            match ez.tag() {
                Tag::NewVar => { oz.write_move(unsafe { substitutions[var_count].span().as_ref().unwrap() }); var_count += 1; }
                Tag::VarRef(r) => { oz.write_move(unsafe { substitutions[r as usize].span().as_ref().unwrap() }); }
                Tag::SymbolSize(s) => { oz.write_move(unsafe { slice_from_raw_parts(ez.root.ptr.byte_add(ez.loc), s as usize + 1).as_ref().unwrap() }); }
                Tag::Arity(_) => { unsafe { *oz.root.ptr.byte_add(oz.loc) = *ez.root.ptr.byte_add(ez.loc); oz.loc += 1; }; }
            }

            if !ez.next() {
                return ez.finish_span()
            }
        }
    }

    pub fn substitute_de_bruijn(self, substitutions: &[Expr], oz: &mut ExprZipper) -> *const [u8] {
        // this can technically be done in place...
        let mut ez = ExprZipper::new(self);
        let mut additions = vec![0u8; substitutions.len()];
        let mut var_count = 0;
        loop {
            match ez.tag() {
                Tag::NewVar => {
                    let nvars = substitutions[var_count].shift(additions[var_count], oz);
                    var_count += 1;
                    // ideally this is something like `_mm512_mask_add_epi8(additions, ~0 << var_count, _mm512_set1_epi8(nvars), additions)`
                    // TODO reference parent and get count that way, future additions don't need to happen yet
                    for j in var_count..additions.len() { additions[j] += nvars; }
                }
                Tag::VarRef(r) => {
                    substitutions[r as usize].bind(additions[r as usize], oz);
                }
                Tag::SymbolSize(s) => { oz.write_move(unsafe { slice_from_raw_parts(ez.root.ptr.byte_add(ez.loc), s as usize + 1).as_ref().unwrap() }); }
                Tag::Arity(_) => { unsafe { *oz.root.ptr.byte_add(oz.loc) = *ez.root.ptr.byte_add(ez.loc); oz.loc += 1; }; }
            }

            if !ez.next() {
                return ez.finish_span()
            }
        }
    }


    fn bind(self, n: u8, oz: &mut ExprZipper) -> *const [u8] {
        // this.foldMap(i => Var(if i == 0 then {index += 1; -index - n} else if i > 0 then i else i - n), App(_, _))
        let mut ez = ExprZipper::new(self);
        let mut var_count = 0u8;
        loop {
            match ez.tag() {
                Tag::NewVar => {
                    if n >= var_count { oz.write_var_ref(n + var_count); oz.loc += 1; var_count += 1; }
                    else { oz.write_var_ref(var_count - n); oz.loc += 1; var_count += 1; } }
                Tag::VarRef(i) => { oz.write_var_ref(n + i); oz.loc += 1; } // good
                Tag::SymbolSize(s) => { oz.write_move(unsafe { slice_from_raw_parts(ez.root.ptr.byte_add(ez.loc), s as usize + 1).as_ref().unwrap() }); }
                Tag::Arity(_) => { unsafe { *oz.root.ptr.byte_add(oz.loc) = *ez.root.ptr.byte_add(ez.loc); oz.loc += 1; }; }
            }

            if !ez.next() {
                return ez.finish_span()
            }
        }
    }

    fn shift(self, n: u8, oz: &mut ExprZipper) -> u8 {
        // this.foldMap(i => Var(if i >= 0 then i else i - n), App(_, _))
        let mut ez = ExprZipper::new(self);
        let mut new_var = 0u8;
        loop {
            match ez.tag() {
                Tag::NewVar => { oz.write_new_var(); oz.loc += 1; new_var += 1; }
                Tag::VarRef(i) => { oz.write_var_ref(i + n); oz.loc += 1; }
                Tag::SymbolSize(s) => { oz.write_move(unsafe { slice_from_raw_parts(ez.root.ptr.byte_add(ez.loc), s as usize + 1).as_ref().unwrap() }); }
                Tag::Arity(_) => { unsafe { *oz.root.ptr.byte_add(oz.loc) = *ez.root.ptr.byte_add(ez.loc); oz.loc += 1; }; }
            }

            if !ez.next() {
                // return self.loc + match self.tag() {
                //     Tag::NewVar => { 1 }
                //     Tag::VarRef(r) => { 1 }
                //     Tag::SymbolSize(s) => { 1 + (s as usize) }
                //     Tag::Arity(a) => { unreachable!() /* expression can't end in arity */ }
                // }
                return new_var;
            }
        }
    }

    pub fn unification(self, other: Expr) -> Result<Expr, ExtractFailure> {
        // [2][2] $ a [2] _1  a  unification
        // [2][2] b $ [2]  b _1
        //  ^ Arity-Arity, eq
        //     ^ Arity-Arity, eq
        //        ^ NewVar-rhs, lhs.substitute_de_bruijn(nvil->rhsz.subexpr()).unification(rhs)
        // [2][2] b a [2]  b  a  unification
        // [2][2] b $ [2]  b _1
        //  ^ Arity-Arity, eq
        //     ^ Arity-Arity, eq
        //        ^ Symbol-Symbol, eq
        //          ^ lhs-NewVar, lhs.unification(rhs.substitute_de_bruijn(nvir->lhsz.subexpr()))
        // [2][2] b a [2]  b  a  unification
        // [2][2] b a [2]  b  a
        //  ^ Arity-Arity, eq
        //     ^ Arity-Arity, eq
        //        ^ Symbol-Symbol, eq
        //          ^ Symbol-Symbol, eq
        //             ^ Arity-Arity, eq
        //                 ^ Symbol-Symbol, eq
        //                    ^ Symbol-Symbol, eq


        // [3] $       a _1        unification
        // [3] [2] b $ $ [2] $ _1
        //     ^ NewVar-rhs, lhs.substitute_de_bruijn(nvil->rhsz.subexpr()).unification(rhs)
        // [3] [2] b $ a [2] b _1     unification
        // [3] [2] b $ $ [2] $ _1
        //             ^ lhs-NewVar, lhs.unification(rhs.substitute_de_bruijn(nvir->lhsz.subexpr()))
        // [3] [2] b $ a [2] b _1     unification
        // [3] [2] b $ a [2] $ _1
        //                   ^ lhs-NewVar, lhs.unification(rhs.substitute_de_bruijn(nvir->lhsz.subexpr()))
        // [3] [2] b $ a [2] b _1     unification
        // [3] [2] b $ a [2] b _1


        let mut ez = ExprZipper::new(self);
        let mut iz = ExprZipper::new(other);
        let mut resv = vec![0; 100];
        let mut o = Expr{ ptr: resv.as_mut_ptr() };
        mem::forget(resv);
        let mut oz = ExprZipper::new(o);
        let mut nvi = 0;
        loop {
            match (ez.item(), iz.item()) {
                (Ok(Tag::NewVar), Ok(Tag::NewVar)) => {
                    // println!("both nvars");
                    let enext = ez.next(); let inext = iz.next();
                    assert_eq!(enext, inext);
                    if !enext {
                        unsafe { debug_assert_eq!(self.span().as_ref().unwrap(), other.span().as_ref().unwrap()); }
                        return Ok(self)
                    };
                    nvi += 1;
                }
                (lhs, Ok(Tag::NewVar)) => {
                    // println!("lhs-NewVar");
                    let mut kvs = vec![];
                    for i in 0..other.newvars() {
                        if i == nvi { kvs.push(ez.subexpr()) }
                        else {
                            let mut v = vec![item_byte(Tag::NewVar)];
                            kvs.push(Expr{ ptr: v.as_mut_ptr() });
                            mem::forget(v);
                        }
                    }
                    other.substitute_de_bruijn(&kvs, &mut oz);
                    return self.unification(o);
                }
                (Ok(Tag::NewVar), rhs) => {
                    // println!("NewVar-rhs");
                    let mut kvs = vec![];
                    for i in 0..self.newvars() {
                        if i == nvi { kvs.push(iz.subexpr()) }
                        else {
                            let mut v = vec![item_byte(Tag::NewVar)];
                            kvs.push(Expr{ ptr: v.as_mut_ptr() });
                            mem::forget(v);
                        }
                    }
                    self.substitute_de_bruijn(&kvs, &mut oz);
                    return o.unification(other);
                }
                (Ok(Tag::VarRef(r1)), Ok(Tag::VarRef(r2))) => {
                    if r1 != r2 { panic!("var ref mismatch") }
                    let enext = ez.next(); let inext = iz.next();
                    assert_eq!(enext, inext);
                    if !enext {
                        unsafe { debug_assert_eq!(self.span().as_ref().unwrap(), other.span().as_ref().unwrap()); }
                        return Ok(self)
                    };
                }
                (_, Ok(Tag::VarRef(r))) => { return Err(RecurrentVar(r)) }
                (Ok(Tag::VarRef(r)), _) => { return Err(RecurrentVar(r)) }
                (Err(aslice), Err(bslice)) => {
                    if aslice != bslice { return Err(SymbolMismatch(aslice.to_vec(), bslice.to_vec())) }
                    let enext = ez.next(); let inext = iz.next();
                    assert_eq!(enext, inext);
                    if !enext {
                        unsafe { debug_assert_eq!(self.span().as_ref().unwrap(), other.span().as_ref().unwrap()); }
                        return Ok(self)
                    };
                }
                (Ok(Tag::Arity(a)), Ok(Tag::Arity(b))) => {
                    if a != b { return Err(ExprEarlyMismatch(a, b)) }
                    let enext = ez.next(); let inext = iz.next();
                    assert_eq!(enext, inext);
                    if !enext {
                        unsafe { debug_assert_eq!(self.span().as_ref().unwrap(), other.span().as_ref().unwrap()); }
                        return Ok(self)
                    };
                }
                _ => {
                    // println!("mismatch");
                    return Err(TypeMismatch(ez.tag(), iz.tag())) }
            }
        }
    }

    pub fn transformData(self, pattern: Expr, template: Expr, oz: &mut ExprZipper) -> Result<(), ExtractFailure> {
        let mut ez = ExprZipper::new(self);
        match pattern.extract_data(&mut ez) {
            Ok(ref bindings) => { template.substitute(bindings, oz); Ok(()) }
            Err(e) => { Err(e) }
        }
    }

    pub fn transform(self, pattern: Expr, template: Expr) -> Result<Expr, ExtractFailure> {
        let mut transformation = vec![item_byte(Tag::Arity(2))];
        transformation.extend_from_slice(unsafe { template.span().as_ref().unwrap() });
        transformation.extend_from_slice(unsafe { pattern.span().as_ref().unwrap() });
        let mut data = vec![item_byte(Tag::Arity(2)), item_byte(Tag::NewVar)];
        data.extend_from_slice(unsafe { self.span().as_ref().unwrap() });
        let res = Expr{ ptr: transformation.as_mut_ptr() }.unification(Expr{ ptr: data.as_mut_ptr() })?;
        Ok(Expr{ ptr: unsafe { data.as_mut_ptr().byte_add(1) } })
    }

    pub fn extract_data(self, iz: &mut ExprZipper) -> Result<Vec<Expr>, ExtractFailure> {
        let mut ez = ExprZipper::new(self);
        let mut bindings: Vec<Expr> = vec![];
        loop {
            match (ez.tag(), iz.tag()) {
                (_, Tag::NewVar) => { return Err(IntroducedVar()) }
                (_, Tag::VarRef(r)) => { return Err(RecurrentVar(r)) }
                (Tag::NewVar, Tag::SymbolSize(_)) => { bindings.push(iz.subexpr()); iz.next(); if !ez.next() { return Ok(bindings) }; }
                (Tag::NewVar, Tag::Arity(a)) => { bindings.push(iz.subexpr());

                    let mut ez1 = ExprZipper::new(iz.subexpr());
                    let x = loop {
                        if !ez1.next() {
                            break ez1.finish_span();
                        }
                    };

                    iz.loc += (unsafe { x.as_ref().unwrap() }).len();

                    if !ez.next() { return Ok(bindings) }; }
                (Tag::VarRef(i), Tag::SymbolSize(s)) => {
                    if let Tag::SymbolSize(s_) = unsafe { byte_item(*bindings[i as usize].ptr) } {
                        if s != s_ { return Err(RefSymbolEarlyMismatch(i, s, s_)) }
                        let aslice = unsafe { &*slice_from_raw_parts(bindings[i as usize].ptr.byte_add(1), s_ as usize) };
                        let bslice = unsafe { &*slice_from_raw_parts(iz.subexpr().ptr.byte_add(1), s as usize) };
                        if aslice != bslice { return Err(RefSymbolMismatch(i, aslice.to_vec(), bslice.to_vec())) }
                        iz.next(); if !ez.next() { return Ok(bindings) };
                    } else {
                        return Err(RefTypeMismatch(i, ez.tag(), iz.tag()))
                    }
                }
                (Tag::VarRef(i), Tag::Arity(s)) => {
                    if let Tag::Arity(s_) = unsafe { byte_item(*bindings[i as usize].ptr) } {
                        if s != s_ { return Err(RefExprEarlyMismatch(i, s, s_)) }
                        // TODO this is quite wasteful: neither span should be re-calculated
                        let aslice = unsafe { &*bindings[i as usize].span() };
                        let bslice = unsafe { &*iz.subexpr().span() };
                        if aslice != bslice { return Err(RefExprMismatch(i, aslice.to_vec(), bslice.to_vec())) }
                        iz.next(); if !ez.next() { return Ok(bindings) };
                    } else {
                        return Err(RefTypeMismatch(i, ez.tag(), iz.tag()))
                    }
                }
                (Tag::SymbolSize(a), Tag::SymbolSize(b)) => {
                    if a != b { return Err(SymbolEarlyMismatch(a, b)) }
                    let aslice = unsafe { &*slice_from_raw_parts(ez.subexpr().ptr.byte_add(1), a as usize) };
                    let bslice = unsafe { &*slice_from_raw_parts(iz.subexpr().ptr.byte_add(1), b as usize) };
                    if aslice != bslice { return Err(SymbolMismatch(aslice.to_vec(), bslice.to_vec())) }
                    iz.next(); if !ez.next() { return Ok(bindings) };
                }
                (Tag::Arity(a), Tag::Arity(b)) => {
                    if a != b { return Err(ExprEarlyMismatch(a, b)) }
                    iz.next(); if !ez.next() { return Ok(bindings) };
                }
                _ => { return Err(TypeMismatch(ez.tag(), iz.tag())) }
            }
        }
    }

    #[inline(never)]
    pub fn string(&self) -> String {
        let mut traversal = DebugTraversal{ string: String::new(), transient: false };
        execute_loop(&mut traversal, *self, 0);
        traversal.string
    }

    #[inline(never)]
    pub fn serialize<Target : std::io::Write, F : for <'a> Fn(&'a [u8]) -> &'a str>(&self, t: &mut Target, map_symbol: F) -> () {
        let mut traversal = SerializerTraversal{ out: t, map_symbol: map_symbol, transient: false };
        execute_loop(&mut traversal, *self, 0);
    }
}

trait Traversal<A, R> {
    fn new_var(&mut self, offset: usize) -> R;
    fn var_ref(&mut self, offset: usize, i: u8) -> R;
    fn symbol(&mut self, offset: usize, s: &[u8]) -> R;
    fn zero(&mut self, offset: usize, a: u8) -> A;
    fn add(&mut self, offset: usize, acc: A, sub: R) -> A;
    fn finalize(&mut self, offset: usize, acc: A) -> R;
}

fn execute<A, R, T : Traversal<A, R>>(t: &mut T, e: Expr, i: usize) -> (usize, R) {
    match unsafe { byte_item(*e.ptr.byte_add(i)) } {
        Tag::NewVar => { (1, t.new_var(i)) }
        Tag::VarRef(r) => { (1, t.var_ref(i, r)) }
        Tag::SymbolSize(s) => {
            let slice = unsafe { &*slice_from_raw_parts(e.ptr.byte_add(i + 1), s as usize) };
            (s as usize + 1, t.symbol(i, slice))
        }
        Tag::Arity(a) => {
            let mut offset = 1;
            let mut acc = t.zero(i, a);
            for k in 0..a {
                let (d, r) = execute(t, e, i + offset);
                acc = t.add(i + offset, acc, r);
                offset += d;
            }
            (offset, t.finalize(i + offset, acc))
        }
    }
}

fn execute_loop<A, R, T : Traversal<A, R>>(t: &mut T, e: Expr, i: usize) -> (usize, R) {
    // example run with e = [3] a [2] x y [2] p q
    // 3 zero()
    // value = symbol(a); 2 add(zero(), symbol(a))
    // 2 add(zero(), symbol(a)), 2 zero()
    // value = symbol(x); 2 add(zero(), symbol(a)), 1 add(zero(), symbol(x))
    // value = symbol(y); 2 add(zero(), symbol(a)); value = finalize(add(add(zero(), symbol(x)), symbol(y))); 1 add(add(zero(), symbol(a)), finalize(add(add(zero(), symbol(x)), symbol(y))))
    // 1 add(add(zero(), symbol(a)), finalize(add(add(zero(), symbol(x)), symbol(y)))), 2 zero()
    // value = symbol(p); 1 add(add(zero(), symbol(a)), finalize(add(add(zero(), symbol(x)), symbol(y)))), 1 add(zero(), symbol(p))
    // value = symbol(q); 1 add(add(zero(), symbol(a)), finalize(add(add(zero(), symbol(x)), symbol(y)))); value = finalize(add(add(zero(), symbol(p)), symbol(q))); value = finalize(add(..., ...)); return
    struct State<X> { iter: u8, payload: X }
    let mut stack: SmallVec<[State<A>; 8]> = SmallVec::new();
    // let mut stack = vec![];
    let mut j = i;
    'putting: loop {
        let mut value = match unsafe { byte_item(*e.ptr.byte_add(j)) } {
            Tag::NewVar => { j += 1; t.new_var(j - 1) }
            Tag::VarRef(r) => { j += 1; t.var_ref(j - 1, r) }
            Tag::SymbolSize(s) => {
                let slice = unsafe { &*slice_from_raw_parts(e.ptr.byte_add(j + 1), s as usize) };
                let v = t.symbol(j, slice);
                j += s as usize + 1;
                v
            }
            Tag::Arity(a) => {
                j += 1;
                let mut acc = t.zero(j, a);
                stack.push(State{ iter: a, payload: acc });
                continue 'putting;
            }
        };

        'popping: loop {
            match stack.last_mut() {
                None => { return (j, value) }
                Some(&mut State{ iter: ref mut k, payload: ref mut acc }) => {
                    unsafe {
                        std::ptr::write(k, std::ptr::read(k).wrapping_sub(1));
                        std::ptr::write(acc, t.add(j, std::ptr::read(acc), value));
                        if std::ptr::read(k) != 0 { continue 'putting }
                    }
                }
            }

            value = match stack.pop() {
                Some(State{ iter: _, payload: acc }) => t.finalize(j, acc),
                None => break 'popping
            }
        }
    }
}

struct DebugTraversal { string: String, transient: bool }

impl Traversal<(), ()> for DebugTraversal {
    #[inline(always)] fn new_var(&mut self, offset: usize) -> () { if self.transient { self.string.push(' '); }; self.string.push('$'); }
    #[inline(always)] fn var_ref(&mut self, offset: usize, i: u8) -> () { if self.transient { self.string.push(' '); }; self.string.push('_'); self.string.push_str((i as u16 + 1).to_string().as_str()); }
    #[inline(always)] fn symbol(&mut self, offset: usize, s: &[u8]) -> () { match std::str::from_utf8(s) {
        Ok(string) => { if self.transient { self.string.push(' '); }; self.string.push_str(string); }
        Err(_) => { if self.transient { self.string.push(' '); }; for b in s { self.string.push_str(format!("\\x{:x}", b).as_str()); }; }
    } }
    #[inline(always)] fn zero(&mut self, offset: usize, a: u8) -> () { if self.transient { self.string.push(' '); }; self.string.push('('); self.transient = false; }
    #[inline(always)] fn add(&mut self, offset: usize, acc: (), sub: ()) -> () { self.transient = true; }
    #[inline(always)] fn finalize(&mut self, offset: usize, acc: ()) -> () { self.string.push(')'); }
}

impl Debug for Expr {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.string());
        Ok(())
    }
}

struct SerializerTraversal<'a, Target : std::io::Write, F : for <'b> Fn(&'b [u8]) -> &'b str> { out: &'a mut Target, map_symbol: F, transient: bool }

impl <Target : std::io::Write, F : for <'b> Fn(&'b [u8]) -> &'b str> Traversal<(), ()> for SerializerTraversal<'_, Target, F> {
    #[inline(always)] fn new_var(&mut self, offset: usize) -> () { if self.transient { self.out.write(" ".as_bytes()); }; self.out.write("$".as_bytes()); }
    #[inline(always)] fn var_ref(&mut self, offset: usize, i: u8) -> () { if self.transient { self.out.write(" ".as_bytes()); }; self.out.write("_".as_bytes()); self.out.write((i as u16 + 1).to_string().as_bytes()); }
    #[inline(always)] fn symbol(&mut self, offset: usize, s: &[u8]) -> () { if self.transient { self.out.write(" ".as_bytes()); }; self.out.write((self.map_symbol)(s).as_bytes()); }
    #[inline(always)] fn zero(&mut self, offset: usize, a: u8) -> () { if self.transient { self.out.write(" ".as_bytes()); }; self.out.write("(".as_bytes()); self.transient = false; }
    #[inline(always)] fn add(&mut self, offset: usize, acc: (), sub: ()) -> () { self.transient = true; }
    #[inline(always)] fn finalize(&mut self, offset: usize, acc: ()) -> () { self.out.write(")".as_bytes()); }
}

#[derive(Clone)]
pub struct ExprZipper {
    pub root: Expr,
    pub loc: usize,
    pub trace: Vec<Breadcrumb>,
}

impl ExprZipper {
    #[inline] pub fn new(e: Expr) -> Self {
        match unsafe { byte_item(*e.ptr) } {
            Tag::NewVar => { Self { root: e, loc: 0, trace: vec![] } }
            Tag::VarRef(r) => { Self { root: e, loc: 0, trace: vec![] } }
            Tag::SymbolSize(s) => { Self { root: e, loc: 0, trace: vec![] } }
            Tag::Arity(a) => {
                Self {
                    root: e,
                    loc: 0,
                    trace: vec![Breadcrumb { parent: 0, arity: a, seen: 0 }],
                    // trace: vec![],
                }
            }
        }
    }

    #[inline] pub fn tag(&self) -> Tag { unsafe { byte_item(*self.root.ptr.byte_add(self.loc)) } }
    #[inline] pub fn item(&self) -> Result<Tag, &[u8]> {
        let tag = self.tag();
        if let Tag::SymbolSize(n) = tag { return unsafe { Err(&*slice_from_raw_parts(self.root.ptr.byte_add(self.loc + 1), n as usize)) } }
        else { return Ok(tag) }
    }
    #[inline] pub fn subexpr(&self) -> Expr { unsafe { Expr { ptr: self.root.ptr.byte_add(self.loc) } } }
    #[inline] pub fn span(&self) -> &[u8] { unsafe { &*slice_from_raw_parts(self.root.ptr, self.loc) } }

    pub fn write_arity(&mut self, arity: u8) -> bool {
        unsafe {
            *self.root.ptr.byte_add(self.loc) = item_byte(Tag::Arity(arity));
            true
        }
    }
    pub fn write_move(&mut self, value: &[u8]) -> bool {
        unsafe {
            let l = value.len();
            std::ptr::copy_nonoverlapping(value.as_ptr(), self.root.ptr.byte_add(self.loc), l);
            self.loc += l;
            true
        }
    }
    pub fn write_symbol(&mut self, value: &[u8]) -> bool {
        unsafe {
            let l = value.len();
            debug_assert!(l < 64);
            let w = self.root.ptr.byte_add(self.loc);
            *w = item_byte(Tag::SymbolSize(l as u8));
            std::ptr::copy_nonoverlapping(value.as_ptr(), w.byte_add(1), l);
            true
        }
    }
    pub fn write_new_var(&mut self) -> bool {
        unsafe {
            *self.root.ptr.byte_add(self.loc) = item_byte(Tag::NewVar);
            true
        }
    }
    pub fn write_var_ref(&mut self, index: u8) -> bool {
        unsafe {
            *self.root.ptr.byte_add(self.loc) = item_byte(Tag::VarRef(index));
            true
        }
    }

    pub fn tag_str(&self) -> String {
        match self.tag() {
            Tag::NewVar => { "$".to_string() }
            Tag::VarRef(r) => { format!("_{}", r + 1) }
            Tag::SymbolSize(s) => { format!("({})", s) }
            Tag::Arity(a) => { format!("[{}]", a) }
        }
    }

    pub fn item_str(&self) -> String {
        match self.item() {
            Ok(tag) => {
                match tag {
                    Tag::NewVar => { "$".to_string() }
                    Tag::VarRef(r) => { format!("_{}", r + 1) }
                    Tag::Arity(a) => { format!("[{}]", a) }
                    _ => { unreachable!() }
                }
            }
            Err(s) => {
                match std::str::from_utf8(s) {
                    Ok(string) => { format!("{}", string) }
                    Err(_) => { format!("{:?}", s) }
                }
            }
        }
    }

    pub fn next(&mut self) -> bool {
        self.gnext(0)
    }

    pub fn gnext(&mut self, offset: usize) -> bool {
        // let t = self.tag();
        // let ct = self.tag_str();
        match self.trace[offset..].last_mut() {
            None => { false }
            Some(&mut Breadcrumb { parent: p, arity: a, seen: ref mut s }) => {
                // println!("parent {} loc {} tag {}", p, self.loc, ct);
                // println!("{} < {}", s, a);
                if *s < a {
                    *s += 1;

                    self.loc += if let Tag::SymbolSize(n) = self.tag() { n as usize + 1 } else { 1 };

                    if let Tag::Arity(a) = self.tag() {
                        self.trace.push(Breadcrumb { parent: self.loc as u32, arity: a, seen: 0 })
                    }

                    // println!("returned true");
                    true
                } else {
                    self.trace.pop();
                    self.next()
                }
            }
        }
    }

    pub fn parent(&mut self) -> bool {
        let Some(Breadcrumb { parent: p, arity: a, seen: s }) = self.trace.last() else { return false; };
        self.loc = *p as usize;
        self.trace.pop();
        true
    }

    pub fn reset(&mut self) -> bool {
        self.loc = 0;
        unsafe { self.trace.set_len(0); }
        true
    }

    pub fn next_child(&mut self) -> bool {
        self.next_descendant(0, 0)
    }

    pub fn next_descendant(&mut self, to: i32, offset: usize) -> bool {
        let (base, backup) = if to < 0 {
            let last = self.trace.len() as i32 + to;
            (self.trace[last as usize].parent, self.trace[last as usize])
        } else if to > 0 {
            (self.trace[(to - 1) as usize].parent, self.trace[(to - 1) as usize])
        } else { (0, self.trace[0]) };
        let initial = self.trace.clone();

        let mut lc = 0;
        loop {
            if !self.gnext(0) {
                // println!("no next {} {}", lc, self.trace.len());
                self.trace = initial;
                return false; }
            let l = self.trace.len() - 1 - offset;
            let parent = self.trace[l].parent;
            if let Tag::Arity(_) = self.tag() {
                if l > 0 && self.trace[l - 1].parent == base {
                    return true;
                }
            } else {
                if parent == base {
                    return true;
                }
            }
            lc += 1;
        }
    }

    /// Debug traversal
    pub fn traverse(&self, i: usize) -> usize {
        match unsafe { maybe_byte_item(*self.root.ptr.byte_add(self.loc + i)) } {
            Ok(Tag::NewVar) => { print!("$"); 1 }
            Ok(Tag::VarRef(r)) => { print!("_{}", r + 1); 1 }
            Ok(Tag::SymbolSize(s)) => {
                let slice = unsafe { &*slice_from_raw_parts(self.root.ptr.byte_add(self.loc + i + 1), s as usize) };
                match std::str::from_utf8(slice) {
                    Ok(string) => { print!("{}", string) }
                    Err(_) => { for b in slice { print!("\\x{:x}", b) } }
                }
                s as usize + 1
            }
            Ok(Tag::Arity(a)) => {
                print!("(");
                let mut offset = 1;
                for k in 0..a {
                    offset += self.traverse(i + offset);
                    if k != (a - 1) { print!(" ") }
                }
                print!(")");
                offset
            }
            Err(b) => {
                print!("{}", b as usize);
                1
            }
        }
    }

    pub fn finish_span(&self) -> *const [u8] {
        let size = self.loc + match self.tag() {
            Tag::NewVar => { 1 }
            Tag::VarRef(r) => { 1 }
            Tag::SymbolSize(s) => { 1 + (s as usize) }
            Tag::Arity(a) => { unreachable!() /* expression can't end in arity */ }
        };
        return slice_from_raw_parts(self.root.ptr, size)
    }
}

const fn to_bytes<const N: usize>(s: &str) -> [u8; N] {
    let bytes = s.as_bytes();
    let mut array = [0u8; N];
    let mut i = 0;
    while i < N {
        array[i] = bytes[i];
        i += 1;
    }
    array
}

const fn is_digit(b: u8) -> bool {
    b >= b'0' && b <= b'9'
}

const fn digit_value(b: u8) -> u8 {
    b - b'0'
}


#[macro_export]
macro_rules! parse {
    ($s:literal) => {{
        const N: usize = compute_length($s);
        const ARR: [u8; N] = parse::<N>($s);
        ARR
    }};
}

pub const fn compute_length(s: &str) -> usize {
    let bytes = s.as_bytes();
    let len = bytes.len();
    let mut i = 0;
    let mut n = 0;

    while i < len {
        // Skip spaces
        while i < len && bytes[i] == b' ' {
            i += 1;
        }
        if i >= len {
            break;
        }

        let b = bytes[i];

        if b == b'[' {
            // Parse [number]
            i += 1;
            while i < len && bytes[i] != b']' {
                i += 1;
            }
            i += 1; // Skip ']'
            n += 1; // item_byte(Tag::Arity(number))
        } else if b == b'$' {
            i += 1;
            n += 1; // item_byte(Tag::NewVar)
        } else if b == b'_' {
            // Parse _number
            i += 1;
            while i < len && is_digit(bytes[i]) {
                i += 1;
            }
            n += 1; // item_byte(Tag::VarRef(number - 1))
        } else {
            // Parse symbol (word)
            let mut word_len = 0;
            while i < len && bytes[i] != b' ' {
                word_len += 1;
                i += 1;
            }
            n += 1 + word_len; // item_byte + word bytes
        }
    }

    n
}

pub const fn parse<const N: usize>(s: &str) -> [u8; N] {
    let bytes = s.as_bytes();
    let len = bytes.len();
    let mut arr = [0u8; N];
    let mut i = 0;
    let mut pos = 0;

    while i < len {
        // Skip spaces
        while i < len && bytes[i] == b' ' {
            i += 1;
        }
        if i >= len {
            break;
        }

        let b = bytes[i];

        if b == b'[' {
            // Parse [number]
            i += 1; // Skip '['
            let mut num = 0u8;
            while i < len && is_digit(bytes[i]) {
                num = num * 10 + digit_value(bytes[i]);
                i += 1;
            }
            if i < len && bytes[i] == b']' {
                i += 1; // Skip ']'
                arr[pos] = item_byte(Tag::Arity(num));
                pos += 1;
            } else {
                // Handle error: expected ']'
                i += 1;
            }
        } else if b == b'$' {
            i += 1; // Skip '$'
            arr[pos] = item_byte(Tag::NewVar);
            pos += 1;
        } else if b == b'_' {
            // Parse _number
            i += 1; // Skip '_'
            let mut num = 0u8;
            while i < len && is_digit(bytes[i]) {
                num = num * 10 + digit_value(bytes[i]);
                i += 1;
            }
            if num > 0 {
                arr[pos] = item_byte(Tag::VarRef(num - 1));
            } else {
                arr[pos] = item_byte(Tag::VarRef(0));
            }
            pos += 1;
        } else {
            // Parse symbol (word)
            let word_start = i;
            let mut word_len = 0;
            while i < len && bytes[i] != b' ' {
                word_len += 1;
                i += 1;
            }
            // Insert item_byte(Tag::SymbolSize(word_len))
            arr[pos] = item_byte(Tag::SymbolSize(word_len));
            pos += 1;
            // Copy the word bytes
            let mut j = 0;
            while j < word_len {
                arr[pos] = bytes[word_start + (j as usize)];
                pos += 1;
                j += 1;
            }
        }
    }

    arr
}


pub fn serialize(bytes: &[u8]) -> String {
    let mut result = String::new();
    let mut i = 0;
    while i < bytes.len() {
        let b = bytes[i];
        match maybe_byte_item(b) {
            Ok(tag) => {
                match tag {
                    Tag::NewVar => {
                        result.push('$');
                        i += 1;
                    },
                    Tag::VarRef(idx) => {
                        result.push('_');
                        result.push_str(&format!("{}", idx + 1)); // idx is 0-based
                        i += 1;
                    },
                    Tag::Arity(a) => {
                        result.push('[');
                        result.push_str(&format!("{}", a));
                        result.push(']');
                        i += 1;
                    },
                    Tag::SymbolSize(s) => {
                        i += 1;
                        if i + (s as usize) > bytes.len() {
                            // Error: Not enough bytes for symbol
                            result.push_str("<Error: Not enough bytes for symbol>");
                            break;
                        } else {
                            // Read the next s bytes as symbol bytes
                            for j in 0..s {
                                let symbol_byte = bytes[i + j as usize];
                                // Check if symbol_byte is printable ASCII
                                if (symbol_byte.is_ascii_graphic() || symbol_byte == b' ') && symbol_byte != b'\\' {
                                    result.push(symbol_byte as char);
                                } else {
                                    result.push_str(&format!("\\x{:02X}", symbol_byte));
                                }
                            }
                            i += s as usize;
                        }
                    }
                }
            },
            Err(b) => {
                // Unknown byte
                result.push_str(&format!("\\x{:02X}", b));
                i += 1;
            }
        }
        // Add space between tokens if needed
        if i < bytes.len() {
            result.push(' ');
        }
    }
    result
}
