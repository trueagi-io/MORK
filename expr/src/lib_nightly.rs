use std::collections::BTreeMap;
use std::convert::Infallible;
use std::ops::{Coroutine, CoroutineState};
use std::ptr::slice_from_raw_parts;
use crate::{byte_item, item_byte, traverseh, Expr, ExprEnv, ExprVar, ExprZipper, Tag, APPLY_DEPTH, PRINT_DEBUG};

pub fn item_sink<W: std::io::Write>(target: &mut W) -> impl Coroutine<Result<Tag, &[u8]>, Yield=(), Return=std::io::Result<Infallible>> {
    #[coroutine] move |mut i: Result<Tag, &[u8]>| {
        loop {
            match i {
                Ok(Tag::SymbolSize(_)) => { panic!("sink uses Err(&[u8]) for symbols, gotten Tag::SymbolSize") }
                Ok(tag) => {
                    target.write_all(&[item_byte(tag)])?;
                }
                Err(slice) => {
                    let l = slice.len();
                    debug_assert!(l < 64);
                    target.write_all(&[item_byte(Tag::SymbolSize(l as _))])?;
                    target.write_all(slice)?;
                }
            }
            i = yield ();
        }
    }
}

pub fn item_source<'a>(e: Expr) -> impl Coroutine<(), Yield=Result<Tag, &'a [u8]>, Return=usize> {
    #[coroutine] move || {
        let mut stack: smallvec::SmallVec<[u8; 64]> = smallvec::SmallVec::new();
        let mut j: usize = 0;
        'putting: loop {
            match unsafe { byte_item(*e.ptr.byte_add(j)) } {
                Tag::NewVar => { j += 1; yield Ok(Tag::NewVar) }
                Tag::VarRef(r) => { j += 1; yield Ok(Tag::VarRef(r)) }
                Tag::SymbolSize(s) => {
                    let slice = unsafe { &*slice_from_raw_parts(e.ptr.byte_add(j + 1), s as usize) };
                    yield Err(slice);
                    j += s as usize + 1;
                }
                Tag::Arity(a) => {
                    yield Ok(Tag::Arity(a));
                    j += 1;
                    stack.push(a);
                    continue 'putting;
                }
            };

            'popping: loop {
                match stack.last_mut() {
                    None => { break 'putting }
                    Some(k) => {
                        *k = *k - 1;
                        if *k != 0 { continue 'putting }
                    }
                }

                match stack.pop() {
                    Some(_) => { },
                    None => break 'popping
                }
            }
        };
        j
    }
}


#[inline(never)]
pub fn apply_e<'o, OS : Coroutine<Result<Tag, &'o [u8]>, Yield=(), Return=std::io::Result<Infallible>>>(n: u8, mut original_intros: u8, mut new_intros: u8, e: Expr, bindings: &BTreeMap<ExprVar, ExprEnv>, es: &mut std::pin::Pin<&mut OS>, cycled: &mut BTreeMap<ExprVar, u8>, stack: &mut Vec<ExprVar>, assignments: &mut Vec<ExprVar>) -> (u8, u8) {
    let depth = stack.len();
    if stack.len() > APPLY_DEPTH as usize { panic!("apply depth > {APPLY_DEPTH}: {n} {original_intros} {new_intros}"); }
    if PRINT_DEBUG { println!("{}@ n={} original={} new={} ez={:?}", "  ".repeat(depth), n, original_intros, new_intros, e); }
    let mut src = item_source(e);
    
    loop {
        match std::pin::pin!(&mut src).resume(()) {
            CoroutineState::Yielded(Ok(Tag::NewVar)) => {
                match bindings.get(&(n, original_intros)) {
                    None => {
                        if PRINT_DEBUG { println!("{}@ $ no binding for {:?}", "  ".repeat(depth), (n, original_intros)); }
                        // println!("original {original_intros} new {new_intros}");
                        if let Some(pos) = assignments.iter().position(|e| *e == (n, original_intros)) {
                            // println!("{}assignments _{} for {:?} (newvar)", "  ".repeat(depth), pos + 1, (n, original_intros));
                            es.as_mut().resume(Ok(Tag::VarRef(pos as _)));
                        } else {
                            es.as_mut().resume(Ok(Tag::NewVar));
                            new_intros += 1;
                            assignments.push((n, original_intros));
                        }
                        original_intros += 1;

                    }
                    Some(rhs) => {
                        if PRINT_DEBUG { println!("{}@ $ with bindings +{} {} for {:?}", "  ".repeat(depth), rhs.n, rhs.show(), (n, original_intros)); }
                        // println!("stack={stack:?}");
                        if let Some(introduced) = cycled.get(&(n, original_intros)) {
                            if PRINT_DEBUG { println!("{}cycled _{} for {:?} (newvar)", "  ".repeat(depth), *introduced+1, (n, original_intros)) };
                            es.as_mut().resume(Ok(Tag::VarRef(*introduced)));
                            // println!("nv cycled contains {:?}", (n, original_intros));
                        } else if stack.contains(&(n, original_intros)) {
                            cycled.insert((n, original_intros), new_intros);
                            // println!("nv cycled insert {:?}", (n, original_intros));
                            es.as_mut().resume(Ok(Tag::NewVar));
                            new_intros += 1;
                        } else {
                            stack.push((n, original_intros));
                            let (evars_, nvars_) = apply_e(rhs.n, rhs.v, new_intros, rhs.subsexpr(), bindings, es, cycled, stack, assignments);
                            new_intros = nvars_;
                            stack.pop();
                        }
                        original_intros += 1;
                    }
                }
            }
            CoroutineState::Yielded(Ok(Tag::VarRef(i))) => {
                match bindings.get(&(n, i)) {
                    None => {
                        if PRINT_DEBUG { println!("{}@ _{} no binding for {:?}", "  ".repeat(depth), i+1, (n, i)); }
                        if let Some(pos) = assignments.iter().position(|e| *e == (n, i)) {
                            // println!("{}assignments _{} for {:?} (ref)", "  ".repeat(depth), pos+1, (n, i));
                            es.as_mut().resume(Ok(Tag::VarRef(pos as u8)));
                        } else {
                            es.as_mut().resume(Ok(Tag::NewVar));
                            new_intros += 1;
                            assignments.push((n, i)); // this can't be right in general
                        }
                    }
                    Some(rhs) => {
                        if PRINT_DEBUG { println!("{}@ _{} with binding +{} {} for {:?}", "  ".repeat(depth), i+1, rhs.n, rhs.show(), (n, i)); }
                        // println!("stack={stack:?}");
                        if let Some(introduced) = cycled.get(&(n, i)) {
                            // println!("vr cycled contains {:?}", (n, i));
                            if PRINT_DEBUG { println!("{}cycled _{} for {:?} (ref) rhs={}", "  ".repeat(depth), *introduced+1, (n, i), rhs.show()); }
                            es.as_mut().resume(Ok(Tag::VarRef(*introduced)));
                        } else if stack.contains(&(n, i)) {
                            // println!("vr cycled insert {:?}", (n, i));
                            cycled.insert((n, i), new_intros);
                            es.as_mut().resume(Ok(Tag::NewVar));
                            new_intros += 1;
                        } else {
                            stack.push((n, i));
                            let (evars_, nvars_) = apply_e(rhs.n, rhs.v, new_intros, rhs.subsexpr(), bindings, es, cycled, stack, assignments);
                            new_intros = nvars_;
                            stack.pop();
                        }
                    }
                }
            }
            CoroutineState::Yielded(Ok(Tag::SymbolSize(_))) => { unsafe { std::hint::unreachable_unchecked() } }
            CoroutineState::Yielded(Ok(Tag::Arity(a))) => {
                if PRINT_DEBUG { println!("{}@ [{}]", "  ".repeat(depth), a); }
                es.as_mut().resume(Ok(Tag::Arity(a)));
            }
            CoroutineState::Yielded(Err(s)) => {
                if PRINT_DEBUG { println!("{}@ \"{}\"", "  ".repeat(depth), unsafe { std::str::from_utf8_unchecked(s) }); }
                es.as_mut().resume(Err(s));
            }
            CoroutineState::Complete(c) => {
                return (original_intros, new_intros) 
            }
        }
    }
}

mod tests {
    use std::ops::*;
    use crate::{item_sink, Expr, Tag, parse, item_source};

    #[test]
    fn basic_sink() {

        let mut v = vec![];
        let mut snk = item_sink(&mut v);
        for x in [Ok(Tag::Arity(2)), Err(&b"foo"[..]), Err(&b"bar"[..])].into_iter() { 
            std::pin::pin!(&mut snk).resume(x); 
        };
        drop(snk);
        let e = Expr{ ptr: v.as_mut_ptr() };
        assert_eq!(format!("{:?}", e), "(foo bar)");
        println!("e {:?}", e);
    }

    #[test]
    fn basic_source() {
        let mut xv = parse!(r"[3] [2] f $ [3] h $ [2] f a _2");
        let x = Expr { ptr: xv.as_mut_ptr() };
        
        let mut src = item_source(x);
        let mut k = 0;
        use Tag::*;
        let mut expected: [Result<Tag, &[u8]>; _] = [
            Ok(Arity(3)),
            Ok(Arity(2)),
            Err(&[102]),
            Ok(NewVar),
            Ok(Arity(3)),
            Err(&[104]),
            Ok(NewVar),
            Ok(Arity(2)),
            Err(&[102]),
            Err(&[97]),
            Ok(VarRef(1)),
        ]; 
        loop { 
            match std::pin::pin!(&mut src).resume(()) {
                CoroutineState::Yielded(i) => { println!("{i:?}"); assert_eq!(i, expected[k]); k += 1; }
                CoroutineState::Complete(c) => { println!("{c:?}"); assert_eq!(c, 15); break }
            }
        }
    }
}