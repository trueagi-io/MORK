use std::collections::BTreeMap;
use std::convert::Infallible;
use std::fmt::{Debug, Formatter};
use std::hash::Hasher;
use std::io::Write;
use std::ops::{Coroutine, CoroutineState};
use std::ptr::slice_from_raw_parts;
use crate::{byte_item, item_byte, traverseh, Expr, ExprEnv, ExprVar, ExprZipper, Tag, APPLY_DEPTH, PRINT_DEBUG};

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum SourceItem<'a> {
    Tag(Tag),
    Symbol(&'a[u8]),
}

pub struct OwnedSourceItem([u8; 64]);

impl OwnedSourceItem {
    fn size(&self) -> usize {
        match byte_item(self.0[0]) {
            Tag::NewVar => { 1 }
            Tag::VarRef(_) => { 1 }
            Tag::SymbolSize(s) => { 1 + s as usize }
            Tag::Arity(_) => { 1 }
        }
    }
}

impl PartialEq<Self> for OwnedSourceItem {
    fn eq(&self, other: &Self) -> bool {
        self.0[0] == other.0[0] && {
            match byte_item(self.0[0]) {
                Tag::NewVar => { true }
                Tag::VarRef(_) => { true }
                Tag::SymbolSize(s) => { self.0[1..(s as usize)+1] == other.0[1..(s as usize)+1] }
                Tag::Arity(_) => { true }
            }
        }
    }
}

impl Eq for OwnedSourceItem {}

impl std::hash::Hash for OwnedSourceItem {
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_u8(self.0[0]);
        if let Tag::SymbolSize(s) = byte_item(self.0[0]) {
            state.write(&self.0[1..(s as usize)+1])
        }
    }
}

impl <'a> From<&'a str> for OwnedSourceItem {
    fn from(value: &'a str) -> Self {
        let vb = value.as_bytes();
        assert!(vb.len() < 64);
        let mut i = OwnedSourceItem([0; 64]);
        i.0[0] = item_byte(Tag::SymbolSize(vb.len() as u8));
        i.0[1..1+vb.len()].copy_from_slice(value.as_bytes());
        i
    }
}

impl Debug for OwnedSourceItem {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_str(crate::serialize(&self.0[..self.size()]).as_str())
    }
}

pub fn item_sink<W: std::io::Write>(target: &mut W) -> impl Coroutine<SourceItem, Yield=(), Return=std::io::Result<usize>> {
    #[coroutine] move |mut i: SourceItem| {
        let mut stack: smallvec::SmallVec<[u8; 64]> = smallvec::SmallVec::new();
        let mut j = 0;
        loop {
            match i {
                SourceItem::Tag(tag) => {
                    match tag {
                        Tag::NewVar => {
                            target.write_all(&[item_byte(tag)])?;
                            j += 1;
                        }
                        Tag::VarRef(_) => {
                            target.write_all(&[item_byte(tag)])?;
                            j += 1;
                        }
                        Tag::SymbolSize(_) => { panic!("sink uses Err(&[u8]) for symbols, gotten Tag::SymbolSize") }
                        Tag::Arity(a) => {
                            target.write_all(&[item_byte(tag)])?;
                            j += 1;
                            if a > 0 {
                                stack.push(a);
                                i = yield ();
                                continue;
                            }
                        }
                    }
                }
                SourceItem::Symbol(slice) => {
                    let l = slice.len();
                    debug_assert!(l < 64);
                    j += 1 + l;
                    target.write_all(&[item_byte(Tag::SymbolSize(l as _))])?;
                    target.write_all(slice)?;
                }
            }

            'popping: loop {
                match stack.last_mut() {
                    None => { return Ok(j) }
                    Some(k) => {
                        *k = *k - 1;
                        if *k != 0 {
                            break 'popping
                        }
                    }
                }

                match stack.pop() {
                    Some(_) => { },
                    None => break 'popping
                }
            }
            i = yield ();
        }
    }
}

pub fn item_source<'a>(e: Expr) -> impl Coroutine<(), Yield=SourceItem<'a>, Return=usize> {
    #[coroutine] move || {
        let mut stack: smallvec::SmallVec<[u8; 64]> = smallvec::SmallVec::new();
        let mut j: usize = 0;
        'putting: loop {
            match unsafe { byte_item(*e.ptr.byte_add(j)) } {
                Tag::NewVar => { j += 1; yield SourceItem::Tag(Tag::NewVar) }
                Tag::VarRef(r) => { j += 1; yield SourceItem::Tag(Tag::VarRef(r)) }
                Tag::SymbolSize(s) => {
                    let slice = unsafe { &*slice_from_raw_parts(e.ptr.byte_add(j + 1), s as usize) };
                    yield SourceItem::Symbol(slice);
                    j += s as usize + 1;
                }
                Tag::Arity(a) => {
                    yield SourceItem::Tag(Tag::Arity(a));
                    j += 1;
                    if a > 0 {
                        stack.push(a);
                        continue 'putting;
                    }
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
pub fn apply_e<'o, OS : Coroutine<SourceItem<'o>, Yield=(), Return=std::io::Result<usize>>>(
    //                                                     [Remy] :
    n                   : u8,                           // Identifies the expression being interpretted.
    mut original_intros : u8,                           // The number of NewVars __read__ so from a source expression stream,
    mut new_intros      : u8,                           // The number of NewVars __written__ to the output.
    e                   : Expr,                         // the expression that will be interpretted as an instructon stream.
    bindings            : &BTreeMap<ExprVar, ExprEnv>,  // These bindings are made using the `unify` function.
    es                  : &mut std::pin::Pin<&mut OS>,  // This is the output expression stream.
    cycled              : &mut BTreeMap<ExprVar, u8>,   // this records all detected cycles found when evaluating. The current behavior is that when a cycle is encountered a NewVar is written.
    stack               : &mut Vec<ExprVar>,            // Used to catch cycles.
    assignments         : &mut Vec<ExprVar>             // This records when a NewVar is written (and isn't cyclic)
) -> (u8, u8) {
    // [Remy] :
    //   The key to understanding this function is it "calls" the input expression as a "routine", and the binding expressions are "subroutines".
    //   What does this mean? probably the best metaphor would be that the bindings are like a library of procedures, and the first procedure to call is the first expression `e`.
    //
    //   The pair '(n, original_intros)` to __identify__ bindings. 
    //   Note, since bindings is immutable it serves to lookup bindings that may not be from the original source expression.
    //   This pair is also used to in conjunction with the `stack` to identify if there is a cycle.
    //   This is done by pushing the pair to the `stack`, and if the same pair is found again, it means we started a new stream from a __binding__,
    //   and that binding eventually spawned itself again. This is effectively the occurs check, but done at application time instead of at binding time.


    // [Remy] :
    //   This variable is used exculsively when PRINT_DEBUG is on. It does not affect the logic of the apply_e behavior.
    let depth = stack.len();
    if stack.len() > APPLY_DEPTH as usize { panic!("apply depth > {APPLY_DEPTH}: {n} {original_intros} {new_intros}"); }
    if PRINT_DEBUG { println!("{}@ n={} original={} new={} ez={:?}", "  ".repeat(depth), n, original_intros, new_intros, e); }
    
    // [Remy] :
    //   `n` identifies source expression `e`.
    //   `e` is now interpretted as a stream of instructions. termination of this function is determined by reaching the end of this stream.
    let mut src = item_source(e);

    loop {
        match std::pin::pin!(&mut src).resume(()) {
            // [Remy] :
            //   It took me a while to grasp that __at least one key__ from the bindings must be the same as the
            //   initial `n` that represents the identity of the initial expression.
            //   I've done my best to avoid describing the logic of unify and apply_e without talking about MORK execs, but it actually serves as
            //   the best example of why it to behaves this way.
            //
            //   MORK rough exec shape : (exec <ground-priority> <patterns> <templates>)
            //
            //   When a MORK exec runs, it does pattern matching on its patterns, then uses those binds on the template.
            //   since the exec is an expression, the whole expression is given a singular id (for example 0).
            //   The patterns are split up into sub expressions, but each sub expression is still given the same expr id (0).
            //   The reason is that they share the same introduction variables, NewVars. In other words they have the same binding context!
            //
            //   However, when a product zipper is made to be matched with each pattern sub expression, each value in the product is a different expression.
            //   Since they are they do not share the same binding context, the need different IDs, one for each, and distinct from the exec (!= 0).
            //
            //   When the two sides are unified, we get bindings, but we use them on the templates.
            //   The templates share the same binding context as the patterns, because they are from the same expression.
            //   In the case of MORK execs, the first bindings we look up are the bindings associated with the patterns,
            //   because the expression we are substituting is the template, and they share the same (0).
            //
            //   Unfortunately, __there is an extra complication__. the patterns and templates also share the same `original_intros`.
            //   This means you need to `apply_e` on the patterns first, in order to compute the original_intros value in the result.
            //
            //   So, if you are running this on the patterns, the first binding to match with `Some` will be on a `NewVar`,
            //   But if you do this on a template, it will be in the `VarRef`` branch. 
            CoroutineState::Yielded(SourceItem::Tag(Tag::NewVar)) => {
                match bindings.get(&(n, original_intros)) {
                    None => {
                        if PRINT_DEBUG { println!("{}@ $ no binding for {:?}", "  ".repeat(depth), (n, original_intros)); }
                        // println!("original {original_intros} new {new_intros}");


                        // [Remy] :
                        //   The `Some` condition below must be understood in terms of the recursive case.
                        //   One needs to consider a binding expression that was written earlier that wrote a NewVar, 
                        //   and it gets written again. then a reference is written instead of a to have sharing.
                        if let Some(pos) = assignments.iter().position(|e| *e == (n, original_intros)) {
                            // println!("{}assignments _{} for {:?} (newvar)", "  ".repeat(depth), pos + 1, (n, original_intros));
                            es.as_mut().resume(SourceItem::Tag(Tag::VarRef(pos as _)));
                        } else {
                            es.as_mut().resume(SourceItem::Tag(Tag::NewVar));
                            new_intros += 1;
                            assignments.push((n, original_intros));
                        }
                        original_intros += 1;

                    }
                    Some(rhs) => {
                        if PRINT_DEBUG { println!("{}@ $ with bindings +{} {} for {:?}", "  ".repeat(depth), rhs.n, rhs.show(), (n, original_intros)); }
                        // println!("stack={stack:?}");

                        
                        if let Some(introduced) = cycled.get(&(n, original_intros)) {
                            // [Remy] :
                            //   It's not entirely clear why the algorithm continues after having cycles, 
                            //   but I hazard to guess the logic here is that __if__ this was a rational tree, all cycles should share the same reference.

                            if PRINT_DEBUG { println!("{}cycled _{} for {:?} (newvar)", "  ".repeat(depth), *introduced+1, (n, original_intros)) };
                            es.as_mut().resume(SourceItem::Tag(Tag::VarRef(*introduced)));
                            // println!("nv cycled contains {:?}", (n, original_intros));

                        } else if stack.contains(&(n, original_intros)) {
                            // [Remy] : 
                            //   Similarly, __if__ we had rational tree semantics,there should still be an introductory variable.

                            cycled.insert((n, original_intros), new_intros);
                            // println!("nv cycled insert {:?}", (n, original_intros));
                            es.as_mut().resume(SourceItem::Tag(Tag::NewVar));
                            new_intros += 1;

                        } else {
                            // [Remy] :
                            //   Understanding this block is crucial. The subtlety here is that we push the aforementioned `(n, original_intros)` pair
                            //   in order to recognise what streams are live and waiting for the current stream to finish. `stack` and `cycles` are what makes this
                            //   a graph algorithm, this stack is effectively a variant of a "visited set". similar to strongly the SCC stack.
                            stack.push((n, original_intros));
                            // [Remy] :
                            //   The next subtle part is that we recurse __procedurally__ via `apply_e`, but __structurally__ via the `bindings`.
                            //   note how after leaving a readable trail with the `stack`, we call `apply_e` using 
                            //   the matched binding's equivalent of `n`(rhs.n) and `original_intros`(rhs.v).
                            //
                            //   This is the "subroutine" behavior
                            let (evars_, nvars_) = apply_e(rhs.n, rhs.v, new_intros, rhs.subsexpr(), bindings, es, cycled, stack, assignments);
                            new_intros = nvars_;
                            // [Remy] :
                            //   Once a substitution is complete, we don't want to accidentally cause future substitutions to think they are cycling prematurely. 
                            stack.pop();
                        }
                        original_intros += 1;
                    }
                }
            }
            // [Remy] :
            //   The main complexity of the code is explained above, and the following block is just a slightly modified version of the `NewVar` block
            CoroutineState::Yielded(SourceItem::Tag(Tag::VarRef(i))) => {
                match bindings.get(&(n, i)) {
                    None => {
                        if PRINT_DEBUG { println!("{}@ _{} no binding for {:?}", "  ".repeat(depth), i+1, (n, i)); }


                        if let Some(pos) = assignments.iter().position(|e| *e == (n, i)) {
                            // println!("{}assignments _{} for {:?} (ref)", "  ".repeat(depth), pos+1, (n, i));
                            es.as_mut().resume(SourceItem::Tag(Tag::VarRef(pos as u8)));
                        } else {
                            es.as_mut().resume(SourceItem::Tag(Tag::NewVar));
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


                            es.as_mut().resume(SourceItem::Tag(Tag::VarRef(*introduced)));
                        } else if stack.contains(&(n, i)) {
                            // println!("vr cycled insert {:?}", (n, i));
                            cycled.insert((n, i), new_intros);
                            es.as_mut().resume(SourceItem::Tag(Tag::NewVar));
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
            CoroutineState::Yielded(SourceItem::Tag(Tag::SymbolSize(_))) => { unsafe { std::hint::unreachable_unchecked() } }
            CoroutineState::Yielded(SourceItem::Tag(Tag::Arity(a))) => {
                if PRINT_DEBUG { println!("{}@ [{}]", "  ".repeat(depth), a); }
                es.as_mut().resume(SourceItem::Tag(Tag::Arity(a)));
            }
            CoroutineState::Yielded(SourceItem::Symbol(s)) => {
                if PRINT_DEBUG { println!("{}@ \"{}\"", "  ".repeat(depth), unsafe { std::str::from_utf8_unchecked(s) }); }
                es.as_mut().resume(SourceItem::Symbol(s));
            }
            CoroutineState::Complete(c) => {
                return (original_intros, new_intros) 
            }
        }
    }
}

/// NOTE : expr_env, stack, assignments are cleared when this is called
#[inline(always)]
pub fn unifiable_reuse_state(left : Expr, right : Expr, mut expr_env : &mut Vec<(ExprEnv, ExprEnv)>, mut stack : &mut Vec<(u8, u8)>, mut assignments : &mut Vec<(u8, u8)>)->bool {
    let mut void   = std::io::sink();
    unifies_reuse_state(left, right, void, expr_env, stack, assignments)
}

/// Unified value will be written to `sink`<br>
/// `sink` can be in an indeterminate shape if the unification fails.<br>
/// NOTE : expr_env, stack, assignments are cleared when this is called
#[inline(always)]
pub fn unifies_reuse_state<W>(
    left            : Expr,
    right           : Expr,
    mut sink        : W,
    mut expr_env    : &mut Vec<(ExprEnv, ExprEnv)>,
    mut stack       : &mut Vec<(u8, u8)>,
    mut assignments : &mut Vec<(u8, u8)>
)-> bool where W : std::io::Write {
    expr_env.clear();
    expr_env.extend_from_slice(&[(ExprEnv::new(0, left), ExprEnv::new(1, right))]);
    let out = match crate::unify(expr_env) {
        Ok(bindings) => crate::apply_e_clears_stacks_and_cycles_check!(0,0,0, left, &bindings, sink, stack, assignments).2,
        Err(_)       => false,
    };
    expr_env.clear();
    out
}




mod tests {
    use std::ops::*;
    use crate::{item_sink, Expr, Tag, parse, item_source, SourceItem};

    #[test]
    fn basic_sink() {

        let mut v = vec![];
        let mut snk = item_sink(&mut v);
        for x in [SourceItem::Tag(Tag::Arity(2)), SourceItem::Symbol(&b"foo"[..]), SourceItem::Symbol(&b"bar"[..])].into_iter() { 
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
        let mut expected: [SourceItem; _] = [
            SourceItem::Tag(Arity(3)),
            SourceItem::Tag(Arity(2)),
            SourceItem::Symbol(&[102]),
            SourceItem::Tag(NewVar),
            SourceItem::Tag(Arity(3)),
            SourceItem::Symbol(&[104]),
            SourceItem::Tag(NewVar),
            SourceItem::Tag(Arity(2)),
            SourceItem::Symbol(&[102]),
            SourceItem::Symbol(&[97]),
            SourceItem::Tag(VarRef(1)),
        ]; 
        loop { 
            match std::pin::pin!(&mut src).resume(()) {
                CoroutineState::Yielded(i) => { println!("{i:?}"); assert_eq!(i, expected[k]); k += 1; }
                CoroutineState::Complete(c) => { println!("{c:?}"); assert_eq!(c, 15); break }
            }
        }
    }

    #[test]
    fn sink_saturate() {
        let mut v = vec![];
        let mut snk = item_sink(&mut v);
        for x in [SourceItem::Tag(Tag::Arity(2)), SourceItem::Symbol(&b"foo"[..])].into_iter() {
            std::pin::pin!(&mut snk).resume(x);
        };
        match std::pin::pin!(&mut snk).resume(SourceItem::Symbol(&b"bar"[..])) {
            CoroutineState::Yielded(_) => unreachable!(), // we can't sink in more, our expression is complete
            CoroutineState::Complete(Err(_)) => unreachable!(), // we can always write into our sink
            CoroutineState::Complete(Ok(written)) => { assert_eq!(written, 9) }, // written 1 + 1+3 + 1+3 bytes
        }
        drop(snk);
        let e = Expr{ ptr: v.as_mut_ptr() };
        assert_eq!(format!("{:?}", e), "(foo bar)");
        println!("e {:?}", e);
    }
}
