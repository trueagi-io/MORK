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
        let mut j: usize = 0;
        let mut pending = 1usize;
        while pending != 0 {
            match unsafe { byte_item(*e.ptr.byte_add(j)) } {
                Tag::NewVar => {
                    j += 1;
                    pending -= 1;
                    yield SourceItem::Tag(Tag::NewVar)
                }
                Tag::VarRef(r) => {
                    j += 1;
                    pending -= 1;
                    yield SourceItem::Tag(Tag::VarRef(r))
                }
                Tag::SymbolSize(s) => {
                    let slice = unsafe { &*slice_from_raw_parts(e.ptr.byte_add(j + 1), s as usize) };
                    j += s as usize + 1;
                    pending -= 1;
                    yield SourceItem::Symbol(slice);
                }
                Tag::Arity(a) => {
                    j += 1;
                    pending = pending - 1 + usize::from(a);
                    yield SourceItem::Tag(Tag::Arity(a));
                }
            }
        }
        j
    }
}


#[inline(never)]
pub fn apply_e<'o, OS : Coroutine<SourceItem<'o>, Yield=(), Return=std::io::Result<usize>>>(n: u8, mut original_intros: u8, mut new_intros: u8, e: Expr, bindings: &BTreeMap<ExprVar, ExprEnv>, es: &mut std::pin::Pin<&mut OS>, cycled: &mut BTreeMap<ExprVar, u8>, stack: &mut Vec<ExprVar>, assignments: &mut Vec<ExprVar>) -> (u8, u8) {
    let depth = stack.len();
    if stack.len() > APPLY_DEPTH as usize { panic!("apply depth > {APPLY_DEPTH}: {n} {original_intros} {new_intros}"); }
    if PRINT_DEBUG { println!("{}@ n={} original={} new={} ez={:?}", "  ".repeat(depth), n, original_intros, new_intros, e); }
    let mut src = item_source(e);
    
    loop {
        match std::pin::pin!(&mut src).resume(()) {
            CoroutineState::Yielded(SourceItem::Tag(Tag::NewVar)) => {
                match bindings.get(&(n, original_intros)) {
                    None => {
                        if PRINT_DEBUG { println!("{}@ $ no binding for {:?}", "  ".repeat(depth), (n, original_intros)); }
                        // println!("original {original_intros} new {new_intros}");
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
                            if PRINT_DEBUG { println!("{}cycled _{} for {:?} (newvar)", "  ".repeat(depth), *introduced+1, (n, original_intros)) };
                            es.as_mut().resume(SourceItem::Tag(Tag::VarRef(*introduced)));
                            // println!("nv cycled contains {:?}", (n, original_intros));
                        } else if stack.contains(&(n, original_intros)) {
                            cycled.insert((n, original_intros), new_intros);
                            // println!("nv cycled insert {:?}", (n, original_intros));
                            es.as_mut().resume(SourceItem::Tag(Tag::NewVar));
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




#[cfg(test)]
mod tests {
    use std::ops::*;
    use crate::{byte_item, item_byte, item_sink, Expr, ExprEnv, Tag, parse, item_source, SourceItem};

    #[derive(Debug, Eq, PartialEq)]
    enum ReferenceItem {
        Tag(Tag),
        Symbol(Vec<u8>),
    }

    struct Lcg(u64);

    impl Lcg {
        fn next(&mut self) -> u32 {
            self.0 = self.0
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            (self.0 >> 32) as u32
        }

        fn below(&mut self, upper: u32) -> u32 {
            self.next() % upper
        }
    }

    fn generate_term(rng: &mut Lcg, depth: u8, introduced: &mut u8, out: &mut Vec<u8>) {
        let choice = if depth == 0 { rng.below(3) } else { rng.below(5) };
        match choice {
            0 if *introduced < 63 => {
                out.push(item_byte(Tag::NewVar));
                *introduced += 1;
            }
            1 if *introduced != 0 => {
                out.push(item_byte(Tag::VarRef(rng.below(u32::from(*introduced)) as u8)));
            }
            3 | 4 if depth != 0 => {
                let arity = rng.below(5) as u8;
                out.push(item_byte(Tag::Arity(arity)));
                for _ in 0..arity {
                    generate_term(rng, depth - 1, introduced, out);
                }
            }
            _ => {
                let size = rng.below(4) as u8 + 1;
                out.push(item_byte(Tag::SymbolSize(size)));
                for _ in 0..size {
                    out.push(b'a' + rng.below(26) as u8);
                }
            }
        }
    }

    fn reference_walk(bytes: &[u8], offset: usize, items: &mut Vec<ReferenceItem>) -> (usize, u8) {
        match byte_item(bytes[offset]) {
            Tag::NewVar => {
                items.push(ReferenceItem::Tag(Tag::NewVar));
                (1, 1)
            }
            Tag::VarRef(index) => {
                items.push(ReferenceItem::Tag(Tag::VarRef(index)));
                (1, 0)
            }
            Tag::SymbolSize(size) => {
                let end = offset + usize::from(size) + 1;
                items.push(ReferenceItem::Symbol(bytes[offset + 1..end].to_vec()));
                (usize::from(size) + 1, 0)
            }
            Tag::Arity(arity) => {
                items.push(ReferenceItem::Tag(Tag::Arity(arity)));
                let mut span = 1;
                let mut introductions = 0u8;
                for _ in 0..arity {
                    let (child_span, child_introductions) =
                        reference_walk(bytes, offset + span, items);
                    span += child_span;
                    introductions = introductions.checked_add(child_introductions).unwrap();
                }
                (span, introductions)
            }
        }
    }

    fn verify_scanners(case: usize, mut bytes: Vec<u8>) {
        let mut expected_items = Vec::new();
        let (span, _) = reference_walk(&bytes, 0, &mut expected_items);
        assert_eq!(span, bytes.len(), "reference span for case {case}");

        let expr = Expr { ptr: bytes.as_mut_ptr() };
        let mut expected_args = Vec::new();
        if let Tag::Arity(arity) = byte_item(bytes[0]) {
            let mut offset = 1usize;
            let mut introductions = 0u8;
            for _ in 0..arity {
                let mut ignored_items = Vec::new();
                let (child_span, child_introductions) =
                    reference_walk(&bytes, offset, &mut ignored_items);
                expected_args.push((offset as u32, introductions));
                offset += child_span;
                introductions = introductions.checked_add(child_introductions).unwrap();
            }
            assert_eq!(offset, bytes.len(), "argument spans for case {case}");
        }

        let mut actual_args = Vec::new();
        ExprEnv::new(7, expr).args(&mut actual_args);
        assert_eq!(actual_args.len(), expected_args.len(), "argument count for case {case}");
        for (actual, &(offset, introductions)) in actual_args.iter().zip(&expected_args) {
            assert_eq!(actual.n, 7, "argument namespace for case {case}");
            assert_eq!(actual.v, introductions, "argument introductions for case {case}");
            assert_eq!(actual.offset, offset, "argument offset for case {case}");
            assert_eq!(actual.base.ptr, expr.ptr, "argument base for case {case}");
        }

        let mut actual_items = Vec::new();
        let mut source = std::pin::pin!(item_source(expr));
        let consumed = loop {
            match source.as_mut().resume(()) {
                CoroutineState::Yielded(SourceItem::Tag(tag)) => {
                    actual_items.push(ReferenceItem::Tag(tag));
                }
                CoroutineState::Yielded(SourceItem::Symbol(symbol)) => {
                    actual_items.push(ReferenceItem::Symbol(symbol.to_vec()));
                }
                CoroutineState::Complete(consumed) => break consumed,
            }
        };
        assert_eq!(consumed, bytes.len(), "source span for case {case}");
        assert_eq!(actual_items, expected_items, "source items for case {case}");
    }

    #[test]
    fn generated_expression_scanners_match_recursive_reference() {
        verify_scanners(0, vec![item_byte(Tag::Arity(0))]);

        let mut deep = vec![item_byte(Tag::Arity(1)); 63];
        deep.extend([item_byte(Tag::SymbolSize(1)), b'x']);
        verify_scanners(1, deep);

        let mut wide = vec![item_byte(Tag::Arity(63))];
        wide.extend(std::iter::repeat_n(item_byte(Tag::NewVar), 63));
        verify_scanners(2, wide);

        let mut rng = Lcg(0x5eed_cafe_f00d_beef);
        for case in 3..4099 {
            let arity = rng.below(9) as u8;
            let mut bytes = vec![item_byte(Tag::Arity(arity))];
            let mut introduced = 0;
            for _ in 0..arity {
                generate_term(&mut rng, 6, &mut introduced, &mut bytes);
            }
            verify_scanners(case, bytes);
        }
    }

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
