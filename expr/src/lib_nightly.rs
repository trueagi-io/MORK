use crate::{APPLY_DEPTH, Expr, ExprEnv, ExprVar, PRINT_DEBUG, Tag, byte_item, item_byte};
use std::collections::BTreeMap;
use std::fmt::{Debug, Formatter};
use std::hash::Hasher;
use std::ptr::slice_from_raw_parts;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum SourceItem<'a> {
    Tag(Tag),
    Symbol(&'a [u8]),
}

pub struct OwnedSourceItem([u8; 64]);

impl OwnedSourceItem {
    fn size(&self) -> usize {
        match byte_item(self.0[0]) {
            Tag::NewVar => 1,
            Tag::VarRef(_) => 1,
            Tag::SymbolSize(s) => 1 + s as usize,
            Tag::Arity(_) => 1,
        }
    }
}

impl PartialEq<Self> for OwnedSourceItem {
    fn eq(&self, other: &Self) -> bool {
        self.0[0] == other.0[0] && {
            match byte_item(self.0[0]) {
                Tag::NewVar => true,
                Tag::VarRef(_) => true,
                Tag::SymbolSize(s) => self.0[1..(s as usize) + 1] == other.0[1..(s as usize) + 1],
                Tag::Arity(_) => true,
            }
        }
    }
}

impl Eq for OwnedSourceItem {}

impl std::hash::Hash for OwnedSourceItem {
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_u8(self.0[0]);
        if let Tag::SymbolSize(s) = byte_item(self.0[0]) {
            state.write(&self.0[1..(s as usize) + 1])
        }
    }
}

impl<'a> From<&'a str> for OwnedSourceItem {
    fn from(value: &'a str) -> Self {
        let vb = value.as_bytes();
        assert!(vb.len() < 64);
        let mut i = OwnedSourceItem([0; 64]);
        i.0[0] = item_byte(Tag::SymbolSize(vb.len() as u8));
        i.0[1..1 + vb.len()].copy_from_slice(value.as_bytes());
        i
    }
}

impl Debug for OwnedSourceItem {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_str(crate::serialize(&self.0[..self.size()]).as_str())
    }
}

/// Hand-rolled push-struct replacement for the old `item_sink` coroutine.
/// Each `push` writes one `SourceItem` to `target` and accumulates the byte
/// count in `written`, which equals the old coroutine's `Return` value once the
/// expression is complete. The old coroutine kept an arity stack to detect
/// completion (it returned `Ok(j)` when the stack emptied); that stack was dead
/// for the only consumer, `apply_e`, which never reads the sink's completion
/// (the macro discards the count). So the push model drops the stack and just
/// emits per item: +1 byte per tag, +1+len bytes per symbol.
pub struct ItemSink<'w, W: std::io::Write> {
    target: &'w mut W,
    written: usize,
}

pub fn item_sink<W: std::io::Write>(target: &mut W) -> ItemSink<'_, W> {
    ItemSink { target, written: 0 }
}

impl<'w, W: std::io::Write> ItemSink<'w, W> {
    #[inline]
    pub fn push(&mut self, i: SourceItem) -> std::io::Result<()> {
        match i {
            SourceItem::Tag(Tag::SymbolSize(_)) => {
                panic!("sink uses Symbol(&[u8]) for symbols, gotten Tag::SymbolSize")
            }
            // NewVar | VarRef | Arity: a single tag byte.
            SourceItem::Tag(tag) => {
                self.target.write_all(&[item_byte(tag)])?;
                self.written += 1;
            }
            SourceItem::Symbol(slice) => {
                let l = slice.len();
                debug_assert!(l < 64);
                self.target.write_all(&[item_byte(Tag::SymbolSize(l as _))])?;
                self.target.write_all(slice)?;
                self.written += 1 + l;
            }
        }
        Ok(())
    }

    #[inline]
    pub fn finish(self) -> std::io::Result<usize> {
        Ok(self.written)
    }
}

/// Hand-rolled iterator replacement for the old `item_source` coroutine.
/// Yields the identical `SourceItem` sequence from the structure walk of a flat
/// byte-encoded `Expr`. `j` holds the consumed length and equals the old
/// coroutine's `Return` value once `next` has returned `None`.
pub struct ItemSource<'a> {
    e: Expr,
    stack: smallvec::SmallVec<[u8; 64]>,
    pub j: usize,
    done: bool,
    _marker: core::marker::PhantomData<&'a ()>,
}

pub fn item_source<'a>(e: Expr) -> ItemSource<'a> {
    ItemSource {
        e,
        stack: smallvec::SmallVec::new(),
        j: 0,
        done: false,
        _marker: core::marker::PhantomData,
    }
}

impl<'a> Iterator for ItemSource<'a> {
    type Item = SourceItem<'a>;

    #[inline]
    fn next(&mut self) -> Option<SourceItem<'a>> {
        if self.done {
            return None;
        }
        let item = match unsafe { byte_item(*self.e.ptr.byte_add(self.j)) } {
            Tag::NewVar => {
                self.j += 1;
                self.after_item();
                SourceItem::Tag(Tag::NewVar)
            }
            Tag::VarRef(r) => {
                self.j += 1;
                self.after_item();
                SourceItem::Tag(Tag::VarRef(r))
            }
            Tag::SymbolSize(s) => {
                let slice =
                    unsafe { &*slice_from_raw_parts(self.e.ptr.byte_add(self.j + 1), s as usize) };
                self.j += s as usize + 1;
                self.after_item();
                SourceItem::Symbol(slice)
            }
            Tag::Arity(a) => {
                self.j += 1;
                if a > 0 {
                    self.stack.push(a);
                } else {
                    self.after_item();
                }
                SourceItem::Tag(Tag::Arity(a))
            }
        };
        Some(item)
    }
}

impl<'a> ItemSource<'a> {
    // replicate the old 'popping loop: descend through completed siblings/ancestors;
    // set done=true when the stack empties (old `break 'putting`).
    #[inline]
    fn after_item(&mut self) {
        loop {
            match self.stack.last_mut() {
                None => {
                    self.done = true;
                    return;
                }
                Some(k) => {
                    *k -= 1;
                    if *k != 0 {
                        return;
                    }
                }
            }
            self.stack.pop();
        }
    }
}

#[inline(never)]
pub fn apply_e<'o, W: std::io::Write>(
    n: u8,
    mut original_intros: u8,
    mut new_intros: u8,
    e: Expr,
    bindings: &BTreeMap<ExprVar, ExprEnv>,
    es: &mut ItemSink<'o, W>,
    cycled: &mut BTreeMap<ExprVar, u8>,
    stack: &mut Vec<ExprVar>,
    assignments: &mut Vec<ExprVar>,
) -> (u8, u8) {
    let depth = stack.len();
    if stack.len() > APPLY_DEPTH as usize {
        panic!("apply depth > {APPLY_DEPTH}: {n} {original_intros} {new_intros}");
    }
    if PRINT_DEBUG {
        println!(
            "{}@ n={} original={} new={} ez={:?}",
            "  ".repeat(depth),
            n,
            original_intros,
            new_intros,
            e
        );
    }
    let mut src = item_source(e);

    loop {
        match src.next() {
            Some(SourceItem::Tag(Tag::NewVar)) => {
                match bindings.get(&(n, original_intros)) {
                    None => {
                        if PRINT_DEBUG {
                            println!(
                                "{}@ $ no binding for {:?}",
                                "  ".repeat(depth),
                                (n, original_intros)
                            );
                        }
                        // println!("original {original_intros} new {new_intros}");
                        if let Some(pos) =
                            assignments.iter().position(|e| *e == (n, original_intros))
                        {
                            // println!("{}assignments _{} for {:?} (newvar)", "  ".repeat(depth), pos + 1, (n, original_intros));
                            let _ = es.push(SourceItem::Tag(Tag::VarRef(pos as _)));
                        } else {
                            let _ = es.push(SourceItem::Tag(Tag::NewVar));
                            new_intros += 1;
                            assignments.push((n, original_intros));
                        }
                        original_intros += 1;
                    }
                    Some(rhs) => {
                        if PRINT_DEBUG {
                            println!(
                                "{}@ $ with bindings +{} {} for {:?}",
                                "  ".repeat(depth),
                                rhs.n,
                                rhs.show(),
                                (n, original_intros)
                            );
                        }
                        // println!("stack={stack:?}");
                        if let Some(introduced) = cycled.get(&(n, original_intros)) {
                            if PRINT_DEBUG {
                                println!(
                                    "{}cycled _{} for {:?} (newvar)",
                                    "  ".repeat(depth),
                                    *introduced + 1,
                                    (n, original_intros)
                                )
                            };
                            let _ = es.push(SourceItem::Tag(Tag::VarRef(*introduced)));
                            // println!("nv cycled contains {:?}", (n, original_intros));
                        } else if stack.contains(&(n, original_intros)) {
                            cycled.insert((n, original_intros), new_intros);
                            // println!("nv cycled insert {:?}", (n, original_intros));
                            let _ = es.push(SourceItem::Tag(Tag::NewVar));
                            new_intros += 1;
                        } else {
                            stack.push((n, original_intros));
                            let (_, nvars_) = apply_e(
                                rhs.n,
                                rhs.v,
                                new_intros,
                                rhs.subsexpr(),
                                bindings,
                                es,
                                cycled,
                                stack,
                                assignments,
                            );
                            new_intros = nvars_;
                            stack.pop();
                        }
                        original_intros += 1;
                    }
                }
            }
            Some(SourceItem::Tag(Tag::VarRef(i))) => {
                match bindings.get(&(n, i)) {
                    None => {
                        if PRINT_DEBUG {
                            println!(
                                "{}@ _{} no binding for {:?}",
                                "  ".repeat(depth),
                                i + 1,
                                (n, i)
                            );
                        }
                        if let Some(pos) = assignments.iter().position(|e| *e == (n, i)) {
                            // println!("{}assignments _{} for {:?} (ref)", "  ".repeat(depth), pos+1, (n, i));
                            let _ = es.push(SourceItem::Tag(Tag::VarRef(pos as u8)));
                        } else {
                            let _ = es.push(SourceItem::Tag(Tag::NewVar));
                            new_intros += 1;
                            assignments.push((n, i)); // this can't be right in general
                        }
                    }
                    Some(rhs) => {
                        if PRINT_DEBUG {
                            println!(
                                "{}@ _{} with binding +{} {} for {:?}",
                                "  ".repeat(depth),
                                i + 1,
                                rhs.n,
                                rhs.show(),
                                (n, i)
                            );
                        }
                        // println!("stack={stack:?}");
                        if let Some(introduced) = cycled.get(&(n, i)) {
                            // println!("vr cycled contains {:?}", (n, i));
                            if PRINT_DEBUG {
                                println!(
                                    "{}cycled _{} for {:?} (ref) rhs={}",
                                    "  ".repeat(depth),
                                    *introduced + 1,
                                    (n, i),
                                    rhs.show()
                                );
                            }
                            let _ = es.push(SourceItem::Tag(Tag::VarRef(*introduced)));
                        } else if stack.contains(&(n, i)) {
                            // println!("vr cycled insert {:?}", (n, i));
                            cycled.insert((n, i), new_intros);
                            let _ = es.push(SourceItem::Tag(Tag::NewVar));
                            new_intros += 1;
                        } else {
                            stack.push((n, i));
                            let (_, nvars_) = apply_e(
                                rhs.n,
                                rhs.v,
                                new_intros,
                                rhs.subsexpr(),
                                bindings,
                                es,
                                cycled,
                                stack,
                                assignments,
                            );
                            new_intros = nvars_;
                            stack.pop();
                        }
                    }
                }
            }
            Some(SourceItem::Tag(Tag::SymbolSize(_))) => unsafe {
                std::hint::unreachable_unchecked()
            },
            Some(SourceItem::Tag(Tag::Arity(a))) => {
                if PRINT_DEBUG {
                    println!("{}@ [{}]", "  ".repeat(depth), a);
                }
                let _ = es.push(SourceItem::Tag(Tag::Arity(a)));
            }
            Some(SourceItem::Symbol(s)) => {
                if PRINT_DEBUG {
                    println!("{}@ \"{}\"", "  ".repeat(depth), unsafe {
                        std::str::from_utf8_unchecked(s)
                    });
                }
                let _ = es.push(SourceItem::Symbol(s));
            }
            None => return (original_intros, new_intros),
        }
    }
}

/// NOTE : expr_env, stack, assignments are cleared when this is called
#[inline(always)]
pub fn unifiable_reuse_state(
    left: Expr,
    right: Expr,
    expr_env: &mut Vec<(ExprEnv, ExprEnv)>,
    stack: &mut Vec<(u8, u8)>,
    assignments: &mut Vec<(u8, u8)>,
) -> bool {
    let void = std::io::sink();
    unifies_reuse_state(left, right, void, expr_env, stack, assignments)
}

/// Unified value will be written to `sink`<br>
/// `sink` can be in an indeterminate shape if the unification fails.<br>
/// NOTE : expr_env, stack, assignments are cleared when this is called
#[inline(always)]
pub fn unifies_reuse_state<W>(
    left: Expr,
    right: Expr,
    mut sink: W,
    expr_env: &mut Vec<(ExprEnv, ExprEnv)>,
    mut stack: &mut Vec<(u8, u8)>,
    mut assignments: &mut Vec<(u8, u8)>,
) -> bool
where
    W: std::io::Write,
{
    expr_env.clear();
    expr_env.extend_from_slice(&[(ExprEnv::new(0, left), ExprEnv::new(1, right))]);
    let out = match crate::unify(expr_env) {
        Ok(bindings) => {
            crate::apply_e_clears_stacks_and_cycles_check!(
                0,
                0,
                0,
                left,
                &bindings,
                sink,
                stack,
                assignments
            )
            .2
        }
        Err(_) => false,
    };
    expr_env.clear();
    out
}

#[cfg(test)]
mod tests {
    use crate::{Expr, ExprZipper, SourceItem, Tag, item_byte, item_sink, item_source, parse};
    use std::ops::{Coroutine, CoroutineState};

    /// Frozen verbatim copy of the pre-conversion coroutine `item_sink`, kept as
    /// the differential reference. The production sink is now `ItemSink::push`;
    /// `ref_item_sink_coroutine` is the old receiving-coroutine the conversion
    /// replaced. Both must emit byte-identical output for the same item stream.
    fn ref_item_sink_coroutine<W: std::io::Write>(
        target: &mut W,
    ) -> impl Coroutine<SourceItem<'_>, Yield = (), Return = std::io::Result<usize>> {
        #[coroutine]
        move |mut i: SourceItem| {
            let mut stack: smallvec::SmallVec<[u8; 64]> = smallvec::SmallVec::new();
            let mut j = 0;
            loop {
                match i {
                    SourceItem::Tag(tag) => match tag {
                        Tag::NewVar => {
                            target.write_all(&[item_byte(tag)])?;
                            j += 1;
                        }
                        Tag::VarRef(_) => {
                            target.write_all(&[item_byte(tag)])?;
                            j += 1;
                        }
                        Tag::SymbolSize(_) => {
                            panic!("sink uses Err(&[u8]) for symbols, gotten Tag::SymbolSize")
                        }
                        Tag::Arity(a) => {
                            target.write_all(&[item_byte(tag)])?;
                            j += 1;
                            if a > 0 {
                                stack.push(a);
                                i = yield ();
                                continue;
                            }
                        }
                    },
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
                        None => return Ok(j),
                        Some(k) => {
                            *k = *k - 1;
                            if *k != 0 {
                                break 'popping;
                            }
                        }
                    }

                    match stack.pop() {
                        Some(_) => {}
                        None => break 'popping,
                    }
                }
                i = yield ();
            }
        }
    }

    // Adversarial + ground expr corpus exercising every apply_e/codec path:
    // ground nesting, coreference ($x..$x), varrefs at the intro boundary,
    // deep nesting, and self-referential shapes that drive the cycle check.
    // `parse!` is const and only takes literals, so each case is spelled out.
    fn diff_corpus() -> Vec<Vec<u8>> {
        vec![
            parse!(r"a").to_vec(),                                   // bare symbol
            parse!(r"[2] f a").to_vec(),                             // ground
            parse!(r"[3] f a b").to_vec(),                           // ground
            parse!(r"$").to_vec(),                                   // lone NewVar
            parse!(r"[2] f $").to_vec(),                             // var under arity
            parse!(r"[3] f $ _1").to_vec(),                          // coreference $x .. $x
            parse!(r"[3] $ _1 _1").to_vec(),                         // triple coreference
            parse!(r"[4] $ $ _1 _2").to_vec(),                       // two distinct vars, reused
            parse!(r"[3] [2] f $ [3] h $ [2] f a _2").to_vec(),      // nested, varref at boundary
            parse!(r"[2] [2] [2] [2] [2] f a b c d e").to_vec(),     // deep nesting
            parse!(r"[3] [3] h $ _1 [3] h $ _1 [3] h a b").to_vec(), // repeated subterm shapes
            parse!(r"[2] [3] f $ _1 [2] g _1").to_vec(),             // varref reused across siblings
        ]
    }

    /// Differential A: the apply_e emit path's *sink*, toggled old vs new.
    /// Stream each corpus expr's SourceItems through both the new push sink and
    /// the frozen reference coroutine sink; assert byte-identical output and an
    /// identical final byte count.
    #[test]
    fn diff_item_sink_old_vs_new() {
        for mut bytes in diff_corpus() {
            let e = Expr {
                ptr: bytes.as_mut_ptr(),
            };

            // collect the item stream once (item_source is checked separately).
            let items: Vec<SourceItem> = item_source(e).collect();

            // new push sink
            let mut new_out = Vec::<u8>::new();
            let mut snk = item_sink(&mut new_out);
            for &it in &items {
                snk.push(it).unwrap();
            }
            let new_count = snk.finish().unwrap();

            // frozen reference coroutine sink
            let mut ref_out = Vec::<u8>::new();
            let mut rs = ref_item_sink_coroutine(&mut ref_out);
            let mut ref_count = 0usize;
            for &it in &items {
                match std::pin::pin!(&mut rs).resume(it) {
                    CoroutineState::Yielded(()) => {}
                    CoroutineState::Complete(r) => {
                        ref_count = r.unwrap();
                        break;
                    }
                }
            }
            drop(rs);

            assert_eq!(
                new_out, ref_out,
                "sink bytes differ for expr {:?}",
                crate::serialize(&bytes)
            );
            assert_eq!(new_count, ref_out.len(), "new sink byte count off");
            // the reference completes only when its arity stack empties; for a
            // fully-formed expr that is exactly at the last item, so counts match.
            assert_eq!(new_count, ref_count, "byte counts differ");
        }
    }

    /// Differential B: end-to-end apply_e emit (the production `apply_e` macro via
    /// `unifies_reuse_state`, now backed by the new ItemSink) cross-checked against
    /// the independent `Expr::unify` path (which substitutes via `apply_bindings`,
    /// a separate code path). Unify each corpus expr with itself; both reconstructions
    /// must produce byte-identical substituted output.
    #[test]
    fn diff_apply_e_emit_vs_unify_oracle() {
        let corpus = diff_corpus();
        for mut bytes in corpus {
            let e = Expr {
                ptr: bytes.as_mut_ptr(),
            };

            // production apply_e path: unify e with a renamed copy of itself, emit.
            let mut copy = bytes.clone();
            let e2 = Expr {
                ptr: copy.as_mut_ptr(),
            };
            let mut expr_env = vec![];
            let mut stack = vec![];
            let mut assignments = vec![];
            let mut prod_out = Vec::<u8>::new();
            let ok = crate::unifies_reuse_state(
                e,
                e2,
                &mut prod_out,
                &mut expr_env,
                &mut stack,
                &mut assignments,
            );
            assert!(ok, "self-unification should succeed for {:?}", crate::serialize(&bytes));

            // independent oracle: Expr::unify writes the unified left via apply_bindings.
            let mut copy2 = bytes.clone();
            let e3 = Expr {
                ptr: copy2.as_mut_ptr(),
            };
            let oracle_buf = vec![0u8; 4096];
            let oracle_e = Expr {
                ptr: oracle_buf.leak().as_mut_ptr(),
            };
            let mut oz = ExprZipper::new(oracle_e);
            e.unify(e3, &mut oz).expect("oracle unify failed");

            let prod_e = Expr {
                ptr: prod_out.as_mut_ptr(),
            };
            assert_eq!(
                format!("{:?}", prod_e),
                format!("{:?}", oracle_e),
                "apply_e emit disagrees with unify oracle for {:?}",
                crate::serialize(&bytes)
            );
        }
    }

    #[test]
    fn basic_sink() {
        let mut v = vec![];
        let mut snk = item_sink(&mut v);
        for x in [
            SourceItem::Tag(Tag::Arity(2)),
            SourceItem::Symbol(&b"foo"[..]),
            SourceItem::Symbol(&b"bar"[..]),
        ]
        .into_iter()
        {
            snk.push(x).unwrap();
        }
        drop(snk);
        let e = Expr {
            ptr: v.as_mut_ptr(),
        };
        assert_eq!(format!("{:?}", e), "(foo bar)");
        println!("e {:?}", e);
    }

    #[test]
    fn basic_source() {
        let mut xv = parse!(r"[3] [2] f $ [3] h $ [2] f a _2");
        let x = Expr {
            ptr: xv.as_mut_ptr(),
        };

        let mut src = item_source(x);
        let mut k = 0;
        use Tag::*;
        let expected: [SourceItem; _] = [
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
            match src.next() {
                Some(i) => {
                    println!("{i:?}");
                    assert_eq!(i, expected[k]);
                    k += 1;
                }
                None => {
                    let c = src.j;
                    println!("{c:?}");
                    assert_eq!(c, 15);
                    break;
                }
            }
        }
    }

    #[test]
    fn sink_saturate() {
        // The push model has no mid-stream completion: `push` writes one item and
        // never signals that the expression is full (the old coroutine returned
        // `Complete` when its arity stack emptied, but that completion was dead for
        // the only consumer). So push all three items, then read the total via
        // `finish`: 1 (Arity) + 1+3 (foo) + 1+3 (bar) = 9 bytes.
        let mut v = vec![];
        let mut snk = item_sink(&mut v);
        for x in [
            SourceItem::Tag(Tag::Arity(2)),
            SourceItem::Symbol(&b"foo"[..]),
            SourceItem::Symbol(&b"bar"[..]),
        ]
        .into_iter()
        {
            snk.push(x).unwrap();
        }
        assert_eq!(snk.finish().unwrap(), 9);
        let e = Expr {
            ptr: v.as_mut_ptr(),
        };
        assert_eq!(format!("{:?}", e), "(foo bar)");
        println!("e {:?}", e);
    }
}
