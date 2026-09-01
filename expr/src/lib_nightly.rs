use std::collections::BTreeMap;
use std::convert::Infallible;
use std::fmt::{Debug, Formatter};
use std::hash::Hasher;
use std::io::Write;
use std::ops::{Coroutine, CoroutineState};
use std::ptr::slice_from_raw_parts;
use crate::{byte_item, item_byte, traverseh, Expr, ExprEnv, ExprVar, ExprZipper, Tag, APPLY_DEPTH, PRINT_DEBUG, Bindings};

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
            Tag::Fuzzy(_) => { 1 }
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
                Tag::Fuzzy(_) => { true }
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

/// Receives the encoded items produced by [`apply_e`].
pub trait ItemSink {
    fn tag(&mut self, tag: Tag);
    fn symbol(&mut self, bytes: &[u8]);
    /// Receives a complete, already-encoded ground subterm, and may append it in bulk.
    ///
    /// Item-for-item equivalent to feeding the span through `tag`/`symbol`, which is what licenses
    /// the bulk copy: a ground subterm re-encodes to exactly its own bytes.
    fn ground(&mut self, bytes: &[u8]);
}

impl<T: ItemSink + ?Sized> ItemSink for &mut T {
    #[inline(always)]
    fn tag(&mut self, tag: Tag) {
        (**self).tag(tag)
    }
    #[inline(always)]
    fn symbol(&mut self, bytes: &[u8]) {
        (**self).symbol(bytes)
    }
    #[inline(always)]
    fn ground(&mut self, bytes: &[u8]) {
        (**self).ground(bytes)
    }
}

/// Discards emitted items while preserving [`apply_e`]'s traversal and accounting: the walk still
/// follows bindings, counts intros and does cycle bookkeeping, and only the output storage is gone.
pub struct NullSink;

impl ItemSink for NullSink {
    #[inline(always)]
    fn tag(&mut self, _tag: Tag) {}
    #[inline(always)]
    fn symbol(&mut self, _bytes: &[u8]) {}
    #[inline(always)]
    fn ground(&mut self, _bytes: &[u8]) {}
}

/// Appends the encoded expression to a byte vector.
pub struct VecSink<'a>(pub &'a mut Vec<u8>);

impl ItemSink for VecSink<'_> {
    #[inline(always)]
    fn tag(&mut self, tag: Tag) {
        self.0.push(item_byte(tag));
    }
    #[inline(always)]
    fn symbol(&mut self, bytes: &[u8]) {
        debug_assert!(bytes.len() < 64);
        self.0.push(item_byte(Tag::SymbolSize(bytes.len() as _)));
        self.0.extend_from_slice(bytes);
    }
    #[inline(always)]
    fn ground(&mut self, bytes: &[u8]) {
        self.0.extend_from_slice(bytes);
    }
}

/// Writes the encoded expression into a caller-owned buffer, tracking how far it got.
///
/// The buffer must be large enough; callers here hand over a `1 << 32` scratch region, exactly as
/// they did when this was a `std::io::Cursor`.
pub struct SliceSink<'a> {
    pub buf: &'a mut [u8],
    pub at: usize,
}

impl<'a> SliceSink<'a> {
    #[inline(always)]
    pub fn new(buf: &'a mut [u8]) -> Self {
        Self { buf, at: 0 }
    }
    /// Bytes written so far.
    #[inline(always)]
    pub fn position(&self) -> usize {
        self.at
    }
}

impl ItemSink for SliceSink<'_> {
    #[inline(always)]
    fn tag(&mut self, tag: Tag) {
        self.buf[self.at] = item_byte(tag);
        self.at += 1;
    }
    #[inline(always)]
    fn symbol(&mut self, bytes: &[u8]) {
        debug_assert!(bytes.len() < 64);
        self.buf[self.at] = item_byte(Tag::SymbolSize(bytes.len() as _));
        self.at += 1;
        self.buf[self.at..self.at + bytes.len()].copy_from_slice(bytes);
        self.at += bytes.len();
    }
    #[inline(always)]
    fn ground(&mut self, bytes: &[u8]) {
        self.buf[self.at..self.at + bytes.len()].copy_from_slice(bytes);
        self.at += bytes.len();
    }
}

/// Pull-based reader over an expression's items.
///
/// [`apply_e`] no longer uses this -- it scans the bytes directly, which is far cheaper than a
/// resume per item. It stays because `experiments/eval` genuinely needs the pull shape: it reads
/// one item, then decides what to do next from its own state, which a push sink cannot express.
pub fn item_source<'a>(e: Expr) -> impl Coroutine<(), Yield=SourceItem<'a>, Return=usize> {
    #[coroutine] move || {
        let mut stack: smallvec::SmallVec<[u8; 64]> = smallvec::SmallVec::new();
        let mut j: usize = 0;
        'putting: loop {
            match unsafe { byte_item(*e.ptr.byte_add(j)) } {
                tag @ (Tag::NewVar | Tag::VarRef(_) | Tag::Fuzzy(_)) => { j += 1; yield SourceItem::Tag(tag) }
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

/// Instantiate `e` under `bindings`, feeding the result to `sink`.
///
/// Returns the running `(original_intros, new_intros)`; `cycled` is left non-empty iff a variable
/// was reached through itself, which is the caller's occurs check.
///
/// The walk is a straight left-to-right scan of `e`'s bytes. Because the encoding is prefix-free
/// and self-delimiting, knowing where the term ends needs one counter rather than an arity stack:
/// `owed` starts at 1, every item settles one slot, and an `Arity(a)` opens `a` more. The scan
/// stops at exactly the end of `e`, so a subterm pointer into a larger buffer stays in bounds --
/// the same guarantee the stack gave, in a register instead of a `SmallVec`.
#[inline(never)]
/// [`apply_e`] specialized to the shape the pattern pass applies: the pattern's own distinct
/// variables, in order, into a null sink -- returning `(oi, ni)`, or `None` when a cycle was cut.
///
/// Written out, that call was applying a synthetic expression of `oi` `NewVar`s, and every part of it
/// is decidable from the bindings except one:
///
///   - an UNBOUND variable emits one fresh intro. Arithmetic: it is the first sight of a distinct
///     key, so no dedup scan is needed, only the record that later references find.
///   - a variable bound to a GROUND value contributes nothing whatsoever. A stamped value holds no
///     variable ([`ExprEnv::ground_skip`]), so it introduces no intro, it cannot lie on the
///     expansion stack, and it cannot close a cycle -- a cycle needs a variable to lead back
///     through. Nothing to walk.
///   - a variable bound to a NON-ground value is the residual work, and it is handed to `apply_e`
///     itself, one variable at a time, so the arms, stack and cycle bookkeeping are the same code
///     the general pass used rather than a reimplementation of it.
///
/// So what is left computationally is exactly: one map lookup and one stamp read per pattern
/// variable, plus `apply_e` over the values that actually contain variables. There is no synthetic
/// expression -- which also means no arity byte, so a pattern with more than 63 variables needs no
/// special case.
pub fn pattern_cycles_and_intros(
    pat_var_count: u8,
    bindings: &Bindings,
    stack: &mut Vec<ExprVar>,
    assignments: &mut Vec<ExprVar>,
) -> Option<(u8, u8)> {
    stack.clear();
    assignments.clear();
    let mut cycled: BTreeMap<ExprVar, u8> = BTreeMap::new();
    let mut new_intros = 0u8;
    for v in 0..pat_var_count {
        match bindings.get(&(0, v)) {
            None => {
                // First sight of this key, so it emits a fresh intro; the record is what makes a
                // later reference to it emit a back-reference instead of another intro.
                assignments.push((0, v));
                new_intros += 1;
            }
            Some(value) if value.ground_stamp() != 0 => {}
            Some(_) => {
                let one_newvar = Expr {
                    ptr: crate::NEW_VAR_EXPR_BYTES.as_ptr().cast_mut(),
                };
                let (_, ni) = apply_e(
                    0,
                    v,
                    new_intros,
                    one_newvar,
                    bindings,
                    &mut NullSink,
                    &mut cycled,
                    stack,
                    assignments,
                );
                new_intros = ni;
                if !cycled.is_empty() {
                    return None;
                }
            }
        }
    }
    Some((pat_var_count, new_intros))
}

pub fn apply_e<S: ItemSink>(n: u8, mut original_intros: u8, mut new_intros: u8, e: Expr, bindings: &Bindings, sink: &mut S, cycled: &mut BTreeMap<ExprVar, u8>, stack: &mut Vec<ExprVar>, assignments: &mut Vec<ExprVar>) -> (u8, u8) {
    let depth = stack.len();
    if stack.len() > APPLY_DEPTH as usize { panic!("apply depth > {APPLY_DEPTH}: {n} {original_intros} {new_intros}"); }
    if PRINT_DEBUG { println!("{}@ n={} original={} new={} ez={:?}", "  ".repeat(depth), n, original_intros, new_intros, e); }

    let mut at = 0usize;
    let mut owed = 1usize;
    while owed > 0 {
        let b = unsafe { *e.ptr.byte_add(at) };
        at += 1;
        owed -= 1;
        match byte_item(b) {
            Tag::NewVar => {
                match bindings.get(&(n, original_intros)) {
                    None => {
                        if PRINT_DEBUG { println!("{}@ $ no binding for {:?}", "  ".repeat(depth), (n, original_intros)); }
                        // println!("original {original_intros} new {new_intros}");
                        if let Some(pos) = assignments.iter().position(|e| *e == (n, original_intros)) {
                            // println!("{}assignments _{} for {:?} (newvar)", "  ".repeat(depth), pos + 1, (n, original_intros));
                            sink.tag(Tag::VarRef(pos as _));
                        } else {
                            sink.tag(Tag::NewVar);
                            new_intros += 1;
                            assignments.push((n, original_intros));
                        }
                        original_intros += 1;

                    }
                    Some(rhs) => {
                        if PRINT_DEBUG { println!("{}@ $ with bindings +{} {} for {:?}", "  ".repeat(depth), rhs.n, rhs.show(), (n, original_intros)); }
                        // println!("stack={stack:?}");
                        // A ground binding needs no walk: it re-encodes to exactly its own bytes,
                        // introduces no variable, and cannot lie on the application stack or in
                        // `cycled` -- either would require a variable inside it -- so those probes
                        // are guaranteed misses. One bulk copy replaces the recursion.
                        if rhs.ground_skip != 0 {
                            sink.ground(unsafe { &*slice_from_raw_parts(rhs.base.ptr.add(rhs.offset as usize), rhs.ground_skip as usize) });
                        } else if let Some(introduced) = cycled.get(&(n, original_intros)) {
                            if PRINT_DEBUG { println!("{}cycled _{} for {:?} (newvar)", "  ".repeat(depth), *introduced+1, (n, original_intros)) };
                            sink.tag(Tag::VarRef(*introduced));
                            // println!("nv cycled contains {:?}", (n, original_intros));
                        } else if stack.contains(&(n, original_intros)) {
                            cycled.insert((n, original_intros), new_intros);
                            // println!("nv cycled insert {:?}", (n, original_intros));
                            sink.tag(Tag::NewVar);
                            new_intros += 1;
                        } else {
                            stack.push((n, original_intros));
                            let (evars_, nvars_) = apply_e(rhs.n, rhs.v, new_intros, rhs.subsexpr(), bindings, sink, cycled, stack, assignments);
                            new_intros = nvars_;
                            stack.pop();
                        }
                        original_intros += 1;
                    }
                }
            }
            Tag::VarRef(i) => {
                match bindings.get(&(n, i)) {
                    None => {
                        if PRINT_DEBUG { println!("{}@ _{} no binding for {:?}", "  ".repeat(depth), i+1, (n, i)); }
                        if let Some(pos) = assignments.iter().position(|e| *e == (n, i)) {
                            // println!("{}assignments _{} for {:?} (ref)", "  ".repeat(depth), pos+1, (n, i));
                            sink.tag(Tag::VarRef(pos as u8));
                        } else {
                            sink.tag(Tag::NewVar);
                            new_intros += 1;
                            assignments.push((n, i)); // this can't be right in general
                        }
                    }
                    Some(rhs) => {
                        if PRINT_DEBUG { println!("{}@ _{} with binding +{} {} for {:?}", "  ".repeat(depth), i+1, rhs.n, rhs.show(), (n, i)); }
                        // println!("stack={stack:?}");
                        // A ground binding needs no walk: it re-encodes to exactly its own bytes,
                        // introduces no variable, and cannot lie on the application stack or in
                        // `cycled` -- either would require a variable inside it -- so those probes
                        // are guaranteed misses. One bulk copy replaces the recursion.
                        if rhs.ground_skip != 0 {
                            sink.ground(unsafe { &*slice_from_raw_parts(rhs.base.ptr.add(rhs.offset as usize), rhs.ground_skip as usize) });
                        } else if let Some(introduced) = cycled.get(&(n, i)) {
                            // println!("vr cycled contains {:?}", (n, i));
                            if PRINT_DEBUG { println!("{}cycled _{} for {:?} (ref) rhs={}", "  ".repeat(depth), *introduced+1, (n, i), rhs.show()); }
                            sink.tag(Tag::VarRef(*introduced));
                        } else if stack.contains(&(n, i)) {
                            // println!("vr cycled insert {:?}", (n, i));
                            cycled.insert((n, i), new_intros);
                            sink.tag(Tag::NewVar);
                            new_intros += 1;
                        } else {
                            stack.push((n, i));
                            let (evars_, nvars_) = apply_e(rhs.n, rhs.v, new_intros, rhs.subsexpr(), bindings, sink, cycled, stack, assignments);
                            new_intros = nvars_;
                            stack.pop();
                        }
                    }
                }
            }
            Tag::SymbolSize(s) => {
                let slice = unsafe { &*slice_from_raw_parts(e.ptr.byte_add(at), s as usize) };
                at += s as usize;
                if PRINT_DEBUG { println!("{}@ \"{}\"", "  ".repeat(depth), unsafe { std::str::from_utf8_unchecked(slice) }); }
                sink.symbol(slice);
            }
            Tag::Arity(a) => {
                if PRINT_DEBUG { println!("{}@ [{}]", "  ".repeat(depth), a); }
                owed += a as usize;
                sink.tag(Tag::Arity(a));
            }
            tag @ Tag::Fuzzy(f) => {
                if PRINT_DEBUG { println!("{}@ \"{{{:0>4b}}}\"", "  ".repeat(depth), f); }
                sink.tag(tag);
            },            
        }
    }
    (original_intros, new_intros)
}
/// NOTE : expr_env, stack, assignments are cleared when this is called
#[inline(always)]
pub fn unifiable_reuse_state(left : Expr, right : Expr, mut expr_env : &mut Vec<(ExprEnv, ExprEnv)>, mut stack : &mut Vec<(u8, u8)>, mut assignments : &mut Vec<(u8, u8)>)->bool {
    unifies_reuse_state(left, right, &mut NullSink, expr_env, stack, assignments)
}

/// Unified value will be written to `sink`<br>
/// `sink` can be in an indeterminate shape if the unification fails.<br>
/// NOTE : expr_env, stack, assignments are cleared when this is called
#[inline(always)]
pub fn unifies_reuse_state<S : ItemSink>(
    left            : Expr,
    right           : Expr,
    mut sink        : &mut S,
    mut expr_env    : &mut Vec<(ExprEnv, ExprEnv)>,
    mut stack       : &mut Vec<(u8, u8)>,
    mut assignments : &mut Vec<(u8, u8)>
)-> bool {
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
    use std::collections::BTreeMap;
    use crate::{apply_e, Expr, NullSink, SliceSink, VecSink, parse};

    /// Instantiate under no bindings. With nothing bound, `apply_e` is the identity on a
    /// well-formed expression, which makes it a byte-exact check on the walk and the sinks.
    fn identity(e: Expr, out: &mut Vec<u8>) -> (u8, u8) {
        let bindings = crate::Bindings::new();
        let mut cycled = BTreeMap::new();
        let (mut stack, mut assignments) = (Vec::new(), Vec::new());
        let mut sink = VecSink(out);
        apply_e(0, 0, 0, e, &bindings, &mut sink, &mut cycled, &mut stack, &mut assignments)
    }

    #[test]
    fn vec_sink_round_trips() {
        let mut xv = parse!(r"[3] [2] f $ [3] h $ [2] f a _2");
        let x = Expr { ptr: xv.as_mut_ptr() };
        let mut out = Vec::new();
        let (oi, ni) = identity(x, &mut out);
        assert_eq!(format!("{:?}", Expr { ptr: out.as_mut_ptr() }), format!("{:?}", x));
        assert_eq!(&out[..], &xv[..], "identity application must reproduce the input bytes");
        assert_eq!((oi, ni), (2, 2), "two variables introduced, two carried out");
    }

    /// The former `item_source` used an arity stack to find where the term ended; the `owed`
    /// counter has to find that same end. A subterm handed to `apply_e` is a bare pointer into a
    /// larger buffer, so overrunning by even one item would read a neighbouring expression.
    #[test]
    fn scan_stops_at_end_of_term() {
        let mut xv = parse!(r"[3] [2] f $ [3] h $ [2] f a _2");
        let len = xv.len();
        let mut buf = xv.to_vec();
        buf.extend_from_slice(&parse!(r"[2] should not be reached"));
        let x = Expr { ptr: buf.as_mut_ptr() };

        let mut out = Vec::new();
        identity(x, &mut out);
        assert_eq!(out.len(), len, "walk must stop at the end of the first term");
        assert_eq!(&out[..], &xv[..]);
    }

    #[test]
    fn nullsink_agrees_with_vecsink_on_counts() {
        let mut xv = parse!(r"[3] [2] f $ [3] h $ [2] f a _2");
        let x = Expr { ptr: xv.as_mut_ptr() };

        let mut out = Vec::new();
        let with_bytes = identity(x, &mut out);

        let bindings = crate::Bindings::new();
        let mut cycled = BTreeMap::new();
        let (mut stack, mut assignments) = (Vec::new(), Vec::new());
        let without = apply_e(0, 0, 0, x, &bindings, &mut NullSink, &mut cycled, &mut stack, &mut assignments);

        assert_eq!(with_bytes, without, "discarding the bytes must not change the counts");
    }

    #[test]
    fn slice_sink_reports_length() {
        let mut xv = parse!(r"[2] [2] f a b");
        let x = Expr { ptr: xv.as_mut_ptr() };

        let mut room = [0u8; 64];
        let bindings = crate::Bindings::new();
        let mut cycled = BTreeMap::new();
        let (mut stack, mut assignments) = (Vec::new(), Vec::new());
        let mut sink = SliceSink::new(&mut room);
        apply_e(0, 0, 0, x, &bindings, &mut sink, &mut cycled, &mut stack, &mut assignments);
        let n = sink.position();

        assert_eq!(n, xv.len());
        assert_eq!(&room[..n], &xv[..]);
    }
}
