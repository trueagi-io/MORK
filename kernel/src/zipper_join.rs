//! Zipper-native worst-case-optimal unification leapfrog over variable-width MORK terms.
//!
//! MORK answers a conjunctive query with the ProductZipper, a relation-at-a-time join that
//! materializes the intermediate product before pruning it. This module seeks directly instead,
//! variable-at-a-time, on the PathMap byte-trie: a join variable's value is a variable-width
//! subterm, found by descending the trie with `child_mask` + `descend_to_byte`, its boundary
//! tracked by a parse stack, and a stored variable in the data is a wildcard that unifies. No
//! domain is materialized. The term encoding, the unification, and the answer emit are
//! `mork_expr`'s own (`Tag`/`byte_item`, `unify`, `apply`); this module contributes the seek
//! order.
//!
//! Built bottom-up, each layer validated before the next: the byte-scan and the subterm parser
//! here, then the zipper subterm cursor, then the unification leapfrog, gated against the
//! ProductZipper.

use mork_expr::{byte_item, item_byte, unify, Expr, ExprEnv, ExprZipper, Tag};
use pathmap::utils::ByteMask;
use pathmap::zipper::{
    ReadZipperUntracked, Zipper, ZipperAbsolutePath, ZipperIteration, ZipperMoving, ZipperValues,
};
use pathmap::PathMap;
use std::collections::{BTreeMap, BTreeSet};
use std::panic::{catch_unwind, AssertUnwindSafe};

const QUERY_NS: u8 = 0;
const NEW_VAR_EXPR_BYTES: [u8; 1] = [item_byte(Tag::NewVar)];

/// The least byte present in `mask` that is `>= k`, or `None` if every set bit is below `k`.
/// `ByteMask::next_bit` returns the least bit strictly above its argument, so test `k` itself
/// first. This is the per-byte leapfrog seek on a trie node's children.
#[inline]
pub fn least_ge(mask: &ByteMask, k: u8) -> Option<u8> {
    if (mask.0[(k >> 6) as usize] >> (k & 63)) & 1 == 1 {
        Some(k)
    } else {
        mask.next_bit(k)
    }
}

/// Parse the first complete subterm at `bytes[0..]`, returning its byte length and whether it is
/// ground. The encoding is prefix-free: an `Arity(k)` consumes the next `k` subterms, a
/// `SymbolSize(s)` consumes `s` payload bytes, a `VarRef`/`NewVar` is one byte. Walking a "need one
/// more complete term" counter to zero gives the span. Panics on a truncated term.
#[inline]
fn parse_first_subterm(bytes: &[u8]) -> (usize, bool) {
    try_parse_first_subterm(bytes).expect("truncated encoded subterm")
}

fn try_parse_first_subterm(bytes: &[u8]) -> Option<(usize, bool)> {
    let mut i = 0usize;
    let mut remaining = 1usize;
    let mut ground = true;
    while remaining > 0 {
        let b = *bytes.get(i)?;
        i += 1;
        remaining -= 1;
        match byte_item(b) {
            Tag::Arity(arity) => remaining += arity as usize,
            Tag::VarRef(_) | Tag::NewVar => ground = false,
            Tag::SymbolSize(size) => {
                i = i.checked_add(size as usize)?;
                if i > bytes.len() {
                    return None;
                }
            }
        }
    }
    Some((i, ground))
}

/// Byte length of the first complete subterm at `bytes[0..]`.
pub fn first_subterm_len(bytes: &[u8]) -> usize {
    parse_first_subterm(bytes).0
}

/// Whether the first complete subterm at `bytes[0..]` is ground (contains no variable).
pub fn first_subterm_is_ground(bytes: &[u8]) -> bool {
    parse_first_subterm(bytes).1
}

/// One step of the incremental parse: consume byte `b`, updating how many complete subterms are
/// still owed (`subterms`) and how many raw symbol-payload bytes are still owed (`payload`). A
/// payload byte completes nothing; a tag byte completes one slot, then an `Arity(k)` owes `k` more
/// subterms and a `SymbolSize(s)` owes `s` payload bytes.
#[inline]
fn step_parse(b: u8, subterms: &mut usize, payload: &mut usize) {
    if *payload > 0 {
        *payload -= 1;
    } else {
        *subterms -= 1;
        match byte_item(b) {
            Tag::Arity(arity) => *subterms += arity as usize,
            Tag::SymbolSize(size) => *payload += size as usize,
            Tag::VarRef(_) | Tag::NewVar => {}
        }
    }
}

/// Whether `bytes` (from the column-start focus) spell exactly one complete subterm. Recomputed
/// per descent step; subterms are short, so the O(len) replay is cheap and keeps the navigation
/// free of incremental-state bugs.
#[inline]
fn is_complete(bytes: &[u8]) -> bool {
    let (mut subterms, mut payload) = (1usize, 0usize);
    for &b in bytes {
        step_parse(b, &mut subterms, &mut payload);
    }
    subterms == 0 && payload == 0
}

#[inline]
fn has_bit(mask: &ByteMask, b: u8) -> bool {
    (mask.0[(b >> 6) as usize] >> (b & 63)) & 1 == 1
}

/// A cursor over the complete variable-width subterms branching from a PathMap zipper's focus, in
/// ascending lexicographic order, with a leapfrog `seek`. This is the zipper-native replacement for
/// a materialized per-variable domain: it seeks on the live byte-trie instead of scanning a `Vec`.
///
/// `key` holds the bytes of the current subterm relative to the focus the cursor was built at
/// (its "floor"). The cursor descends with `descend_to_byte` and ascends with `ascend_byte`, never
/// above the floor (it stops when `key` is empty), so the zipper is left at the floor between
/// re-seeks and at the subterm boundary while positioned.
pub struct SubtermCursor<Z> {
    z: Z,
    key: Vec<u8>,
    at_end: bool,
    /// Values of the columns already descended past, below the zipper's creation
    /// focus. `descend_floor` locks the current subterm as a column value and
    /// lowers the floor into it (so the next enumeration is of the following
    /// column); `ascend_floor` restores it. This lets one cursor walk a factor's
    /// successive columns with the zipper HELD -- descended and ascended in place,
    /// never re-opened from the trie root (which is the join's dominant cost).
    floor_stack: Vec<Vec<u8>>,
}

impl<Z: Zipper + ZipperMoving> SubtermCursor<Z> {
    /// Build a cursor at the zipper's current focus. Not positioned until `first`/`seek` is called.
    pub fn new(z: Z) -> Self {
        SubtermCursor {
            z,
            key: Vec::new(),
            at_end: true,
            floor_stack: Vec::new(),
        }
    }

    /// Ascend back to the floor (column start), clearing the key.
    fn reset_to_floor(&mut self) {
        while self.key.pop().is_some() {
            self.z.ascend_byte();
        }
        self.at_end = false;
    }

    /// Lock the current complete subterm (the cursor's `key`) as a consumed column
    /// value: the floor descends into it so subsequent enumeration is of the NEXT
    /// column. The zipper stays put (it is already descended into `key`); only the
    /// floor bookkeeping moves. Pairs with `ascend_floor`.
    pub fn descend_floor(&mut self) {
        self.floor_stack.push(std::mem::take(&mut self.key));
        self.at_end = false;
    }

    /// Undo the most recent `descend_floor`: the floor rises back to this column
    /// and the cursor is repositioned at the value it held (its `key`), ready to
    /// advance via `next`. Requires the zipper to be back at this column's floor
    /// plus that value, which holds because a fully-exhausted deeper column
    /// leaves its cursor at its own floor (== this value's end).
    pub fn ascend_floor(&mut self) {
        self.key = self
            .floor_stack
            .pop()
            .expect("ascend_floor without a matching descend_floor");
        self.at_end = false;
    }

    /// Whether the current focus (after consuming every column) carries a stored
    /// value: the factor's fact is present at this full binding.
    pub fn has_value(&self) -> bool
    where
        Z: ZipperValues<()>,
    {
        self.z.value().is_some()
    }

    /// Descend the least child at each step until the key forms a complete subterm. Returns false
    /// if a node runs out of children before completion (malformed/empty branch).
    fn complete_leftmost(&mut self) -> bool {
        while !is_complete(&self.key) {
            let mask = self.z.child_mask();
            match least_ge(&mask, 0) {
                Some(b) => {
                    self.z.descend_to_byte(b);
                    self.key.push(b);
                }
                None => return false,
            }
        }
        true
    }

    /// From the current complete subterm, move to the least subterm strictly greater: ascend until a
    /// level offers a larger sibling, take the least such, then complete leftmost. False = exhausted.
    fn backtrack_then_leftmost(&mut self) -> bool {
        loop {
            let Some(last) = self.key.pop() else {
                return false;
            };
            self.z.ascend_byte();
            let mask = self.z.child_mask();
            if let Some(b) = mask.next_bit(last) {
                self.z.descend_to_byte(b);
                self.key.push(b);
                return self.complete_leftmost();
            }
        }
    }

    /// Position at the least subterm.
    pub fn first(&mut self) {
        self.reset_to_floor();
        if !self.complete_leftmost() {
            self.at_end = true;
        }
    }

    /// Advance to the next subterm.
    pub fn next(&mut self) {
        if self.at_end {
            return;
        }
        if !self.backtrack_then_leftmost() {
            self.at_end = true;
        }
    }

    /// The current subterm bytes, or `None` when exhausted.
    pub fn key(&self) -> Option<&[u8]> {
        if self.at_end {
            None
        } else {
            Some(&self.key)
        }
    }

    pub fn at_end(&self) -> bool {
        self.at_end
    }

    /// Position at the least subterm `>= target`. `target` must itself be a complete subterm (the
    /// leapfrog only ever seeks to another factor's bound subterm value). Because the encoding is
    /// prefix-free and `target` is complete, a completed descent matches `target` exactly; any
    /// divergence is handled by taking the least larger child (then completing leftmost) or, when no
    /// larger child exists at that level, backtracking to an ancestor that offers one.
    pub fn seek(&mut self, target: &[u8]) {
        self.reset_to_floor();
        let mut ti = 0usize;
        loop {
            if is_complete(&self.key) {
                self.at_end = false;
                return;
            }
            let mask = self.z.child_mask();
            if ti < target.len() {
                let t = target[ti];
                if has_bit(&mask, t) {
                    self.z.descend_to_byte(t);
                    self.key.push(t);
                    ti += 1;
                    continue;
                }
                match mask.next_bit(t) {
                    Some(b) => {
                        self.z.descend_to_byte(b);
                        self.key.push(b);
                        if !self.complete_leftmost() {
                            self.at_end = true;
                        }
                        return;
                    }
                    None => {
                        if !self.backtrack_then_leftmost() {
                            self.at_end = true;
                        }
                        return;
                    }
                }
            } else {
                if !self.complete_leftmost() {
                    self.at_end = true;
                }
                return;
            }
        }
    }
}

/// Leapfrog intersection of several subterm cursors: the subterm values present in ALL of them, in
/// ascending order. The textbook leapfrog step seeks every cursor to the current maximum key; when
/// they all agree, that key is in the intersection, then one cursor steps past it. Each step either
/// emits a match and advances, or jumps a cursor forward, so it terminates and is worst-case-optimal
/// on the cursors' sizes.
fn intersect<Z: Zipper + ZipperMoving>(cursors: &mut [SubtermCursor<Z>]) -> Vec<Vec<u8>> {
    let mut out = Vec::new();
    if cursors.is_empty() {
        return out;
    }
    for c in cursors.iter_mut() {
        c.first();
        if c.at_end() {
            return out;
        }
    }
    loop {
        let max = cursors
            .iter()
            .map(|c| c.key().unwrap())
            .max()
            .unwrap()
            .to_vec();
        let mut all_match = true;
        for c in cursors.iter_mut() {
            if c.key().unwrap() != max.as_slice() {
                c.seek(&max);
                if c.at_end() {
                    return out;
                }
                if c.key().unwrap() != max.as_slice() {
                    all_match = false;
                }
            }
        }
        if all_match {
            out.push(max);
            cursors[0].next();
            if cursors[0].at_end() {
                return out;
            }
        }
    }
}

/// The `(namespace, variable)` key of `mork_expr::unify`'s bindings map. `mork_expr` keeps its
/// `ExprVar = (u8, u8)` alias private, so the concrete pair type is named again here.
type BindingKey = (u8, u8);
type Bindings = BTreeMap<BindingKey, ExprEnv>;

/// A materialized encoded term plus the query-variable intro count before it in the original body.
/// The bytes stay in MORK's native encoding; unification and substitution operate through
/// [`ExprEnv`] views over them.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EncodedTerm {
    pub bytes: Vec<u8>,
    pub intro: u8,
}

impl EncodedTerm {
    fn new(bytes: Vec<u8>, intro: u8) -> Self {
        EncodedTerm { bytes, intro }
    }

    fn expr(&self) -> Expr {
        expr_from_bytes(&self.bytes)
    }

    fn tag(&self) -> Tag {
        byte_item(self.bytes[0])
    }

    fn is_ground(&self) -> bool {
        expr_is_ground(self.expr())
    }

    fn is_nonground_compound(&self) -> bool {
        matches!(self.tag(), Tag::Arity(_)) && !self.is_ground()
    }

    fn min_var_pos(&self, var_pos: &[usize]) -> Option<usize> {
        min_var_pos_in_expr(self.expr(), self.intro, var_pos)
    }
}

/// One query argument column in a factor. Top-level variables are exposed so the leapfrog order can
/// seek them directly; every structured or ground column stays as native encoded bytes.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum FactorColumn {
    Var(usize),
    Term(EncodedTerm),
}

impl FactorColumn {
    fn min_var_pos(&self, var_pos: &[usize]) -> Option<usize> {
        match self {
            FactorColumn::Var(v) => Some(var_pos[*v]),
            FactorColumn::Term(term) => term.min_var_pos(var_pos),
        }
    }

    /// Whether this column is a compound containing a variable, the shape the routing gate
    /// inspects.
    pub fn is_nonground_compound(&self) -> bool {
        matches!(self, FactorColumn::Term(term) if term.is_nonground_compound())
    }
}

/// A query factor: its seek prefix in the PathMap, and every column in syntactic order. The body
/// parser emits the arity byte alone as the prefix, with the relation head as column 0 (a direct
/// construction may bake a ground head into the prefix instead, at the cost of never matching a
/// wildcard stored head). Ground columns stay columns so they can unify with stored data variables
/// at their trie position.
#[derive(Clone, Debug)]
pub struct Factor {
    pub prefix: Vec<u8>,
    pub cols: Vec<FactorColumn>,
}

impl Factor {
    pub fn var_cols(prefix: Vec<u8>, cols: Vec<usize>) -> Self {
        Factor {
            prefix,
            cols: cols.into_iter().map(FactorColumn::Var).collect(),
        }
    }
}

fn expr_from_bytes(bytes: &[u8]) -> Expr {
    Expr {
        ptr: bytes.as_ptr().cast_mut(),
    }
}

fn expr_span_len(expr: Expr) -> usize {
    unsafe { expr.span().as_ref().unwrap().len() }
}

fn expr_is_ground(expr: Expr) -> bool {
    let mut ez = ExprZipper::new(expr);
    loop {
        match ez.tag() {
            Tag::NewVar | Tag::VarRef(_) => return false,
            Tag::SymbolSize(_) | Tag::Arity(_) => {}
        }
        if !ez.next() {
            return true;
        }
    }
}

fn expr_children(term: &EncodedTerm) -> Option<Vec<EncodedTerm>> {
    let Tag::Arity(arity) = term.tag() else {
        return None;
    };
    let mut children = Vec::with_capacity(arity as usize);
    if arity == 0 {
        return Some(children);
    }
    let mut ez = ExprZipper::new(term.expr());
    let mut intro = term.intro;
    for _ in 0..arity {
        if !ez.next_child() {
            return None;
        }
        let child_expr = ez.subexpr();
        let len = expr_span_len(child_expr);
        let start = ez.loc;
        let child_bytes = term.bytes.get(start..start + len)?.to_vec();
        children.push(EncodedTerm::new(child_bytes, intro));
        let next_intro = intro as usize + child_expr.newvars();
        if next_intro > u8::MAX as usize {
            return None;
        }
        intro = next_intro as u8;
    }
    Some(children)
}

fn validate_vars_and_count(expr: Expr) -> Option<usize> {
    let mut ez = ExprZipper::new(expr);
    let mut intros = 0usize;
    loop {
        match ez.tag() {
            Tag::NewVar => {
                intros = intros.checked_add(1)?;
                if intros > u8::MAX as usize {
                    return None;
                }
            }
            Tag::VarRef(i) if i as usize >= intros => return None,
            Tag::VarRef(_) | Tag::SymbolSize(_) | Tag::Arity(_) => {}
        }
        if !ez.next() {
            return Some(intros);
        }
    }
}

fn min_var_pos_in_expr(expr: Expr, intro_start: u8, var_pos: &[usize]) -> Option<usize> {
    let mut ez = ExprZipper::new(expr);
    let mut intro = intro_start as usize;
    let mut min_pos: Option<usize> = None;
    loop {
        let var = match ez.tag() {
            Tag::NewVar => {
                let id = intro;
                intro += 1;
                Some(id)
            }
            Tag::VarRef(i) => Some(i as usize),
            Tag::SymbolSize(_) | Tag::Arity(_) => None,
        };
        if let Some(id) = var {
            let pos = var_pos[id];
            min_pos = Some(min_pos.map_or(pos, |current| current.min(pos)));
        }
        if !ez.next() {
            return min_pos;
        }
    }
}

/// Ground worst-case-optimal join over PathMap factors, seeking variable-width subterms directly on
/// the byte-trie with no materialized domain. `var_order` lists the global variables in binding
/// order; it must be compatible with every factor's column order (each factor's variables, in
/// `var_order`, occur in column order), which holds for any acyclic query under a suitable order.
/// Cyclic queries that admit no compatible order are handled by re-indexing in a later layer.
///
/// Returns one row per answer: `row[v]` is the bound subterm bytes for global variable `v`.
///
/// COMPLETENESS CONTRACT: this is an EXACT-match join. It is complete only when every
/// joined relation is fully GROUND. It does not unify: a stored fact that carries a
/// variable (a schematic fact, e.g. `(sol $n ..)`) is not matched against a query
/// ground value (`(sol Z ..)`), and a nonground compound query column (e.g.
/// `(: $b (-> $c $d))`) stays unconsumed. On ground data flat-leapfrog equals the
/// ProductZipper; on schematic data it is a strict subset and will SILENTLY drop
/// answers. A caller that may join over schematic facts must detect that (any factor
/// column is a nonground compound, or any joined relation holds a non-ground fact at
/// the functor prefix) and route to a unifying join instead.
pub fn ground_join(
    map: &PathMap<()>,
    factors: &[Factor],
    var_order: &[usize],
    nvars: usize,
) -> Vec<Vec<Vec<u8>>> {
    let mut out = Vec::new();
    GroundJoin::new(map, factors, var_order, nvars, None).run(&mut |b: &[Vec<u8>]| out.push(b.to_vec()));
    out
}

/// `ground_join` restricted to the leading variable's values assigned to
/// worker `worker` of `nworkers` by hash. The union over `worker in 0..nworkers`
/// equals `ground_join`.
pub fn ground_join_partition(
    map: &PathMap<()>,
    factors: &[Factor],
    var_order: &[usize],
    nvars: usize,
    worker: usize,
    nworkers: usize,
) -> Vec<Vec<Vec<u8>>> {
    let mut out = Vec::new();
    GroundJoin::new(map, factors, var_order, nvars, Some((worker, nworkers.max(1))))
        .run(&mut |b: &[Vec<u8>]| out.push(b.to_vec()));
    out
}

/// Streams each join answer (the per-variable bound values, indexed by variable)
/// to `emit`, restricted to worker `worker` of `nworkers` by hashing the leading
/// variable. No answer vector is materialized -- the caller applies its template
/// to each binding as it is produced. The held-cursor substrate of the parallel
/// ground transform.
pub fn ground_join_for_each<F: FnMut(&[Vec<u8>])>(
    map: &PathMap<()>,
    factors: &[Factor],
    var_order: &[usize],
    nvars: usize,
    worker: usize,
    nworkers: usize,
    mut emit: F,
) {
    GroundJoin::new(map, factors, var_order, nvars, Some((worker, nworkers.max(1)))).run(&mut emit);
}

/// Data-parallel `ground_join`: partition the leading variable's domain across
/// `nthreads` workers by hash, each running the join on the shared read-only map
/// into its own answer buffer, then concatenate. Byte-identical (as a set) to
/// `ground_join`. Safe: concurrent reads of an immutable `PathMap`, no shared
/// writes.
pub fn ground_join_parallel(
    map: &PathMap<()>,
    factors: &[Factor],
    var_order: &[usize],
    nvars: usize,
    nthreads: usize,
) -> Vec<Vec<Vec<u8>>> {
    let nthreads = nthreads.max(1);
    let parts: Vec<Vec<Vec<Vec<u8>>>> = std::thread::scope(|scope| {
        let handles: Vec<_> = (0..nthreads)
            .map(|w| scope.spawn(move || ground_join_partition(map, factors, var_order, nvars, w, nthreads)))
            .collect();
        handles.into_iter().map(|h| h.join().unwrap()).collect()
    });
    let mut out = Vec::new();
    for p in parts {
        out.extend(p);
    }
    out
}

/// Data-parallel `ground_join` that only COUNTS answers (no materialization),
/// isolating the join's parallel scaling from answer-vector allocation.
pub fn ground_join_count_parallel(
    map: &PathMap<()>,
    factors: &[Factor],
    var_order: &[usize],
    nvars: usize,
    nthreads: usize,
) -> u64 {
    let nthreads = nthreads.max(1);
    let counts: Vec<u64> = std::thread::scope(|scope| {
        let handles: Vec<_> = (0..nthreads)
            .map(|w| {
                scope.spawn(move || {
                    let mut n = 0u64;
                    GroundJoin::new(map, factors, var_order, nvars, Some((w, nthreads)))
                        .run(&mut |_b: &[Vec<u8>]| n += 1);
                    n
                })
            })
            .collect();
        handles.into_iter().map(|h| h.join().unwrap()).collect()
    });
    counts.into_iter().sum()
}

/// Worst-case-optimal leapfrog join over ground MORK facts, HELD-cursor: one
/// `SubtermCursor` per factor is opened once at the factor's relation prefix and
/// walked column by column with `descend_floor`/`ascend_floor` as variables bind
/// and backtrack, so the byte-trie is descended incrementally and never re-opened
/// from the root (the dominant cost of the naive per-column re-descend, ~25% of
/// the join). Answers stream to a caller closure -- no domain is materialized.
struct GroundJoin<'a> {
    factors: &'a [Factor],
    var_order: &'a [usize],
    cursors: Vec<SubtermCursor<ReadZipperUntracked<'a, 'static, ()>>>,
    next_col: Vec<usize>,
    binding: Vec<Vec<u8>>,
    /// Assigns the FIRST scheduled variable's values to workers by
    /// `hash(value) % nworkers == worker` (`None` = whole domain, sequential).
    /// Hashing the whole value balances the domain; a byte-range split would give
    /// one worker everything (every value shares its leading tag byte).
    lead_partition: Option<(usize, usize)>,
}

impl<'a> GroundJoin<'a> {
    fn new(
        map: &'a PathMap<()>,
        factors: &'a [Factor],
        var_order: &'a [usize],
        nvars: usize,
        lead_partition: Option<(usize, usize)>,
    ) -> Self {
        let cursors = factors
            .iter()
            .map(|f| SubtermCursor::new(map.read_zipper_at_path(&f.prefix)))
            .collect();
        GroundJoin {
            factors,
            var_order,
            cursors,
            next_col: vec![0; factors.len()],
            binding: vec![Vec::new(); nvars],
            lead_partition,
        }
    }

    fn run<F: FnMut(&[Vec<u8>])>(&mut self, emit: &mut F) {
        self.catch_up(0, 0, emit);
    }

    fn recurse<F: FnMut(&[Vec<u8>])>(&mut self, i: usize, emit: &mut F) {
        self.catch_up(i, 0, emit);
    }

    /// Consume every ground or already-bound column of factor `f` (and beyond) at
    /// the current variable depth by seeking the held cursor to the exact value,
    /// then hand off to the free-variable leapfrog. Descends in place -- no re-open.
    fn catch_up<F: FnMut(&[Vec<u8>])>(&mut self, i: usize, f: usize, emit: &mut F) {
        if f == self.factors.len() {
            self.recurse_after_catch_up(i, emit);
            return;
        }
        let Some(col) = self.factors[f].cols.get(self.next_col[f]).cloned() else {
            self.catch_up(i, f + 1, emit);
            return;
        };
        let target = match col {
            FactorColumn::Term(term) if term.is_ground() => Some(term.bytes),
            FactorColumn::Var(v) if !self.binding[v].is_empty() => Some(self.binding[v].clone()),
            FactorColumn::Var(_) | FactorColumn::Term(_) => None,
        };
        let Some(target) = target else {
            self.catch_up(i, f + 1, emit);
            return;
        };
        self.cursors[f].seek(&target);
        if self.cursors[f].key() == Some(target.as_slice()) {
            self.cursors[f].descend_floor();
            self.next_col[f] += 1;
            self.catch_up(i, f, emit);
            self.next_col[f] -= 1;
            self.cursors[f].ascend_floor();
        }
        self.cursors[f].reset_to_floor();
    }

    fn recurse_after_catch_up<F: FnMut(&[Vec<u8>])>(&mut self, i: usize, emit: &mut F) {
        if i == self.var_order.len() {
            if (0..self.factors.len())
                .all(|f| self.next_col[f] == self.factors[f].cols.len() && self.cursors[f].has_value())
            {
                emit(&self.binding);
            }
            return;
        }
        let v = self.var_order[i];
        let parts: Vec<usize> = (0..self.factors.len())
            .filter(|&f| {
                matches!(self.factors[f].cols.get(self.next_col[f]), Some(FactorColumn::Var(cv)) if *cv == v)
            })
            .collect();
        self.leapfrog(i, v, &parts, emit);
    }

    /// Held-cursor streaming leapfrog for free variable `v` over its participating
    /// factors `parts`: seek each cursor to the running maximum subterm; when they
    /// all agree, that value is in the intersection, so descend every cursor into
    /// it, recurse, ascend back, and step the first cursor forward. Every exit
    /// resets the participating cursors to their column floors so the parent can
    /// ascend past its own column cleanly.
    fn leapfrog<F: FnMut(&[Vec<u8>])>(&mut self, i: usize, v: usize, parts: &[usize], emit: &mut F) {
        if parts.is_empty() {
            return;
        }
        for &f in parts {
            self.cursors[f].first();
            if self.cursors[f].at_end() {
                self.reset_parts(parts);
                return;
            }
        }
        loop {
            let max: Vec<u8> = parts
                .iter()
                .map(|&f| self.cursors[f].key().unwrap().to_vec())
                .max()
                .unwrap();
            let mut all_match = true;
            for &f in parts {
                if self.cursors[f].key().unwrap() != max.as_slice() {
                    self.cursors[f].seek(&max);
                    if self.cursors[f].at_end() {
                        self.reset_parts(parts);
                        return;
                    }
                    if self.cursors[f].key().unwrap() != max.as_slice() {
                        all_match = false;
                    }
                }
            }
            if all_match {
                if self.lead_owned(i, &max) {
                    for &f in parts {
                        self.cursors[f].descend_floor();
                        self.next_col[f] += 1;
                    }
                    self.binding[v].clear();
                    self.binding[v].extend_from_slice(&max);
                    self.recurse(i + 1, emit);
                    self.binding[v].clear();
                    for &f in parts {
                        self.next_col[f] -= 1;
                        self.cursors[f].ascend_floor();
                    }
                }
                self.cursors[parts[0]].next();
                if self.cursors[parts[0]].at_end() {
                    self.reset_parts(parts);
                    return;
                }
            }
        }
    }

    /// The leading-variable work-partition gate (only at the first scheduled
    /// variable): hash the value and keep it iff it belongs to this worker.
    fn lead_owned(&self, i: usize, val: &[u8]) -> bool {
        if i != 0 {
            return true;
        }
        match self.lead_partition {
            None => true,
            Some((worker, nworkers)) => {
                let mut h = 0xcbf29ce484222325u64;
                for &b in val {
                    h ^= b as u64;
                    h = h.wrapping_mul(0x100000001b3);
                }
                (h % nworkers as u64) as usize == worker
            }
        }
    }

    fn reset_parts(&mut self, parts: &[usize]) {
        for &f in parts {
            self.cursors[f].reset_to_floor();
        }
    }
}

// ---- unification layer: schematic data (stored variables in facts act as wildcards) ----

#[inline]
fn is_wildcard_term(k: &[u8]) -> bool {
    k.len() == 1 && matches!(byte_item(k[0]), Tag::NewVar | Tag::VarRef(_))
}

/// The children of a factor's current column when the join variable is still free. This is the
/// lead, which enumerates the whole column (structured children and wildcards alike).
fn free_candidates<Z: Zipper + ZipperMoving>(cur: &mut SubtermCursor<Z>) -> Vec<Vec<u8>> {
    let mut out = Vec::new();
    cur.first();
    while let Some(k) = cur.key() {
        out.push(k.to_vec());
        cur.next();
    }
    out
}

/// The candidates at a ground column: the exact ground subterm if the trie holds it, plus every
/// stored wildcard at that position. Wildcards are one tag byte in the contiguous range
/// `VarRef(0)..=NewVar`, so one seek to `VarRef(0)` and a scan while-wildcard covers them all.
fn ground_candidates<Z: Zipper + ZipperMoving>(
    cur: &mut SubtermCursor<Z>,
    g: &[u8],
) -> Vec<Vec<u8>> {
    let mut out = Vec::new();
    cur.seek(g);
    if cur.key() == Some(g) {
        out.push(g.to_vec());
    }
    cur.seek(&[item_byte(Tag::VarRef(0))]);
    while let Some(k) = cur.key() {
        if is_wildcard_term(k) {
            out.push(k.to_vec());
            cur.next();
        } else {
            break;
        }
    }
    out
}

/// A factor is inverted when its columns are not in `var_order` order, so the join cannot seek it
/// forward (a later column's variable is bound before an earlier one). The triangle's third factor
/// `(e $z $x)` under order `$x,$y,$z` is the case: its `$x` column comes second but binds first.
fn is_inverted(factor: &Factor, var_pos: &[usize]) -> bool {
    let mut prev = None;
    for col in &factor.cols {
        if let Some(pos) = col.min_var_pos(var_pos) {
            if prev.is_some_and(|p| p > pos) {
                return true;
            }
            prev = Some(pos);
        }
    }
    false
}

/// One position in a re-emitted subterm: a literal byte, or a variable identified by its original
/// id (so the re-index can renumber it canonically in the new column order).
enum Item {
    Byte(u8),
    Var(usize),
}

/// Split a fact's column bytes (everything after the relation prefix) into its `ncols` subterms.
fn split_columns(bytes: &[u8], ncols: usize) -> Vec<&[u8]> {
    let mut cols = Vec::with_capacity(ncols);
    let mut i = 0;
    for _ in 0..ncols {
        let len = expr_span_len(expr_from_bytes(&bytes[i..]));
        cols.push(&bytes[i..i + len]);
        i += len;
    }
    cols
}

/// Decode each column into items, tagging every variable with its original id. NewVar takes the next
/// id in encounter order across the whole fact; VarRef(i) refers to id `i`. This is what lets the
/// re-index renumber a coreferent schematic fact, say `(e $u $u)`, correctly after its columns move.
fn columns_to_items(cols: &[&[u8]]) -> Vec<Vec<Item>> {
    let mut next_orig = 0usize;
    let mut out = Vec::with_capacity(cols.len());
    for col in cols {
        let mut items = Vec::new();
        let mut ez = ExprZipper::new(expr_from_bytes(col));
        loop {
            match ez.item() {
                Ok(Tag::Arity(arity)) => items.push(Item::Byte(item_byte(Tag::Arity(arity)))),
                Ok(Tag::VarRef(var)) => items.push(Item::Var(var as usize)),
                Ok(Tag::NewVar) => {
                    items.push(Item::Var(next_orig));
                    next_orig += 1;
                }
                Err(symbol) => {
                    items.push(Item::Byte(item_byte(Tag::SymbolSize(symbol.len() as u8))));
                    items.extend(symbol.iter().copied().map(Item::Byte));
                }
                Ok(Tag::SymbolSize(_)) => unreachable!(),
            }
            if !ez.next() {
                break;
            }
        }
        out.push(items);
    }
    out
}

/// Re-emit the columns in `new_order`, renumbering variables so the first reference to each original
/// id (in the new order) is a NewVar and later references are a VarRef of its new index. Produces a
/// canonical, self-consistent encoding for the re-indexed key.
fn emit_reordered(items_by_col: &[Vec<Item>], new_order: &[usize]) -> Vec<u8> {
    use std::collections::HashMap;
    let mut out = Vec::new();
    let mut renum: HashMap<usize, usize> = HashMap::new();
    for &c in new_order {
        for item in &items_by_col[c] {
            match item {
                Item::Byte(b) => out.push(*b),
                Item::Var(orig) => match renum.get(orig) {
                    Some(&new_id) => out.push(item_byte(Tag::VarRef(new_id as u8))),
                    None => {
                        renum.insert(*orig, renum.len());
                        out.push(item_byte(Tag::NewVar));
                    }
                },
            }
        }
    }
    out
}

/// Re-index an inverted factor: copy its facts into a fresh PathMap with the columns permuted into
/// `var_order` position order (variables renumbered to stay canonical). Returns that map, the new
/// column-variable list, now non-decreasing, so the join seeks it like any compatible factor, and
/// the permutation itself (`new_order[j]` = original column at re-indexed position `j`) so a leaf
/// can reconstruct the stored fact's original bytes. This is the one partial materialization the
/// cyclic case needs, and only the inverted factor pays it; re-keying into another attribute order
/// is the standard worst-case-optimal answer to a cycle.
fn build_reindex(
    map: &PathMap<()>,
    factor: &Factor,
    var_pos: &[usize],
) -> (PathMap<()>, Vec<FactorColumn>, Vec<usize>) {
    let ncols = factor.cols.len();
    let mut new_order: Vec<usize> = (0..ncols).collect();
    new_order.sort_by_key(|&c| match &factor.cols[c] {
        FactorColumn::Term(term) if term.is_ground() => (0usize, 0usize, c),
        col => (
            col.min_var_pos(var_pos).map_or(usize::MAX, |pos| pos + 1),
            1usize,
            c,
        ),
    });
    let new_cols: Vec<FactorColumn> = new_order.iter().map(|&c| factor.cols[c].clone()).collect();

    let mut reindex = PathMap::<()>::new();
    let plen = factor.prefix.len();
    let mut rz = map.read_zipper_at_path(&factor.prefix);
    while rz.to_next_val() {
        let full = rz.origin_path();
        let cols = split_columns(&full[plen..], ncols);
        let items = columns_to_items(&cols);
        reindex.insert(&emit_reordered(&items, &new_order), ());
    }
    (reindex, new_cols, new_order)
}

/// Worst-case-optimal leapfrog-UNIFICATION join directly on the PathMap byte-trie, returning the
/// fully-ground answer rows (`row[v]` = global variable `v`'s value). A row with any still-free query
/// variable is dropped here; the live route uses [`unify_join_zipper_partial`] instead, to keep it
/// and bind only its ground components, exactly as the materialized route does.
pub fn unify_join_zipper(
    map: &PathMap<()>,
    factors: &[Factor],
    var_order: &[usize],
    nvars: usize,
) -> BTreeSet<Vec<Vec<u8>>> {
    unify_join_zipper_partial(map, factors, var_order, nvars)
        .into_iter()
        .filter_map(|row| {
            row.into_iter()
                .map(|component| component.filter(|bytes| first_subterm_is_ground(bytes)))
                .collect::<Option<Vec<Vec<u8>>>>()
        })
        .collect()
}

/// As [`unify_join_zipper`], but each answer component is `Some(bytes)` when the query variable
/// resolved to a concrete term (ground or schematic) and `None` when it stayed free. Generalizes
/// [`ground_join`]: a stored variable in the data is a wildcard that unifies with the join variable
/// through the trail. Inverted factors (a cyclic query has one) are re-indexed up front so the join
/// can seek them; every other factor stays zero-copy on the live map. An assignment whose bindings
/// close a cycle (an occurs violation built across columns) yields no row.
pub fn unify_join_zipper_partial(
    map: &PathMap<()>,
    factors: &[Factor],
    var_order: &[usize],
    nvars: usize,
) -> BTreeSet<Vec<Option<Vec<u8>>>> {
    run_unify_join(map, factors, var_order, nvars, false).out
}

/// As [`unify_join_zipper_partial`], but returns each answer as one variable-coordinated tuple
/// encoding (query variables `0..nvars` in order, sharing one intro map), so a free variable that
/// spans answer positions renders with coordinated NewVar/VarRef the way MORK's emit does.
fn unify_join_zipper_coordinated(
    map: &PathMap<()>,
    factors: &[Factor],
    var_order: &[usize],
    nvars: usize,
) -> BTreeSet<Vec<u8>> {
    run_unify_join(map, factors, var_order, nvars, true).coordinated
}

/// Build the join state without running it. When `want_coordinated`, a run also collects each
/// answer as one variable-coordinated tuple encoding (see [`unify_join_zipper_coordinated`]).
fn join_state<'a>(
    map: &'a PathMap<()>,
    factors: &[Factor],
    var_order: &'a [usize],
    nvars: usize,
    want_coordinated: bool,
) -> UnifyJoin<'a> {
    let nf = factors.len();
    let mut var_pos = vec![0usize; nvars];
    for (pos, &v) in var_order.iter().enumerate() {
        var_pos[v] = pos;
    }

    // Re-index inverted factors so the join can seek them in var_order; a compatible factor keeps its
    // live-map prefix and pays nothing. `factor_src[f]` selects which map factor `f` reads from.
    let mut owned: Vec<Factor> = Vec::with_capacity(nf);
    let mut reindexes: Vec<PathMap<()>> = Vec::new();
    let mut factor_src: Vec<Option<usize>> = Vec::with_capacity(nf);
    let mut originals: Vec<Option<(Vec<u8>, Vec<usize>)>> = Vec::with_capacity(nf);
    for factor in factors {
        if is_inverted(factor, &var_pos) {
            let (ri, new_cols, new_order) = build_reindex(map, factor, &var_pos);
            factor_src.push(Some(reindexes.len()));
            originals.push(Some((factor.prefix.clone(), new_order)));
            reindexes.push(ri);
            owned.push(Factor {
                prefix: Vec::new(),
                cols: new_cols,
            });
        } else {
            factor_src.push(None);
            originals.push(None);
            owned.push(factor.clone());
        }
    }

    UnifyJoin {
        map,
        reindexes,
        factor_src,
        originals,
        factors: owned,
        var_order,
        var_pos,
        nvars,
        bound: vec![Vec::new(); nf],
        next_col: vec![0; nf],
        data_intro: vec![0; nf],
        bindings: BTreeMap::new(),
        arena: Vec::new(),
        out: BTreeSet::new(),
        want_coordinated,
        coordinated: BTreeSet::new(),
        on_tuple: None,
        stopped: false,
    }
}

/// Build the join state and run it, collecting answer rows (and coordinated tuples when asked).
fn run_unify_join<'a>(
    map: &'a PathMap<()>,
    factors: &[Factor],
    var_order: &'a [usize],
    nvars: usize,
    want_coordinated: bool,
) -> UnifyJoin<'a> {
    let mut state = join_state(map, factors, var_order, nvars, want_coordinated);
    state.recurse(0);
    state
}

/// Run the join streaming each accepted assignment's per-factor original fact bytes to `on_tuple`
/// instead of collecting rows; a `false` return stops the search early.
pub fn run_unify_join_stream(
    map: &PathMap<()>,
    factors: &[Factor],
    var_order: &[usize],
    nvars: usize,
    on_tuple: &mut dyn FnMut(&[Vec<u8>]) -> bool,
) {
    let mut state = join_state(map, factors, var_order, nvars, false);
    state.on_tuple = Some(on_tuple);
    state.recurse(0);
}

/// Parse an encoded conjunction body `(, p1 .. pk)` into factors, threading the body's variable
/// numbering (a NewVar takes the next id in first-occurrence order, a VarRef back-references one).
/// Returns the factors and the variable count.
pub fn parse_body_factors(body: &[u8]) -> Option<(Vec<Factor>, usize)> {
    let (body_len, _) = try_parse_first_subterm(body)?;
    if body_len != body.len() {
        return None;
    }
    let body_term = EncodedTerm::new(body.to_vec(), 0);
    let body_expr = body_term.expr();
    let nvars = validate_vars_and_count(body_expr)?;
    let Tag::Arity(nconj) = body_term.tag() else {
        return None;
    };
    if nconj == 0 {
        return None;
    }
    let children = expr_children(&body_term)?;
    if children.len() != nconj as usize {
        return None;
    }
    let mut factors = Vec::with_capacity(nconj.saturating_sub(1) as usize);
    for factor in children.iter().skip(1) {
        factors.push(parse_pattern_factor(factor)?);
    }
    Some((factors, nvars))
}

/// One conjunct `(rel arg..)` to a factor. The prefix is the arity byte alone, and the relation
/// head is column 0 like any argument: a variable query head then unifies with every stored head,
/// and a wildcard stored head is captured under a ground query head, neither of which a head baked
/// into the literal seek prefix can reach.
fn parse_pattern_factor(pat: &EncodedTerm) -> Option<Factor> {
    let Tag::Arity(total_arity) = pat.tag() else {
        return None;
    };
    if total_arity == 0 {
        return None;
    }
    let children = expr_children(pat)?;
    if children.len() != total_arity as usize {
        return None;
    }
    let prefix = vec![item_byte(Tag::Arity(total_arity))];
    let mut cols = Vec::with_capacity(total_arity as usize);
    for child in &children {
        cols.push(parse_pattern_col(child)?);
    }
    Some(Factor { prefix, cols })
}

fn parse_pattern_col(term: &EncodedTerm) -> Option<FactorColumn> {
    if term.bytes.len() == 1 {
        match term.tag() {
            Tag::NewVar => return Some(FactorColumn::Var(term.intro as usize)),
            Tag::VarRef(id) => return Some(FactorColumn::Var(id as usize)),
            Tag::SymbolSize(_) | Tag::Arity(_) => {}
        }
    }
    Some(FactorColumn::Term(term.clone()))
}

/// Live-route entry: parse the conjunction body into factors and run the join on the live map.
/// Variables bind in first-occurrence order, the order the emit numbers the answer components in.
/// None if the body is not a relation-prefix conjunction.
pub fn unify_join_zipper_body(map: &PathMap<()>, body: &[u8]) -> Option<BTreeSet<Vec<Vec<u8>>>> {
    let (factors, nvars) = parse_body_factors(body)?;
    let var_order: Vec<usize> = (0..nvars).collect();
    Some(unify_join_zipper(map, &factors, &var_order, nvars))
}

/// Returns true when `body` is a nonempty relation-prefixed conjunction, which is the whole class
/// the join owns. The decision reads only the encoded body through the same factor parser as the
/// join; the map argument is kept for signature stability and is not consulted.
pub fn unify_join_zipper_body_routable(_map: &PathMap<()>, body: &[u8]) -> bool {
    catch_unwind(AssertUnwindSafe(|| {
        let Some((factors, _)) = parse_body_factors(body) else {
            return false;
        };
        body_factors_routable_to_zipper_join(&factors)
    }))
    .unwrap_or(false)
}

/// Parse, route-check, and run the zipper join for bodies whose all-variable answer rows can be
/// represented exactly as ground bytes. Bodies that route but produce any free or schematic
/// answer component return `None`; callers that can render partial rows should use
/// [`unify_join_zipper_body_partial_safe`].
pub fn unify_join_zipper_body_safe(
    map: &PathMap<()>,
    body: &[u8],
) -> Option<BTreeSet<Vec<Vec<u8>>>> {
    let (_, rows) = unify_join_zipper_body_partial_safe(map, body)?;
    rows.into_iter()
        .map(|row| {
            row.into_iter()
                .map(|component| component.filter(|bytes| first_subterm_is_ground(bytes)))
                .collect::<Option<Vec<Vec<u8>>>>()
        })
        .collect()
}

/// Parse, route-check, and run the zipper join, preserving free or schematic answer components for
/// the live template renderer. `None` only for a body that is not a nonempty relation-prefixed
/// conjunction (or one whose evaluation panicked), which stays on the ProductZipper path.
pub fn unify_join_zipper_body_partial_safe(
    map: &PathMap<()>,
    body: &[u8],
) -> Option<(usize, BTreeSet<Vec<Option<Vec<u8>>>>)> {
    catch_unwind(AssertUnwindSafe(|| {
        let (factors, nvars) = parse_body_factors(body)?;
        if !body_factors_routable_to_zipper_join(&factors) {
            return None;
        }
        let var_order: Vec<usize> = (0..nvars).collect();
        Some((
            nvars,
            unify_join_zipper_partial(map, &factors, &var_order, nvars),
        ))
    }))
    .ok()
    .flatten()
}

/// Parse, route-check, and run the zipper join, returning each answer as one variable-coordinated
/// tuple encoding. Unlike [`unify_join_zipper_body_safe`], a free-variable answer is kept: a
/// variable shared across answer positions emits as one coordinated variable, so the caller can
/// render and compare free-variable answers up to consistent renaming. `None` only for a body
/// outside the nonempty relation-prefixed conjunction class, which stays on the ProductZipper
/// path.
pub fn unify_join_zipper_body_rows_rendered(
    map: &PathMap<()>,
    body: &[u8],
) -> Option<BTreeSet<Vec<u8>>> {
    catch_unwind(AssertUnwindSafe(|| {
        let (factors, nvars) = parse_body_factors(body)?;
        if !body_factors_routable_to_zipper_join(&factors) {
            return None;
        }
        let var_order: Vec<usize> = (0..nvars).collect();
        Some(unify_join_zipper_coordinated(
            map, &factors, &var_order, nvars,
        ))
    }))
    .ok()
    .flatten()
}

/// The engine dispatch mode: off, the default intersecting-bodies policy, or every routable body
/// (`MORK_LEAPFROG=all`, an experiment knob for workloads whose enumeration-shaped bodies happen
/// to profit anyway).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum DispatchMode {
    Off,
    Intersecting,
    All,
}

thread_local! {
    /// Per-thread engine dispatch mode, default the intersecting policy; `MORK_LEAPFROG=0` turns
    /// dispatch off at thread start, `MORK_LEAPFROG=all` dispatches every routable body.
    /// Thread-local rather than process-global so a differential can hold one run on the
    /// ProductZipper while another thread runs dispatched, without racing parallel tests.
    static LEAPFROG_DISPATCH: std::cell::Cell<DispatchMode> = std::cell::Cell::new(
        match std::env::var("MORK_LEAPFROG").as_deref() {
            Ok("0") => DispatchMode::Off,
            Ok("all") => DispatchMode::All,
            _ => DispatchMode::Intersecting,
        },
    );
}

/// Whether the space-to-space transform routes conjunctive bodies to the leapfrog join on this
/// thread.
pub fn leapfrog_dispatch_enabled() -> bool {
    LEAPFROG_DISPATCH.with(|c| c.get()) != DispatchMode::Off
}

/// Turn the leapfrog dispatch on (the default intersecting-bodies policy) or off for this thread.
/// The differentials use this to pin a reference run to the ProductZipper path.
pub fn set_leapfrog_dispatch(on: bool) {
    LEAPFROG_DISPATCH.with(|c| {
        c.set(if on {
            DispatchMode::Intersecting
        } else {
            DispatchMode::Off
        })
    })
}

/// The engine-facing dispatch entry: stream every product tuple the leapfrog accepts through the
/// stock `query_multi` callback contract. Each accepted assignment reconstructs its per-factor
/// stored facts, pairs them with the pattern factors exactly as `Space::query_multi_raw` does, and
/// hands them to `mork_expr::unify`, so `effect` sees the bindings the ProductZipper path
/// produces and the template emit downstream stays stock; occurs failures are skipped where stock
/// skips them. Returns the successful-match count, or `None` for a body outside the nonempty
/// relation-prefixed conjunction class (or if evaluation panicked), which the caller sends down
/// the ProductZipper path. A `false` from `effect` stops the search, as it stops the stock scan.
pub fn query_multi_leapfrog<F: FnMut(Result<&[u32], BTreeMap<(u8, u8), ExprEnv>>, Expr) -> bool>(
    map: &PathMap<()>,
    pat_expr: Expr,
    mut effect: F,
) -> Option<usize> {
    catch_unwind(AssertUnwindSafe(|| {
        let body = unsafe { pat_expr.span().as_ref().unwrap() };
        let (factors, nvars) = parse_body_factors(body)?;
        if !body_factors_routable_to_zipper_join(&factors) {
            return None;
        }
        if LEAPFROG_DISPATCH.with(|c| c.get()) != DispatchMode::All
            && !body_factors_profit_from_leapfrog(map, &factors, nvars)
        {
            return None;
        }
        let var_order: Vec<usize> = (0..nvars).collect();
        let mut pat_args = Vec::new();
        ExprEnv::new(0, pat_expr).args(&mut pat_args);
        let sources = &pat_args[1..];
        debug_assert_eq!(sources.len(), factors.len());
        let mut candidate = 0usize;
        let mut on_tuple = |tuple: &[Vec<u8>]| -> bool {
            unsafe { crate::space::unifications += 1 };
            let e = Expr {
                ptr: tuple[0].as_ptr().cast_mut(),
            };
            let mut pairs = vec![(sources[0], ExprEnv::new(1, e))];
            for (j, fact) in tuple.iter().enumerate().skip(1) {
                pairs.push((
                    sources[j],
                    ExprEnv::new(
                        (j + 1) as u8,
                        Expr {
                            ptr: fact.as_ptr().cast_mut(),
                        },
                    ),
                ));
            }
            match unify(&mut pairs) {
                Ok(bs) => {
                    candidate += 1;
                    effect(Err(bs), e)
                }
                Err(_) => true,
            }
        };
        run_unify_join_stream(map, &factors, &var_order, nvars, &mut on_tuple);
        Some(candidate)
    }))
    .ok()
    .flatten()
}

/// GHD drop-in for [`query_multi_leapfrog`]: for a *cyclic* body with a low-width hypertree
/// decomposition, materialize each bag with the WCO join and natural-join the bags (an acyclic
/// bag-query), streaming the SAME `(bindings, loc)` per full match as the global join, so the
/// answer set is byte-identical. Returns `None` (fall back to the global join) for an acyclic body
/// (already output-optimal), a body with a nonground compound column (a shared variable the bag
/// key would miss), or when no width `<= 3` decomposition exists.
pub fn query_multi_ghd<F: FnMut(Result<&[u32], BTreeMap<(u8, u8), ExprEnv>>, Expr) -> bool>(
    map: &PathMap<()>,
    pat_expr: Expr,
    mut effect: F,
) -> Option<usize> {
    let body = unsafe { pat_expr.span().as_ref().unwrap() };
    let (factors, nvars) = parse_body_factors(body)?;
    if !body_factors_routable_to_zipper_join(&factors) {
        return None;
    }
    // Every variable must be a top-level column: `extract_var_values` reads top-level columns, so a
    // nonground compound column could hide a shared variable the bag-join key misses.
    if factors
        .iter()
        .any(|f| f.cols.iter().any(|c| c.is_nonground_compound()))
    {
        return None;
    }
    let edges = crate::ghd::hypergraph(&factors);
    let ghd = crate::ghd::decompose(&edges, 3)?;
    if ghd.width < 2 {
        return None; // acyclic bodies are already output-optimal under the global WCO join.
    }
    let bags_mat: Vec<(crate::ghd::Bag, Vec<crate::ghd::BagMatch>)> = ghd
        .bags
        .iter()
        .map(|b| (b.clone(), crate::ghd::materialize_bag(map, &factors, b, nvars)))
        .collect();
    let full_tuples = crate::ghd::join_bags(&bags_mat, factors.len());

    let mut pat_args = Vec::new();
    ExprEnv::new(0, pat_expr).args(&mut pat_args);
    let sources = &pat_args[1..];
    debug_assert_eq!(sources.len(), factors.len());
    let mut candidate = 0usize;
    for tuple in &full_tuples {
        unsafe { crate::space::unifications += 1 };
        let e = Expr {
            ptr: tuple[0].as_ptr().cast_mut(),
        };
        let mut pairs = vec![(sources[0], ExprEnv::new(1, e))];
        for (j, fact) in tuple.iter().enumerate().skip(1) {
            pairs.push((
                sources[j],
                ExprEnv::new(
                    (j + 1) as u8,
                    Expr {
                        ptr: fact.as_ptr().cast_mut(),
                    },
                ),
            ));
        }
        if let Ok(bs) = unify(&mut pairs) {
            candidate += 1;
            if !effect(Err(bs), e) {
                break;
            }
        }
    }
    Some(candidate)
}

/// The join owns every nonempty relation-prefixed conjunction: each column carries full
/// `mork_expr::unify` with data-side capture, and an assignment that closes a cycle is rejected at
/// emit, so no query or fact shape needs a decline. The check is parse-level and reads nothing
/// from the map. The per-column byte-level union-find this gate once scanned facts for is gone;
/// its boundary (`nonflat_uf_unsound`) constrained that mechanism, not this one.
fn body_factors_routable_to_zipper_join(factors: &[Factor]) -> bool {
    !factors.is_empty()
}

/// Collect the query variables of one factor into `out`: the top-level `Var` columns and every
/// variable nested in a `Term` column. A NewVar takes the next id after the ones introduced before
/// this term (`term.intro`), a VarRef names its id, matching the body's global numbering.
pub fn collect_factor_vars(factor: &Factor, out: &mut std::collections::BTreeSet<usize>) {
    for col in &factor.cols {
        match col {
            FactorColumn::Var(v) => {
                out.insert(*v);
            }
            FactorColumn::Term(term) => {
                let mut ez = ExprZipper::new(term.expr());
                let mut intro = term.intro as usize;
                loop {
                    match ez.tag() {
                        Tag::NewVar => {
                            out.insert(intro);
                            intro += 1;
                        }
                        Tag::VarRef(i) => {
                            out.insert(i as usize);
                        }
                        Tag::SymbolSize(_) | Tag::Arity(_) => {}
                    }
                    if !ez.next() {
                        break;
                    }
                }
            }
        }
    }
}

/// Row cap for the functional-dependency probe. Below it a relation is walked in full and its
/// trailing FD decided exactly; a body whose relations all fit is cheap to probe. Above it the
/// probe is skipped and the structurally cyclic body dispatches, which is correct: at that scale a
/// genuine cyclic graph pattern is the worst-case-optimal join's win, and reading the whole
/// relation to decide would cost more than it saves (following the fork's 200k threshold).
const FD_PROBE_ROW_CAP: usize = 200_000;

/// The engine dispatch's performance policy, distinct from routability: dispatch a body only when
/// it has a cycle the leapfrog can seek and win on. Three conjuncts, each with a measured
/// counterexample behind it, cheapest first.
///
/// The cycle must be seekable: cyclic over the variables that occur as whole columns, because a
/// whole column is what the leapfrog intersects on the trie. A body whose cycle is carried only
/// inside compound arguments (the counter machine's `(IC $i)`, `(JZ $r $j)`) gives the seek
/// nothing, and its small hot queries pay only the join's per-candidate machinery (measured 1.6x
/// slower dispatched).
///
/// The cycle must be genuine: cyclic over the full variable sets, nested occurrences included,
/// because alpha-acyclic queries are where a relation-at-a-time plan already meets the optimal
/// bound, O(input + output), and the seek beats the product asymptotically only where every such
/// plan builds a super-linear intermediate the AGM bound forbids the answer from having (Ngo et
/// al. 2012). This declines paths, semijoins, enumeration-and-filter, and pure products without
/// reading data (a 10^6-tuple product measured 1.8x slower dispatched).
///
/// And the cycle must not be functionally degenerate: `(a /\ b = c)(a \/ b = d)(c - d = e)` is a
/// real hyperedge diamond, but each relation is a function, so its AGM bound collapses to O(N)
/// (Gottlob-Lee-Valiant-Valiant; Abo Khamis-Ngo-Suciu) and the leapfrog wins nothing
/// (finite_domain measured 3.8x slower dispatched). Only for bodies the first two conjuncts pass
/// does the probe read bounded data: it detects each relation's trailing functional dependency
/// (the `(lhs.. = result)` convention) by comparing the distinct determinant projection against
/// the full rows, folds every dependent into the atoms holding its determinant, and re-runs GYO.
/// A graph's `edge` disproves its FD at the first repeated source, so a genuine cyclic pattern
/// stops paying for the scan within a few facts and dispatches.
///
/// Correctness never depends on any of this, since both paths return the same matches.
///
/// Within the cyclic non-functional class, the instance still decides who wins, and the full
/// bench suite measured the boundary. Every relation tiny: the whole query is fast either way
/// and the ProductZipper's constants win (the tile puzzle's inequality tables), so it declines.
/// Four or more join factors: a relation-at-a-time product deepens multiplicatively while the
/// join stays output-bounded (the clique bench's 6- and 10-factor queries ran 50x faster
/// dispatched), so it dispatches. Three factors: only skew pays, so a bounded probe samples
/// first-argument values for a heavy hitter, the hub through which a product blows up
/// quadratically (the 240x triangle); a uniform instance has none and declines (the transitive
/// bench's triangle detect over a million random edges measured 15% slower dispatched, and
/// declines). A hub outside the sample window is missed, and the body then merely stays on the
/// stock path; telling those apart exactly is the cost-based dispatch this policy approximates
/// with bounded reads.
fn body_factors_profit_from_leapfrog(map: &PathMap<()>, factors: &[Factor], nvars: usize) -> bool {
    if !(hypergraph_is_cyclic(column_var_edges(factors), nvars) && body_is_cyclic(factors, nvars)) {
        return false;
    }
    let counts: Vec<usize> = factors
        .iter()
        .map(|f| bounded_fact_count(map, f, DISPATCH_MIN_FACTS))
        .collect();
    if counts.iter().all(|c| *c < DISPATCH_MIN_FACTS) {
        return false;
    }
    if factors.len() < DISPATCH_MANY_FACTORS {
        let heavy = factors
            .iter()
            .zip(&counts)
            .any(|(f, c)| *c >= DISPATCH_MIN_FACTS && factor_has_sampled_heavy_hitter(map, f));
        if !heavy {
            return false;
        }
    }
    !body_is_acyclic_modulo_fds(map, factors, nvars)
}

/// Below this many facts in every factor's relation the query is small either way and the
/// ProductZipper's straight-line constants win; the tile puzzle's 56-fact inequality tables
/// measured a mild loss dispatched, while the demonstration's smallest hub instance (265 facts)
/// must still dispatch.
const DISPATCH_MIN_FACTS: usize = 128;

/// From this many join factors on, the relation-at-a-time product deepens multiplicatively while
/// the join stays output-bounded, skewed instance or not: the clique bench's 6- and 10-factor
/// queries measured 50x faster dispatched on a graph whose 3-factor triangle declines.
const DISPATCH_MANY_FACTORS: usize = 4;

/// A first-argument value with this many continuations is a heavy hitter: the product through it
/// blows up quadratically. Uniform random graphs (the transitive bench's degrees average ~20)
/// stay below it and decline.
const DISPATCH_HEAVY_DEGREE: usize = 64;

/// How many first-argument values the heavy-hitter probe samples, in trie order.
const DISPATCH_HEAVY_SAMPLES: usize = 64;

/// The factor's relation region: its prefix, extended by the head column when the head is a
/// ground symbol, so the counts and samples read this relation rather than every same-arity fact.
fn factor_scan_path(factor: &Factor) -> Vec<u8> {
    let mut p = factor.prefix.clone();
    if let Some(FactorColumn::Term(head)) = factor.cols.first() {
        if head.is_ground() {
            p.extend_from_slice(&head.bytes);
        }
    }
    p
}

/// Count the facts under the factor's relation region, stopping at `cap`: a bounded walk, so the
/// gate's cost stays independent of the space size.
fn bounded_fact_count(map: &PathMap<()>, factor: &Factor, cap: usize) -> usize {
    let mut rz = map.read_zipper_at_path(&factor_scan_path(factor));
    let mut n = 0;
    while n < cap && rz.to_next_val() {
        n += 1;
    }
    n
}

/// Sample up to [`DISPATCH_HEAVY_SAMPLES`] first-argument values of the factor's relation, in
/// trie order, and report whether any has [`DISPATCH_HEAVY_DEGREE`] or more continuations. Both
/// walks are capped, so the probe reads a bounded region regardless of the space size.
fn factor_has_sampled_heavy_hitter(map: &PathMap<()>, factor: &Factor) -> bool {
    let base = factor_scan_path(factor);
    let mut cur = SubtermCursor::new(map.read_zipper_at_path(&base));
    cur.first();
    let mut sampled = 0;
    while sampled < DISPATCH_HEAVY_SAMPLES && !cur.at_end() {
        let Some(key) = cur.key() else { break };
        let mut path = base.clone();
        path.extend_from_slice(key);
        let mut inner = SubtermCursor::new(map.read_zipper_at_path(&path));
        inner.first();
        let mut deg = 0;
        while !inner.at_end() && deg < DISPATCH_HEAVY_DEGREE {
            deg += 1;
            inner.next();
        }
        if deg >= DISPATCH_HEAVY_DEGREE {
            return true;
        }
        sampled += 1;
        cur.next();
    }
    false
}

/// The hyperedges of the variables the leapfrog can seek: per factor, its whole-column variables
/// only, compound-nested occurrences excluded.
fn column_var_edges(factors: &[Factor]) -> Vec<std::collections::BTreeSet<usize>> {
    factors
        .iter()
        .map(|f| {
            f.cols
                .iter()
                .filter_map(|col| match col {
                    FactorColumn::Var(v) => Some(*v),
                    FactorColumn::Term(_) => None,
                })
                .collect::<std::collections::BTreeSet<usize>>()
        })
        .filter(|s| !s.is_empty())
        .collect()
}

/// The ordered distinct query variables of a factor when every column is simple (a top-level
/// variable or a ground symbol), else `None`. Only these factors carry a decidable trailing FD in
/// the `(lhs.. = result)` sense; a compound column has no such reading, so its factor contributes
/// no FD and stays a plain hyperedge.
fn factor_simple_var_schema(factor: &Factor) -> Option<Vec<usize>> {
    let mut schema = Vec::new();
    for col in &factor.cols {
        match col {
            FactorColumn::Var(v) => {
                if !schema.contains(v) {
                    schema.push(*v);
                }
            }
            FactorColumn::Term(term)
                if term.is_ground() && matches!(term.tag(), Tag::SymbolSize(_)) => {}
            _ => return None,
        }
    }
    Some(schema)
}

/// Per-factor accumulator for the trailing-FD probe, driven by one shared walk of the facts under
/// the factor's prefix. The column plan is precomputed so folding a fact needs no allocation until
/// it passes the factor's ground columns: `ground_cols` are the (index, bytes) a fact must match,
/// `var_cols` the (index, variable) bindings, and `schema` the variable order (determinant is all
/// but the last, dependent is the last). `over_cap` trips when the relation exceeds the probe cap.
struct FactorFd {
    schema: Vec<usize>,
    ground_cols: Vec<(usize, Vec<u8>)>,
    var_cols: Vec<(usize, usize)>,
    det_rows: std::collections::BTreeSet<Vec<u8>>,
    full_rows: std::collections::BTreeSet<Vec<u8>>,
    seen: usize,
    /// Set when the factor can no longer yield an FD: the relation exceeded the probe cap, or a
    /// determinant collision already disproved functionality. A genuinely relational factor (a
    /// graph's `edge`) collides within its first few facts, so it stops paying for the scan
    /// almost immediately; only a genuinely functional table is read in full, where the read buys
    /// the decline.
    dead: bool,
}

impl FactorFd {
    fn new(factor: &Factor, schema: Vec<usize>) -> Self {
        let mut ground_cols = Vec::new();
        let mut var_cols = Vec::new();
        for (ci, col) in factor.cols.iter().enumerate() {
            match col {
                FactorColumn::Var(v) => var_cols.push((ci, *v)),
                FactorColumn::Term(term) => ground_cols.push((ci, term.bytes.clone())),
            }
        }
        FactorFd {
            schema,
            ground_cols,
            var_cols,
            det_rows: std::collections::BTreeSet::new(),
            full_rows: std::collections::BTreeSet::new(),
            seen: 0,
            dead: false,
        }
    }

    /// Fold one fact's column spans into the accumulator, if the fact matches the factor's ground
    /// columns and its repeated variables agree. Rejects on the ground columns before allocating.
    fn observe(&mut self, cols: &[&[u8]]) {
        if self.dead {
            return;
        }
        for (ci, bytes) in &self.ground_cols {
            if cols[*ci] != &bytes[..] {
                return;
            }
        }
        // Bind each variable to its first column's value; a later column of the same variable must
        // agree. `vals` stays in schema order, tiny (a factor has a handful of columns).
        let mut vals: Vec<(usize, &[u8])> = Vec::with_capacity(self.var_cols.len());
        for (ci, v) in &self.var_cols {
            match vals.iter().find(|(bv, _)| bv == v) {
                Some((_, prev)) if *prev != cols[*ci] => return,
                Some(_) => {}
                None => vals.push((*v, cols[*ci])),
            }
        }
        self.seen += 1;
        if self.seen > FD_PROBE_ROW_CAP {
            self.dead = true;
            self.det_rows.clear();
            self.full_rows.clear();
            return;
        }
        let val_of = |var: usize| vals.iter().find(|(v, _)| *v == var).unwrap().1;
        let (dependent, determinant) = self.schema.split_last().unwrap();
        let mut det_key = Vec::new();
        for v in determinant {
            det_key.extend_from_slice(val_of(*v));
            det_key.push(0xFF);
        }
        let mut full_key = det_key.clone();
        full_key.extend_from_slice(val_of(*dependent));
        self.det_rows.insert(det_key);
        self.full_rows.insert(full_key);
        // A determinant seen again with a new dependent disproves the FD for good.
        if self.full_rows.len() > self.det_rows.len() {
            self.dead = true;
            self.det_rows.clear();
            self.full_rows.clear();
        }
    }

    /// The trailing FD `(determinant -> dependent)` this factor's data supports, if any.
    fn resolve(&self) -> Option<(std::collections::BTreeSet<usize>, usize)> {
        if self.dead || self.seen == 0 {
            return None;
        }
        debug_assert_eq!(self.det_rows.len(), self.full_rows.len());
        let (dependent, determinant) = self.schema.split_last().unwrap();
        Some((determinant.iter().copied().collect(), *dependent))
    }
}

/// Whether the body is acyclic once functional dependencies are folded in. Detect each factor's
/// trailing FD from the data, extend every atom that holds a determinant with its dependent to a
/// fixpoint, and re-run GYO on the extended hyperedges. A body all of whose cycles are carried by
/// functional relations reduces to acyclic here; a genuine relational cycle does not.
///
/// The detection walks each distinct factor prefix once and folds every fact into all factors
/// sharing that prefix, so a body whose factors are the same arity (a functional pipeline over
/// one arity, like `finite_domain`) pays a single scan, not one per factor.
fn body_is_acyclic_modulo_fds(map: &PathMap<()>, factors: &[Factor], nvars: usize) -> bool {
    use std::collections::BTreeSet;

    // Only simple factors with two or more variables carry a decidable trailing FD; the rest never
    // contribute one, so they are skipped in the scan and stay plain hyperedges.
    let mut states: Vec<Option<FactorFd>> = factors
        .iter()
        .map(|f| {
            factor_simple_var_schema(f)
                .filter(|s| s.len() >= 2)
                .map(|schema| FactorFd::new(f, schema))
        })
        .collect();

    if states.iter().all(|s| s.is_none()) {
        return false;
    }

    // Group probeable factors by prefix, walk each prefix's facts once, fold into every factor
    // that shares it.
    let mut prefixes: Vec<Vec<u8>> = Vec::new();
    for (i, st) in states.iter().enumerate() {
        if st.is_some() && !prefixes.contains(&factors[i].prefix) {
            prefixes.push(factors[i].prefix.clone());
        }
    }
    for prefix in &prefixes {
        let members: Vec<usize> = (0..factors.len())
            .filter(|&i| states[i].is_some() && &factors[i].prefix == prefix)
            .collect();
        // One prefix means one arity byte, so every member parses the same column count.
        let ncols = factors[members[0]].cols.len();
        debug_assert!(members.iter().all(|&i| factors[i].cols.len() == ncols));
        let mut rz = map.read_zipper_at_path(prefix);
        while rz.to_next_val() {
            let full = rz.origin_path();
            let cols = split_columns(&full[prefix.len()..], ncols);
            let mut live = false;
            for &i in &members {
                let st = states[i].as_mut().unwrap();
                st.observe(&cols);
                live |= !st.dead;
            }
            // Every member disproved: a genuinely relational prefix stops paying within its
            // first collisions instead of walking the whole relation.
            if !live {
                break;
            }
        }
    }

    let fds: Vec<(BTreeSet<usize>, usize)> = states
        .iter()
        .filter_map(|s| s.as_ref().and_then(FactorFd::resolve))
        .collect();
    if fds.is_empty() {
        return false;
    }

    let mut edges: Vec<BTreeSet<usize>> = factors
        .iter()
        .map(|f| {
            let mut s = BTreeSet::new();
            collect_factor_vars(f, &mut s);
            s
        })
        .collect();
    loop {
        let mut changed = false;
        for (determinant, dependent) in &fds {
            for e in edges.iter_mut() {
                if determinant.is_subset(e) && e.insert(*dependent) {
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }

    let edges: Vec<BTreeSet<usize>> = edges.into_iter().filter(|s| !s.is_empty()).collect();
    !hypergraph_is_cyclic(edges, nvars)
}

/// Whether the body's join hypergraph is cyclic, by GYO reduction (Graham; Yu and Ozsoyoglu). The
/// hyperedges are the factor variable sets. Runs in the query's size, which is tiny, and touches
/// no data.
fn body_is_cyclic(factors: &[Factor], nvars: usize) -> bool {
    let edges: Vec<std::collections::BTreeSet<usize>> = factors
        .iter()
        .map(|f| {
            let mut s = std::collections::BTreeSet::new();
            collect_factor_vars(f, &mut s);
            s
        })
        .filter(|s| !s.is_empty())
        .collect();
    hypergraph_is_cyclic(edges, nvars)
}

/// GYO reduction on an explicit hyperedge list. Repeatedly drop every vertex that lies in only one
/// edge (an "ear" attachment), then remove any edge contained in another; a query is alpha-acyclic
/// exactly when this peels the hypergraph down to a single edge or nothing. Whatever cannot be
/// peeled is a cycle.
fn hypergraph_is_cyclic(mut edges: Vec<std::collections::BTreeSet<usize>>, nvars: usize) -> bool {
    loop {
        let mut changed = false;

        // Drop vertices that occur in exactly one edge: they can never close a cycle.
        let mut occ = vec![0usize; nvars];
        for e in &edges {
            for &v in e {
                occ[v] += 1;
            }
        }
        for e in &mut edges {
            let before = e.len();
            e.retain(|&v| occ[v] > 1);
            if e.len() != before {
                changed = true;
            }
        }

        // Remove an edge contained in (or equal to) another edge; an empty edge is contained in any.
        let mut removed = None;
        'outer: for i in 0..edges.len() {
            for j in 0..edges.len() {
                if i != j && edges[i].is_subset(&edges[j]) {
                    // On equal sets remove only the later one, so two equal edges collapse to one.
                    if edges[i] == edges[j] && i > j {
                        continue;
                    }
                    removed = Some(i);
                    break 'outer;
                }
            }
        }
        if let Some(i) = removed {
            edges.remove(i);
            changed = true;
        }

        if !changed {
            break;
        }
    }

    edges.len() > 1
}

struct UnifyJoin<'a> {
    map: &'a PathMap<()>,
    /// Re-indexed copies of inverted factors; `factor_src[f] = Some(i)` reads `reindexes[i]`.
    reindexes: Vec<PathMap<()>>,
    factor_src: Vec<Option<usize>>,
    /// Per factor, `Some((original_prefix, new_order))` when re-indexed: the original relation
    /// prefix and the column permutation `build_reindex` applied (`new_order[j]` = original column
    /// at re-indexed position `j`), enough to reconstruct the stored fact's original bytes at a
    /// leaf.
    originals: Vec<Option<(Vec<u8>, Vec<usize>)>>,
    /// Owned because a re-indexed factor's prefix and columns differ from the input factor's.
    factors: Vec<Factor>,
    var_order: &'a [usize],
    /// `var_pos[v]` = position of global variable `v` in `var_order`, for the catch-up test.
    var_pos: Vec<usize>,
    nvars: usize,
    bound: Vec<Vec<u8>>,
    next_col: Vec<usize>,
    data_intro: Vec<u8>,
    bindings: Bindings,
    arena: Vec<Box<[u8]>>,
    /// Answer rows, one `Option` per query variable: `Some(bytes)` for a resolved term, `None` for
    /// a still-free variable. The all-ground entry filters to fully-ground rows.
    out: BTreeSet<Vec<Option<Vec<u8>>>>,
    /// When set, also collect each answer as one variable-coordinated tuple encoding in `coordinated`.
    want_coordinated: bool,
    /// Answer tuples encoded through one shared intro map, so free-variable coreference across answer
    /// positions survives for the live renderer. Empty unless `want_coordinated`.
    coordinated: BTreeSet<Vec<u8>>,
    /// When set, each accepted assignment streams its per-factor original fact bytes here instead
    /// of collecting rows, and a `false` return stops the search. The engine dispatch uses this to
    /// re-derive each match's bindings with `mork_expr::unify` on the stock path's terms.
    on_tuple: Option<&'a mut dyn FnMut(&[Vec<u8>]) -> bool>,
    /// Set when `on_tuple` asked to stop; the recursion unwinds without visiting more candidates.
    stopped: bool,
}

impl UnifyJoin<'_> {
    fn recurse(&mut self, i: usize) {
        self.catch_up(i, 0);
    }

    fn recurse_after_catch_up(&mut self, i: usize) {
        if self.stopped {
            return;
        }
        if i == self.var_order.len() {
            if !(0..self.factors.len()).all(|f| self.factor_has_value(f)) {
                return;
            }
            if self.on_tuple.is_some() {
                // The engine dispatch consumes tuples, not rows: reconstruct each factor's stored
                // fact and let the caller re-derive the match's bindings with `mork_expr::unify`
                // on the stock path's own terms, per product tuple, exactly as the ProductZipper
                // path does. Occurs rejection then happens where stock does it, so none of the
                // row or cycled bookkeeping below runs.
                let tuple: Vec<Vec<u8>> = (0..self.factors.len())
                    .map(|f| self.original_fact_bytes(f))
                    .collect();
                let cb = self.on_tuple.as_mut().unwrap();
                if !cb(&tuple) {
                    self.stopped = true;
                }
                return;
            }
            // Keep every component that resolved to a term, ground or schematic. A variable that is
            // still free is None; the live emit can then render schematic compounds and leave free
            // variables fresh, matching the ProductZipper's byte output.
            //
            // `mork_expr::unify` checks occurs only per equation, so a cycle can arrive through a
            // chain of columns (the join-propagated capture builds x0 = (k (k x0))). `apply`
            // records in `cycled` every variable whose cycle it had to cut; `Expr::_unify` rejects
            // exactly that after its own apply. Mirror it per answer row: a cyclic assignment is an
            // occurs violation and yields no answer, as the ProductZipper's full unification does.
            let mut cycled = BTreeMap::new();
            let row: Vec<Option<Vec<u8>>> = (0..self.nvars)
                .map(|v| self.query_component(v, &mut cycled))
                .collect();
            if !cycled.is_empty() {
                return;
            }
            self.out.insert(row);
            if self.want_coordinated {
                self.coordinated.insert(self.emit_coordinated_tuple());
            }
            return;
        }
        let v = self.var_order[i];
        let mut parts: Vec<usize> = (0..self.factors.len())
            .filter(|&f| {
                let nc = self.next_col[f];
                matches!(self.factors[f].cols.get(nc), Some(FactorColumn::Var(cv)) if *cv == v)
            })
            .collect();
        if parts.is_empty() {
            self.recurse(i + 1);
            return;
        }
        if self.deref_env(self.query_var_env(v)).var_opt().is_none() {
            self.consume_var_parts(&parts, 0, v, i);
            return;
        }
        // The leapfrog principle: lead with the smallest domain so the leading factor enumerates
        // few candidates and the rest seek. A bounded subterm count under each factor's current
        // position is the estimate. This is what makes a selective factor, say (e a $y) with a few
        // edges, drive the join instead of the whole relation.
        parts.sort_by_key(|&f| self.domain_estimate(f));
        self.consume_var_parts(&parts, 0, v, i);
    }

    /// The map factor `f` reads from: its re-indexed copy if it was inverted, else the live map.
    fn src_map(&self, f: usize) -> &PathMap<()> {
        match self.factor_src[f] {
            Some(ri) => &self.reindexes[ri],
            None => self.map,
        }
    }

    /// Domain-size estimate for lead selection, bounded so it is independent of the space size.
    /// Count the distinct subterm values under the factor's current position, but stop at a small
    /// cap. The leapfrog only needs to know which factor has the fewest candidates, not the exact
    /// count, so a bounded count suffices and stays O(cap). A full `val_count` is O(subtree), which
    /// would make a selective join's cost climb with the whole relation rather than the answer.
    fn domain_estimate(&self, f: usize) -> usize {
        const CAP: usize = 32;
        let mut path = self.factors[f].prefix.clone();
        path.extend_from_slice(&self.bound[f]);
        let mut cur = SubtermCursor::new(self.src_map(f).read_zipper_at_path(&path));
        cur.first();
        let mut n = 0;
        while !cur.at_end() && n < CAP {
            n += 1;
            cur.next();
        }
        n
    }

    fn factor_path(&self, f: usize) -> Vec<u8> {
        let mut path = self.factors[f].prefix.clone();
        path.extend_from_slice(&self.bound[f]);
        path
    }

    /// The stored fact factor `f` sits on at a leaf, in its original encoding. A factor read from
    /// the live map is its prefix plus the bound column bytes. A re-indexed factor's bound bytes
    /// are its permuted, canonically renumbered columns; putting the columns back in original
    /// order and renumbering again (first reference NewVar, later ones VarRef of the new index) is
    /// exactly the stored encoding, because a stored fact is itself numbered canonically in column
    /// order.
    fn original_fact_bytes(&self, f: usize) -> Vec<u8> {
        match &self.originals[f] {
            None => self.factor_path(f),
            Some((orig_prefix, new_order)) => {
                let ncols = self.factors[f].cols.len();
                let spans = split_columns(&self.bound[f], ncols);
                let items = columns_to_items(&spans);
                // `orig_positions[c]` = where original column `c` sits in the re-indexed layout,
                // so emitting in that order restores the original column order.
                let mut orig_positions = vec![0usize; ncols];
                for (j, &c) in new_order.iter().enumerate() {
                    orig_positions[c] = j;
                }
                let mut out = orig_prefix.clone();
                out.extend_from_slice(&emit_reordered(&items, &orig_positions));
                debug_assert!(
                    self.map.read_zipper_at_path(&out).val().is_some(),
                    "re-indexed leaf must reconstruct a fact stored in the source map"
                );
                out
            }
        }
    }

    fn factor_has_value(&self, f: usize) -> bool {
        if self.next_col[f] != self.factors[f].cols.len() {
            return false;
        }
        let path = self.factor_path(f);
        self.src_map(f).read_zipper_at_path(&path).val().is_some()
    }

    /// The candidates at factor `f`'s current column when a query variable is still free.
    fn open_free_candidates(&self, f: usize) -> Vec<Vec<u8>> {
        let path = self.factor_path(f);
        let mut cur = SubtermCursor::new(self.src_map(f).read_zipper_at_path(&path));
        free_candidates(&mut cur)
    }

    /// The candidates at factor `f`'s current ground column that can unify with the fixed query
    /// value. A data-side wildcard captures that ground value and keeps its stored slot for later
    /// VarRef columns in the same fact.
    fn open_ground_candidates(&self, f: usize, ground: &[u8]) -> Vec<Vec<u8>> {
        let path = self.factor_path(f);
        let mut cur = SubtermCursor::new(self.src_map(f).read_zipper_at_path(&path));
        ground_candidates(&mut cur, ground)
    }

    fn child_bytes_at_current(&self, f: usize) -> Vec<u8> {
        let path = self.factor_path(f);
        self.src_map(f)
            .read_zipper_at_path(&path)
            .child_mask()
            .iter()
            .collect()
    }

    fn wildcard_children_at_current(&self, f: usize) -> Vec<u8> {
        self.child_bytes_at_current(f)
            .into_iter()
            .filter(|&b| is_wildcard_term(&[b]))
            .collect()
    }

    fn child_exists_at_current(&self, f: usize, b: u8) -> bool {
        let path = self.factor_path(f);
        has_bit(&self.src_map(f).read_zipper_at_path(&path).child_mask(), b)
    }

    fn factor_namespace(&self, f: usize) -> u8 {
        1 + f as u8
    }

    fn query_var_env(&self, v: usize) -> ExprEnv {
        ExprEnv {
            n: QUERY_NS,
            v: v as u8,
            offset: 0,
            base: expr_from_bytes(&NEW_VAR_EXPR_BYTES),
        }
    }

    fn var_env(&self, (n, v): BindingKey) -> ExprEnv {
        ExprEnv {
            n,
            v,
            offset: 0,
            base: expr_from_bytes(&NEW_VAR_EXPR_BYTES),
        }
    }

    fn arena_env(&mut self, namespace: u8, intro: u8, bytes: &[u8]) -> ExprEnv {
        self.arena.push(bytes.to_vec().into_boxed_slice());
        let bytes = self.arena.last().unwrap();
        ExprEnv {
            n: namespace,
            v: intro,
            offset: 0,
            base: expr_from_bytes(bytes),
        }
    }

    fn data_env_for(&mut self, f: usize, bytes: &[u8]) -> ExprEnv {
        self.arena_env(self.factor_namespace(f), self.data_intro[f], bytes)
    }

    fn unified_bindings(&self, lhs: ExprEnv, rhs: ExprEnv) -> Option<Bindings> {
        let mut pairs = Vec::with_capacity(self.bindings.len() + 1);
        for (&var, &env) in &self.bindings {
            pairs.push((self.var_env(var), env));
        }
        pairs.push((lhs, rhs));
        unify(&mut pairs).ok()
    }

    fn deref_env(&self, env: ExprEnv) -> ExprEnv {
        let mut current = env;
        loop {
            let Some(var) = current.var_opt() else {
                return current;
            };
            let Some(bound) = self.bindings.get(&var) else {
                return current;
            };
            current = *bound;
        }
    }

    fn query_component(&self, v: usize, cycled: &mut BTreeMap<BindingKey, u8>) -> Option<Vec<u8>> {
        let env = self.query_var_env(v);
        if self.deref_env(env).var_opt().is_some() {
            None
        } else {
            Some(self.emit_env_bytes(env, cycled))
        }
    }

    fn applied_var_len(&self, key: BindingKey, stack: &mut Vec<BindingKey>) -> usize {
        let Some(bound) = self.bindings.get(&key) else {
            return 1;
        };
        if stack.contains(&key) {
            return 1;
        }
        stack.push(key);
        let len = self.applied_len_inner(*bound, stack);
        stack.pop();
        len
    }

    fn applied_len_inner(&self, env: ExprEnv, stack: &mut Vec<BindingKey>) -> usize {
        let mut ez = ExprZipper::new(env.subsexpr());
        let mut original = env.v;
        let mut len = 0usize;
        loop {
            match ez.item() {
                Ok(Tag::NewVar) => {
                    len += self.applied_var_len((env.n, original), stack);
                    original += 1;
                }
                Ok(Tag::VarRef(i)) => len += self.applied_var_len((env.n, i), stack),
                Ok(Tag::Arity(_)) => len += 1,
                Ok(Tag::SymbolSize(_)) => unreachable!(),
                Err(symbol) => len += 1 + symbol.len(),
            }
            if !ez.next() {
                return len;
            }
        }
    }

    fn applied_len(&self, env: ExprEnv) -> usize {
        self.applied_len_inner(env, &mut Vec::new())
    }

    #[allow(deprecated)]
    fn apply_env_into(
        &self,
        env: ExprEnv,
        new_intros: u8,
        out: &mut Vec<u8>,
        cycled: &mut BTreeMap<BindingKey, u8>,
        stack: &mut Vec<BindingKey>,
        assignments: &mut Vec<BindingKey>,
    ) -> u8 {
        let len = self.applied_len(env).max(1);
        let start = out.len();
        out.resize(start + len, 0);
        let mut ez = ExprZipper::new(env.subsexpr());
        let mut oz = ExprZipper::new(Expr {
            ptr: out[start..].as_mut_ptr(),
        });
        let (_, next_new) = mork_expr::apply(
            env.n,
            env.v,
            new_intros,
            &mut ez,
            &self.bindings,
            &mut oz,
            cycled,
            stack,
            assignments,
        );
        debug_assert!(
            oz.loc <= len,
            "apply wrote {} bytes into a buffer sized {} by applied_len",
            oz.loc,
            len
        );
        out.truncate(start + oz.loc);
        next_new
    }

    fn emit_env_bytes(&self, env: ExprEnv, cycled: &mut BTreeMap<BindingKey, u8>) -> Vec<u8> {
        let mut out = Vec::new();
        let mut stack = Vec::new();
        let mut assignments = Vec::new();
        self.apply_env_into(env, 0, &mut out, cycled, &mut stack, &mut assignments);
        out
    }

    fn emit_coordinated_tuple(&self) -> Vec<u8> {
        let mut out = Vec::new();
        let mut cycled = BTreeMap::new();
        let mut stack = Vec::new();
        let mut assignments = Vec::new();
        let mut new_intros = 0;
        for v in 0..self.nvars {
            new_intros = self.apply_env_into(
                self.query_var_env(v),
                new_intros,
                &mut out,
                &mut cycled,
                &mut stack,
                &mut assignments,
            );
        }
        out
    }

    /// Consume variable `v`'s column in each participating factor in turn, then move to the next
    /// scheduled variable. The lead factor (`pi == 0`, `v` still free) enumerates its small domain
    /// and binds `v`; every later factor SEEKS the now-bound `v` instead of enumerating its own
    /// relation. `consume_col` resolves `v` and does exactly that: it enumerates while `v` is free
    /// and seeks once it is bound (a data-side wildcard still captures the value); when `v` was
    /// already bound by an earlier level, every factor seeks. The seek is what keeps a k-factor
    /// join O(answer) rather than O(relation^k); enumerating every factor made the triangle O(s^2).
    fn consume_var_parts(&mut self, parts: &[usize], pi: usize, v: usize, i: usize) {
        if self.stopped {
            return;
        }
        if pi == parts.len() {
            self.recurse(i + 1);
            return;
        }
        let f = parts[pi];
        self.consume_col(f, FactorColumn::Var(v), &mut |this| {
            this.consume_var_parts(parts, pi + 1, v, i);
        });
    }

    fn consume_col(&mut self, f: usize, col: FactorColumn, cont: &mut dyn FnMut(&mut Self)) {
        self.match_col_at_current(f, col, &mut |this| {
            this.next_col[f] += 1;
            cont(this);
            this.next_col[f] -= 1;
        });
    }

    fn with_bound_path_bytes(
        &mut self,
        f: usize,
        bytes: &[u8],
        intro_delta: u8,
        cont: &mut dyn FnMut(&mut Self),
    ) {
        let len = self.bound[f].len();
        let intro = self.data_intro[f];
        self.bound[f].extend_from_slice(bytes);
        self.data_intro[f] += intro_delta;
        cont(self);
        self.data_intro[f] = intro;
        self.bound[f].truncate(len);
    }

    fn with_bound_term(&mut self, f: usize, bytes: &[u8], cont: &mut dyn FnMut(&mut Self)) {
        let intro_delta = expr_from_bytes(bytes).newvars() as u8;
        self.with_bound_path_bytes(f, bytes, intro_delta, cont);
    }

    fn match_col_at_current(
        &mut self,
        f: usize,
        col: FactorColumn,
        cont: &mut dyn FnMut(&mut Self),
    ) {
        let env = match col {
            FactorColumn::Var(v) => self.query_var_env(v),
            FactorColumn::Term(term) => self.arena_env(QUERY_NS, term.intro, &term.bytes),
        };
        self.match_expr_at_current(f, env, cont);
    }

    fn match_candidate(
        &mut self,
        f: usize,
        pattern: ExprEnv,
        bytes: &[u8],
        cont: &mut dyn FnMut(&mut Self),
    ) {
        if self.stopped {
            return;
        }
        let saved_bindings = self.bindings.clone();
        let arena_mark = self.arena.len();
        let data_env = self.data_env_for(f, bytes);
        if let Some(bindings) = self.unified_bindings(pattern, data_env) {
            self.bindings = bindings;
            self.with_bound_term(f, bytes, cont);
        }
        self.bindings = saved_bindings;
        self.arena.truncate(arena_mark);
    }

    fn match_expr_at_current(
        &mut self,
        f: usize,
        pattern: ExprEnv,
        cont: &mut dyn FnMut(&mut Self),
    ) {
        let resolved = self.deref_env(pattern);
        if resolved.var_opt().is_some() {
            for bytes in self.open_free_candidates(f) {
                self.match_candidate(f, pattern, &bytes, cont);
            }
            return;
        }
        match byte_item(unsafe { *resolved.subsexpr().ptr }) {
            Tag::Arity(_) => self.match_compound_at_current(f, pattern, resolved, cont),
            Tag::NewVar | Tag::VarRef(_) => unreachable!(),
            Tag::SymbolSize(_) => {
                // A symbol holds no variables, so the resolved value needs no substitution: its
                // bytes are the subexpression span itself. `apply` stays for compound values.
                let bytes = unsafe { resolved.subsexpr().span().as_ref().unwrap() }.to_vec();
                for candidate in self.open_ground_candidates(f, &bytes) {
                    // Ground against ground: the seek established byte equality, and on ground
                    // terms byte equality is unifiability (RoutingSafe.thy,
                    // `ground_unifiable_iff_eq`), so `unify` would return the bindings unchanged.
                    // Bind the column directly; a wildcard candidate still unifies through
                    // `mork_expr::unify` below.
                    if candidate == bytes {
                        self.with_bound_path_bytes(f, &candidate, 0, cont);
                    } else {
                        self.match_candidate(f, pattern, &candidate, cont);
                    }
                }
            }
        }
    }

    fn match_compound_at_current(
        &mut self,
        f: usize,
        pattern: ExprEnv,
        resolved: ExprEnv,
        cont: &mut dyn FnMut(&mut Self),
    ) {
        for w in self.wildcard_children_at_current(f) {
            self.match_candidate(f, pattern, &[w], cont);
        }
        let Some(arity) = resolved.subsexpr().arity() else {
            return;
        };
        let arity_byte = item_byte(Tag::Arity(arity));
        if self.child_exists_at_current(f, arity_byte) {
            let mut children = Vec::new();
            resolved.args(&mut children);
            self.with_bound_path_bytes(f, &[arity_byte], 0, &mut |this| {
                this.match_compound_children(f, &children, 0, cont);
            });
        }
    }

    fn match_compound_children(
        &mut self,
        f: usize,
        children: &[ExprEnv],
        idx: usize,
        cont: &mut dyn FnMut(&mut Self),
    ) {
        if idx == children.len() {
            cont(self);
            return;
        }
        let child = children[idx];
        self.match_expr_at_current(f, child, &mut |this| {
            this.match_compound_children(f, children, idx + 1, cont);
        });
    }

    /// Before each scheduled variable, consume every column whose value is already known: ground
    /// query arguments, compound arguments, and repeated or inverted variables already bound by
    /// earlier levels. Columns can branch because a stored data variable may capture the fixed query
    /// value or compound.
    fn catch_up(&mut self, i: usize, f: usize) {
        if self.stopped {
            return;
        }
        if f == self.factors.len() {
            self.recurse_after_catch_up(i);
            return;
        }
        let Some(col) = self.factors[f].cols.get(self.next_col[f]).cloned() else {
            self.catch_up(i, f + 1);
            return;
        };
        match col {
            FactorColumn::Var(vp) if self.var_pos[vp] < i => {
                self.consume_col(f, FactorColumn::Var(vp), &mut |this| this.catch_up(i, f));
            }
            FactorColumn::Var(_) => {
                self.catch_up(i, f + 1);
            }
            other => {
                self.consume_col(f, other, &mut |this| this.catch_up(i, f));
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn mask_of(bytes: &[u8]) -> ByteMask {
        let mut m = [0u64; 4];
        for &b in bytes {
            m[(b >> 6) as usize] |= 1u64 << (b & 63);
        }
        ByteMask(m)
    }

    fn sym(s: &str) -> Vec<u8> {
        let mut v = vec![item_byte(Tag::SymbolSize(s.len() as u8))];
        v.extend_from_slice(s.as_bytes());
        v
    }

    /// `(rel a0 a1 ...)` encoded: Arity(1+n), Sym(rel), then each arg's bytes.
    fn nest(rel: &str, args: &[Vec<u8>]) -> Vec<u8> {
        let mut v = vec![item_byte(Tag::Arity((1 + args.len()) as u8))];
        v.extend(sym(rel));
        for a in args {
            v.extend_from_slice(a);
        }
        v
    }

    fn conj(factors: &[Vec<u8>]) -> Vec<u8> {
        nest(",", factors)
    }

    fn new_var() -> Vec<u8> {
        vec![item_byte(Tag::NewVar)]
    }

    fn var_ref(idx: u8) -> Vec<u8> {
        vec![item_byte(Tag::VarRef(idx))]
    }

    /// The stored-path prefix for a relation of the given total arity (head + args).
    fn relation_prefix(rel: &str, total_arity: usize) -> Vec<u8> {
        let mut v = vec![item_byte(Tag::Arity(total_arity as u8))];
        v.extend(sym(rel));
        v
    }

    #[test]
    fn safe_body_routes_flat_ground_answers() {
        let mut map = PathMap::<()>::new();
        map.insert(&nest("e", &[sym("a"), sym("b")]), ());
        map.insert(&nest("e", &[sym("b"), sym("c")]), ());
        let body = conj(&[
            nest("e", &[new_var(), new_var()]),
            nest("e", &[var_ref(1), new_var()]),
        ]);

        let rows = unify_join_zipper_body_safe(&map, &body).expect("flat body routes");
        let expected = BTreeSet::from([vec![sym("a"), sym("b"), sym("c")]]);
        assert_eq!(rows, expected);
    }

    #[test]
    fn safe_body_routes_single_ground_answer() {
        let mut map = PathMap::<()>::new();
        map.insert(&nest("p", &[sym("a"), sym("b")]), ());
        let body = conj(&[nest("p", &[sym("a"), new_var()])]);

        let rows = unify_join_zipper_body_safe(&map, &body).expect("flat body routes");
        let expected = BTreeSet::from([vec![sym("b")]]);
        assert_eq!(rows, expected);
    }

    #[test]
    fn safe_body_partial_routes_when_all_ground_entry_cannot_represent_rows() {
        let mut map = PathMap::<()>::new();
        map.insert(&nest("r", &[new_var()]), ());
        map.insert(&nest("r", &[nest("a", &[sym("v0")])]), ());
        let body = conj(&[nest("r", &[nest("a", &[new_var()])])]);

        assert!(unify_join_zipper_body_routable(&map, &body));
        let (_nvars, rows) =
            unify_join_zipper_body_partial_safe(&map, &body).expect("partial route is safe");
        assert!(
            rows.iter()
                .any(|row| row.iter().any(|component| component.is_none())),
            "the live renderer must preserve the free non-ground row"
        );
        assert!(
            unify_join_zipper_body_safe(&map, &body).is_none(),
            "the all-ground entry must not silently drop non-ground rows"
        );
    }

    #[test]
    fn coordinated_rows_preserve_free_var_coreference() {
        // A schematic fact (e $u $u) couples the two query variables: matching (e $x $y) binds both
        // to one free variable. The coordinated tuple must share it (NewVar then VarRef(0)), the way
        // MORK's emit numbers a coreferent answer.
        let mut coref = PathMap::<()>::new();
        coref.insert(&nest("e", &[new_var(), var_ref(0)]), ()); // (e $u $u)
        let body = conj(&[nest("e", &[new_var(), new_var()])]); // (e $x $y)
        let rows = unify_join_zipper_body_rows_rendered(&coref, &body).expect("flat body routes");
        assert_eq!(
            rows.len(),
            1,
            "one answer: $x and $y are the same free variable"
        );
        assert_eq!(
            rows.iter().next().unwrap(),
            &vec![item_byte(Tag::NewVar), item_byte(Tag::VarRef(0))],
            "coreferent free variables must coordinate to NewVar, VarRef(0)"
        );

        // Two independent data variables stay distinct: two NewVars, no back-reference.
        let mut indep = PathMap::<()>::new();
        indep.insert(&nest("e", &[new_var(), new_var()]), ()); // (e $u $w)
        let indep_rows =
            unify_join_zipper_body_rows_rendered(&indep, &body).expect("flat body routes");
        assert_eq!(
            indep_rows.iter().next().unwrap(),
            &vec![item_byte(Tag::NewVar), item_byte(Tag::NewVar)],
            "independent free variables must stay distinct NewVars"
        );
    }

    #[test]
    fn goal2_boundary_shapes_all_route() {
        let mut occurs = PathMap::<()>::new();
        occurs.insert(&nest("e", &[new_var(), var_ref(0)]), ());
        occurs.insert(&nest("e", &[sym("v0"), nest("f", &[sym("v1")])]), ());
        let occurs_body = conj(&[nest("e", &[new_var(), nest("f", &[var_ref(0)])])]);

        let mut ground_query = PathMap::<()>::new();
        ground_query.insert(&nest("r", &[nest("a", &[new_var()]), sym("v0")]), ());
        ground_query.insert(&nest("s", &[sym("v0"), sym("v1")]), ());
        ground_query.insert(&nest("t", &[sym("v1"), sym("b")]), ());
        let ground_query_body = conj(&[
            nest("r", &[nest("a", &[sym("b")]), new_var()]),
            nest("s", &[var_ref(0), new_var()]),
            nest("t", &[var_ref(1), sym("b")]),
        ]);

        let mut propagated = PathMap::<()>::new();
        propagated.insert(&nest("e", &[nest("k", &[new_var()]), sym("v0")]), ());
        propagated.insert(&nest("e", &[new_var(), var_ref(0)]), ());
        propagated.insert(&nest("h", &[new_var(), var_ref(0)]), ());
        let propagated_body = conj(&[
            nest("e", &[nest("k", &[new_var()]), new_var()]),
            nest("e", &[nest("k", &[var_ref(1)]), new_var()]),
            nest("h", &[var_ref(2), var_ref(0)]),
        ]);

        // The router is total on relation-prefixed conjunctions: the once-declined
        // join-propagated capture routes too, since the per-column step is full unification and a
        // cyclic assignment is rejected at emit (the raw-answer pin is the test below).
        for (name, map, body) in [
            ("acyclic-occurs", &occurs, &occurs_body),
            (
                "fact-schematic-compound-under-ground-query",
                &ground_query,
                &ground_query_body,
            ),
            (
                "join-propagated-compound-capture",
                &propagated,
                &propagated_body,
            ),
        ] {
            assert!(
                unify_join_zipper_body_routable(map, body),
                "{name} must be inside the zipper-owned route"
            );
            assert!(
                unify_join_zipper_body_partial_safe(map, body).is_some(),
                "{name} must route safely"
            );
        }
    }

    #[test]
    fn cyclic_capture_assignment_yields_no_row() {
        // The join-propagated capture can close a cycle across columns: matching (e $s1 $s1) at
        // both e-factors builds x1 = (k x0) and x2 = (k (k x0)), then (h $s0 $s0) forces x2 = x0,
        // an occurs violation. `mork_expr::unify` checks occurs per equation, so the cycle only
        // surfaces at the answer emit, where the row must be dropped: the ProductZipper's full
        // unification returns exactly the three ground rows. Pins the raw partial entry on the
        // shape that made the old byte-level mechanism decline.
        let mut map = PathMap::<()>::new();
        map.insert(&nest("e", &[nest("k", &[new_var()]), sym("v0")]), ());
        map.insert(&nest("e", &[new_var(), var_ref(0)]), ());
        map.insert(&nest("h", &[new_var(), var_ref(0)]), ());
        map.insert(&nest("h", &[sym("junk"), sym("junk")]), ());
        let body = conj(&[
            nest("e", &[nest("k", &[new_var()]), new_var()]),
            nest("e", &[nest("k", &[var_ref(1)]), new_var()]),
            nest("h", &[var_ref(2), var_ref(0)]),
        ]);
        let (factors, nvars) = parse_body_factors(&body).expect("body parses");
        let order: Vec<usize> = (0..nvars).collect();
        let rows = unify_join_zipper_partial(&map, &factors, &order, nvars);
        let k_v0 = nest("k", &[sym("v0")]);
        let expected: BTreeSet<Vec<Option<Vec<u8>>>> = BTreeSet::from([
            vec![Some(k_v0.clone()), Some(sym("v0")), Some(k_v0.clone())],
            vec![Some(sym("v0")), Some(k_v0), Some(sym("v0"))],
            vec![Some(sym("v0")), Some(sym("v0")), Some(sym("v0"))],
        ]);
        assert_eq!(rows, expected, "a cyclic assignment must yield no row");
    }

    #[test]
    fn subterm_cursor_enumerates_and_seeks_arg1() {
        // First arguments of various shapes: a compound (sorts first, tag 0x02 < symbol tag 0xC1),
        // several one-byte-length symbols, and a two-byte-length one (sorts last, 0xC2 > 0xC1).
        let a_terms: Vec<Vec<u8>> = vec![
            sym("a"),
            sym("b"),
            sym("c"),
            sym("z"),
            sym("bb"),
            nest("k", &[sym("v")]),
        ];
        // Each arg1 appears in two facts (distinct arg2) to exercise trie merging / distinctness.
        let mut facts = Vec::new();
        for (i, a) in a_terms.iter().enumerate() {
            facts.push(nest("e", &[a.clone(), sym(&format!("p{i}"))]));
            facts.push(nest("e", &[a.clone(), sym(&format!("q{i}"))]));
        }
        // A different relation under the same map, to confirm the prefix scopes the cursor.
        facts.push(nest("h", &[sym("a"), sym("a")]));

        let mut map = PathMap::<()>::new();
        for f in &facts {
            map.insert(f, ());
        }
        let pfx = relation_prefix("e", 3);

        // Oracle: distinct arg1 subterms in byte-lex order.
        let mut want: Vec<Vec<u8>> = a_terms.clone();
        want.sort();
        want.dedup();

        let mut cur = SubtermCursor::new(map.read_zipper_at_path(&pfx));
        cur.first();
        let mut got = Vec::new();
        while let Some(k) = cur.key() {
            got.push(k.to_vec());
            cur.next();
        }
        assert_eq!(
            got, want,
            "enumeration must be the distinct arg1 subterms in lex order"
        );

        // seek to each oracle value and to a few off-key targets; compare to least >= target.
        let mut targets = want.clone();
        targets.push(nest("k", &[sym("a")])); // a compound just below (k v)
        targets.push(sym("ba")); // between b and bb in byte order? [0xC2,'b','a'] vs [0xC2,'b','b']
        for target in &targets {
            cur.seek(target);
            let expect = want
                .iter()
                .find(|w| w.as_slice() >= target.as_slice())
                .cloned();
            assert_eq!(
                cur.key().map(<[u8]>::to_vec),
                expect,
                "seek({target:?}) must land on the least subterm >= target"
            );
        }

        // seek past every subterm -> exhausted.
        cur.seek(&sym("zz"));
        assert!(
            cur.at_end(),
            "seek past the maximum must exhaust the cursor"
        );
    }

    struct Lcg(u64);
    impl Lcg {
        fn new(seed: u64) -> Self {
            Lcg(seed
                .wrapping_mul(2862933555777941757)
                .wrapping_add(3037000493))
        }
        fn next_u64(&mut self) -> u64 {
            self.0 = self
                .0
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            self.0
        }
        fn below(&mut self, n: usize) -> usize {
            (self.next_u64() % n as u64) as usize
        }
    }

    /// A random variable-width term over a two-byte symbol alphabet, so symbols share prefixes and
    /// force multi-level backtracking in seek; with nested compounds when depth allows.
    fn rand_term(rng: &mut Lcg, depth: usize) -> Vec<u8> {
        const ALPHA: &[u8] = b"ab";
        if depth == 0 || rng.below(3) != 0 {
            let len = 1 + rng.below(3);
            let mut v = vec![item_byte(Tag::SymbolSize(len as u8))];
            for _ in 0..len {
                v.push(ALPHA[rng.below(ALPHA.len())]);
            }
            v
        } else {
            let n = 1 + rng.below(2);
            let mut v = vec![item_byte(Tag::Arity((1 + n) as u8))];
            v.extend(sym("f"));
            for _ in 0..n {
                v.extend(rand_term(rng, depth - 1));
            }
            v
        }
    }

    #[test]
    fn subterm_cursor_property_vs_brute_force() {
        for seed in 0..300u64 {
            let mut rng = Lcg::new(seed.wrapping_add(1));
            let n = 1 + rng.below(12);
            let a_terms: Vec<Vec<u8>> = (0..n).map(|_| rand_term(&mut rng, 2)).collect();

            let mut map = PathMap::<()>::new();
            for (i, a) in a_terms.iter().enumerate() {
                map.insert(&nest("e", &[a.clone(), sym(&format!("z{}", i % 3))]), ());
            }
            let pfx = relation_prefix("e", 3);

            let mut want: Vec<Vec<u8>> = a_terms.clone();
            want.sort();
            want.dedup();

            let mut cur = SubtermCursor::new(map.read_zipper_at_path(&pfx));
            cur.first();
            let mut got = Vec::new();
            while let Some(k) = cur.key() {
                got.push(k.to_vec());
                cur.next();
            }
            assert_eq!(got, want, "seed {seed}: enumeration");

            let mut targets = want.clone();
            for _ in 0..12 {
                targets.push(rand_term(&mut rng, 2));
            }
            for target in &targets {
                cur.seek(target);
                let expect = want
                    .iter()
                    .find(|w| w.as_slice() >= target.as_slice())
                    .cloned();
                assert_eq!(
                    cur.key().map(<[u8]>::to_vec),
                    expect,
                    "seed {seed}: seek({target:?})"
                );
            }
        }
    }

    /// Reference join: nested loop over one matching fact per factor, binding shared variables and
    /// rejecting on conflict. `factor_rows[f]` is the column-subterm list of factor f's facts.
    fn brute_rec(
        f: usize,
        factors: &[Factor],
        factor_rows: &[Vec<Vec<Vec<u8>>>],
        binding: &mut Vec<Option<Vec<u8>>>,
        out: &mut Vec<Vec<Vec<u8>>>,
    ) {
        if f == factors.len() {
            out.push(binding.iter().map(|b| b.clone().unwrap()).collect());
            return;
        }
        for row in &factor_rows[f] {
            let mut undo: Vec<usize> = Vec::new();
            let mut ok = true;
            for (ci, col) in factors[f].cols.iter().enumerate() {
                match col {
                    FactorColumn::Term(term) if term.is_ground() => {
                        if term.bytes != row[ci] {
                            ok = false;
                            break;
                        }
                    }
                    FactorColumn::Var(v) => {
                        if let Some(existing) = &binding[*v] {
                            if existing != &row[ci] {
                                ok = false;
                                break;
                            }
                        } else {
                            binding[*v] = Some(row[ci].clone());
                            undo.push(*v);
                        }
                    }
                    FactorColumn::Term(_) => {
                        ok = false;
                        break;
                    }
                }
            }
            if ok {
                brute_rec(f + 1, factors, factor_rows, binding, out);
            }
            for v in undo.into_iter().rev() {
                binding[v] = None;
            }
        }
    }

    #[test]
    fn ground_join_matches_brute_force() {
        for seed in 0..150u64 {
            let mut rng = Lcg::new(seed.wrapping_add(7));
            let nnodes = 3 + rng.below(4);
            let nodes: Vec<Vec<u8>> = (0..nnodes)
                .map(|i| sym(&((b'a' + i as u8) as char).to_string()))
                .collect();

            let mut map = PathMap::<()>::new();
            let mut e_facts: Vec<Vec<Vec<u8>>> = Vec::new();
            let mut f_facts: Vec<Vec<Vec<u8>>> = Vec::new();
            let nedges = 4 + rng.below(8);
            for _ in 0..nedges {
                let a = nodes[rng.below(nnodes)].clone();
                let b = nodes[rng.below(nnodes)].clone();
                if map
                    .insert(&nest("e", &[a.clone(), b.clone()]), ())
                    .is_none()
                {
                    e_facts.push(vec![a, b]);
                }
                let c = nodes[rng.below(nnodes)].clone();
                let d = nodes[rng.below(nnodes)].clone();
                if map
                    .insert(&nest("f", &[c.clone(), d.clone()]), ())
                    .is_none()
                {
                    f_facts.push(vec![c, d]);
                }
            }
            let pe = relation_prefix("e", 3);
            let pf = relation_prefix("f", 3);

            let queries: Vec<(Vec<Factor>, Vec<usize>, usize)> = vec![
                // path  (e $0 $1)(e $1 $2)
                (
                    vec![
                        Factor::var_cols(pe.clone(), vec![0, 1]),
                        Factor::var_cols(pe.clone(), vec![1, 2]),
                    ],
                    vec![0, 1, 2],
                    3,
                ),
                // star  (e $0 $1)(e $0 $2)
                (
                    vec![
                        Factor::var_cols(pe.clone(), vec![0, 1]),
                        Factor::var_cols(pe.clone(), vec![0, 2]),
                    ],
                    vec![0, 1, 2],
                    3,
                ),
                // two-relation path  (e $0 $1)(f $1 $2)
                (
                    vec![
                        Factor::var_cols(pe.clone(), vec![0, 1]),
                        Factor::var_cols(pf.clone(), vec![1, 2]),
                    ],
                    vec![0, 1, 2],
                    3,
                ),
                // three-path  (e $0 $1)(e $1 $2)(e $2 $3)
                (
                    vec![
                        Factor::var_cols(pe.clone(), vec![0, 1]),
                        Factor::var_cols(pe.clone(), vec![1, 2]),
                        Factor::var_cols(pe.clone(), vec![2, 3]),
                    ],
                    vec![0, 1, 2, 3],
                    4,
                ),
                // triangle  (e $0 $1)(e $1 $2)(e $2 $0) -- cyclic: factor 2's columns invert the
                // variable order, so it must validate $0 after binding $2 (the catch-up path).
                (
                    vec![
                        Factor::var_cols(pe.clone(), vec![0, 1]),
                        Factor::var_cols(pe.clone(), vec![1, 2]),
                        Factor::var_cols(pe.clone(), vec![2, 0]),
                    ],
                    vec![0, 1, 2],
                    3,
                ),
                // same triangle under a rotated variable order (different participation pattern).
                (
                    vec![
                        Factor::var_cols(pe.clone(), vec![0, 1]),
                        Factor::var_cols(pe.clone(), vec![1, 2]),
                        Factor::var_cols(pe.clone(), vec![2, 0]),
                    ],
                    vec![1, 2, 0],
                    3,
                ),
                // four-cycle  (e $0 $1)(e $1 $2)(e $2 $3)(e $3 $0)
                (
                    vec![
                        Factor::var_cols(pe.clone(), vec![0, 1]),
                        Factor::var_cols(pe.clone(), vec![1, 2]),
                        Factor::var_cols(pe.clone(), vec![2, 3]),
                        Factor::var_cols(pe.clone(), vec![3, 0]),
                    ],
                    vec![0, 1, 2, 3],
                    4,
                ),
                // intra-factor coreference  (e $0 $0): only the self-loops, via catch-up on col 1.
                (vec![Factor::var_cols(pe.clone(), vec![0, 0])], vec![0], 1),
                // triangle with a pendant  (e $0 $1)(e $1 $2)(e $2 $0)(f $0 $3)
                (
                    vec![
                        Factor::var_cols(pe.clone(), vec![0, 1]),
                        Factor::var_cols(pe.clone(), vec![1, 2]),
                        Factor::var_cols(pe.clone(), vec![2, 0]),
                        Factor::var_cols(pf.clone(), vec![0, 3]),
                    ],
                    vec![0, 1, 2, 3],
                    4,
                ),
            ];

            for (factors, order, nvars) in &queries {
                let factor_rows: Vec<Vec<Vec<Vec<u8>>>> = factors
                    .iter()
                    .map(|fac| {
                        if fac.prefix == pe {
                            e_facts.clone()
                        } else {
                            f_facts.clone()
                        }
                    })
                    .collect();

                let mut got = ground_join(&map, factors, order, *nvars);
                let mut want = {
                    let mut binding = vec![None; *nvars];
                    let mut out = Vec::new();
                    brute_rec(0, factors, &factor_rows, &mut binding, &mut out);
                    out
                };
                got.sort();
                got.dedup();
                want.sort();
                want.dedup();
                assert_eq!(
                    got, want,
                    "seed {seed}: join answers must match the nested loop"
                );
            }
        }
    }

    // The data-parallel ground_join must return byte-identically (as a set) what
    // the sequential ground_join returns: the leading variable's hash partition is
    // a disjoint cover, so the workers' answer sets union to the whole. Checked on
    // a moderate edge relation via the 2-hop join.
    #[test]
    fn ground_join_parallel_matches_sequential() {
        let mut s = crate::space::Space::new();
        let mut prog = String::new();
        for a in 0..48u32 {
            for b in 0..48u32 {
                if (a.wrapping_mul(31).wrapping_add(b.wrapping_mul(17))) % 5 == 0 {
                    prog.push_str(&format!("(edge {} {})\n", a % 13, b % 13));
                }
            }
        }
        s.add_all_sexpr(prog.as_bytes()).unwrap();
        let body = crate::expr!(s, "[3] , [3] edge $ $ [3] edge _2 $");
        let span = unsafe { body.span().as_ref().unwrap() };
        let (factors, nvars) = parse_body_factors(span).expect("parses");
        let var_order: Vec<usize> = (0..nvars).collect();

        let mut seq = ground_join(&s.btm, &factors, &var_order, nvars);
        let mut par = ground_join_parallel(&s.btm, &factors, &var_order, nvars, 32);
        assert!(!seq.is_empty(), "the join must produce answers");
        seq.sort();
        par.sort();
        assert_eq!(seq, par, "parallel join answer set must equal sequential");
    }

    #[test]
    fn least_ge_matches_brute_force() {
        let sets: &[&[u8]] = &[
            &[],
            &[0],
            &[255],
            &[0, 1, 2, 63, 64, 65, 127, 128, 191, 192, 255],
            &[10, 50, 90, 130, 170, 210, 250],
            &[63, 64],
        ];
        for set in sets {
            let mask = mask_of(set);
            for k in 0u8..=255 {
                let want = set.iter().copied().filter(|&b| b >= k).min();
                assert_eq!(least_ge(&mask, k), want, "set={set:?} k={k}");
            }
        }
    }

    #[test]
    fn first_subterm_len_parses_each_shape() {
        // symbol "ab": SymbolSize(2), 'a', 'b'  -> 3 bytes
        let sym = [item_byte(Tag::SymbolSize(2)), b'a', b'b'];
        assert_eq!(first_subterm_len(&sym), 3);
        assert!(first_subterm_is_ground(&sym));

        // NewVar -> 1 byte, non-ground
        let nv = [item_byte(Tag::NewVar)];
        assert_eq!(first_subterm_len(&nv), 1);
        assert!(!first_subterm_is_ground(&nv));

        // VarRef(0) -> 1 byte, non-ground
        let vr = [item_byte(Tag::VarRef(0))];
        assert_eq!(first_subterm_len(&vr), 1);
        assert!(!first_subterm_is_ground(&vr));

        // (k v0):  Arity(2), Sym("k"), Sym("v0")
        let k = item_byte(Tag::SymbolSize(1));
        let v0 = item_byte(Tag::SymbolSize(2));
        let compound = [item_byte(Tag::Arity(2)), k, b'k', v0, b'v', b'0'];
        assert_eq!(first_subterm_len(&compound), 6);
        assert!(first_subterm_is_ground(&compound));

        // (k $x): Arity(2), Sym("k"), NewVar  -> 4 bytes, non-ground
        let compound_var = [item_byte(Tag::Arity(2)), k, b'k', item_byte(Tag::NewVar)];
        assert_eq!(first_subterm_len(&compound_var), 4);
        assert!(!first_subterm_is_ground(&compound_var));

        // trailing bytes after the first subterm are ignored: (e A B) prefix then junk
        let mut buf = compound.to_vec();
        buf.extend_from_slice(&[0xFF, 0xFF]);
        assert_eq!(first_subterm_len(&buf), 6);
    }

    /// A generated fact column: a ground symbol, or a fact variable slot (a slot shared within the
    /// fact encodes as NewVar on first use and VarRef after, so facts can be coreferent).
    enum FCol {
        G(Vec<u8>),
        V(usize),
    }

    fn encode_fact(rel: &str, cols: &[FCol]) -> Vec<u8> {
        let mut v = vec![item_byte(Tag::Arity((1 + cols.len()) as u8))];
        v.extend(sym(rel));
        let mut introduced: Vec<usize> = Vec::new();
        for col in cols {
            match col {
                FCol::G(g) => v.extend_from_slice(g),
                FCol::V(slot) => match introduced.iter().position(|s| s == slot) {
                    Some(idx) => v.push(item_byte(Tag::VarRef(idx as u8))),
                    None => {
                        introduced.push(*slot);
                        v.push(item_byte(Tag::NewVar));
                    }
                },
            }
        }
        v
    }

    fn gen_fact(rng: &mut Lcg, syms: &[Vec<u8>]) -> Vec<FCol> {
        (0..2)
            .map(|_| {
                if rng.below(3) == 0 {
                    FCol::V(rng.below(2))
                } else {
                    FCol::G(syms[rng.below(syms.len())].clone())
                }
            })
            .collect()
    }

    /// A query factor as one expression for the naive reference: the relation prefix followed by
    /// every column, with each query variable encoded as a VarRef of its GLOBAL id. `var_opt`
    /// reads a VarRef id as absolute within its namespace, so all factors share their variables
    /// through namespace `QUERY_NS` with no per-factor renumbering.
    fn naive_query_expr(factor: &Factor) -> Vec<u8> {
        let mut v = factor.prefix.clone();
        for col in &factor.cols {
            match col {
                FactorColumn::Var(id) => v.push(item_byte(Tag::VarRef(*id as u8))),
                FactorColumn::Term(term) => v.extend_from_slice(&term.bytes),
            }
        }
        v
    }

    /// Nested-loop reference join over the SAME stock unifier: pick one fact per factor, unify the
    /// accumulated factor/fact equations with `mork_expr::unify` (pruning at the first failing
    /// level), and at the leaf keep the row when every query variable dereferences to ground. The
    /// leapfrog and this reference share `unify`, so a divergence is in the join order, not the
    /// unification.
    fn naive_rec(
        fi: usize,
        query_exprs: &[Vec<u8>],
        factor_facts: &[Vec<Vec<u8>>],
        chosen: &mut Vec<Vec<u8>>,
        nvars: usize,
        out: &mut BTreeSet<Vec<Vec<u8>>>,
    ) {
        let mut pairs: Vec<(ExprEnv, ExprEnv)> = query_exprs[..fi]
            .iter()
            .zip(chosen.iter())
            .enumerate()
            .map(|(i, (q, f))| {
                (
                    ExprEnv::new(QUERY_NS, expr_from_bytes(q)),
                    ExprEnv::new(1 + i as u8, expr_from_bytes(f)),
                )
            })
            .collect();
        let Ok(bindings) = unify(&mut pairs) else {
            return;
        };
        if fi == query_exprs.len() {
            let mut row = Vec::with_capacity(nvars);
            for v in 0..nvars {
                let mut env = ExprEnv {
                    n: QUERY_NS,
                    v: v as u8,
                    offset: 0,
                    base: expr_from_bytes(&NEW_VAR_EXPR_BYTES),
                };
                loop {
                    let Some(var) = env.var_opt() else { break };
                    match bindings.get(&var) {
                        Some(next) => env = *next,
                        None => return, // still free: the all-ground join drops this row
                    }
                }
                let bytes = unsafe { env.subsexpr().span().as_ref().unwrap() }.to_vec();
                if !first_subterm_is_ground(&bytes) {
                    return;
                }
                row.push(bytes);
            }
            out.insert(row);
            return;
        }
        for fact in &factor_facts[fi] {
            chosen.push(fact.clone());
            naive_rec(fi + 1, query_exprs, factor_facts, chosen, nvars, out);
            chosen.pop();
        }
    }

    #[test]
    fn unify_join_matches_naive_on_schematic_facts() {
        for seed in 0..400u64 {
            let mut rng = Lcg::new(seed.wrapping_add(11));
            let nsyms = 2 + rng.below(2);
            let syms: Vec<Vec<u8>> = (0..nsyms)
                .map(|i| sym(&((b'a' + i as u8) as char).to_string()))
                .collect();

            let mut map = PathMap::<()>::new();
            let mut e_facts: Vec<Vec<u8>> = Vec::new();
            let mut f_facts: Vec<Vec<u8>> = Vec::new();
            let nfacts = 3 + rng.below(6);
            for _ in 0..nfacts {
                let fe = encode_fact("e", &gen_fact(&mut rng, &syms));
                if map.insert(&fe, ()).is_none() {
                    e_facts.push(fe);
                }
                let ff = encode_fact("f", &gen_fact(&mut rng, &syms));
                if map.insert(&ff, ()).is_none() {
                    f_facts.push(ff);
                }
            }
            let pe = relation_prefix("e", 3);
            let pf = relation_prefix("f", 3);

            let queries: Vec<(Vec<Factor>, Vec<usize>, usize)> = vec![
                // single factor  (e $0 $1)
                (
                    vec![Factor::var_cols(pe.clone(), vec![0, 1])],
                    vec![0, 1],
                    2,
                ),
                // path  (e $0 $1)(e $1 $2)
                (
                    vec![
                        Factor::var_cols(pe.clone(), vec![0, 1]),
                        Factor::var_cols(pe.clone(), vec![1, 2]),
                    ],
                    vec![0, 1, 2],
                    3,
                ),
                // star  (e $0 $1)(e $0 $2)
                (
                    vec![
                        Factor::var_cols(pe.clone(), vec![0, 1]),
                        Factor::var_cols(pe.clone(), vec![0, 2]),
                    ],
                    vec![0, 1, 2],
                    3,
                ),
                // two-relation path  (e $0 $1)(f $1 $2)
                (
                    vec![
                        Factor::var_cols(pe.clone(), vec![0, 1]),
                        Factor::var_cols(pf.clone(), vec![1, 2]),
                    ],
                    vec![0, 1, 2],
                    3,
                ),
                // cyclic triangle over schematic edges (the re-index + catch-up path).
                (
                    vec![
                        Factor::var_cols(pe.clone(), vec![0, 1]),
                        Factor::var_cols(pe.clone(), vec![1, 2]),
                        Factor::var_cols(pe.clone(), vec![2, 0]),
                    ],
                    vec![0, 1, 2],
                    3,
                ),
                // cyclic four-cycle over schematic edges.
                (
                    vec![
                        Factor::var_cols(pe.clone(), vec![0, 1]),
                        Factor::var_cols(pe.clone(), vec![1, 2]),
                        Factor::var_cols(pe.clone(), vec![2, 3]),
                        Factor::var_cols(pe.clone(), vec![3, 0]),
                    ],
                    vec![0, 1, 2, 3],
                    4,
                ),
                // swap pair  (e $0 $1)(e $1 $0)
                (
                    vec![
                        Factor::var_cols(pe.clone(), vec![0, 1]),
                        Factor::var_cols(pe.clone(), vec![1, 0]),
                    ],
                    vec![0, 1],
                    2,
                ),
                // intra-factor coreference  (e $0 $0) against schematic facts.
                (vec![Factor::var_cols(pe.clone(), vec![0, 0])], vec![0], 1),
            ];

            for (qi, (factors, order, nvars)) in queries.iter().enumerate() {
                let query_exprs: Vec<Vec<u8>> = factors.iter().map(naive_query_expr).collect();
                let factor_facts: Vec<Vec<Vec<u8>>> = factors
                    .iter()
                    .map(|fac| {
                        if fac.prefix == pe {
                            e_facts.clone()
                        } else {
                            f_facts.clone()
                        }
                    })
                    .collect();

                let got = unify_join_zipper(&map, factors, order, *nvars);
                let mut want = BTreeSet::new();
                let mut chosen = Vec::new();
                naive_rec(
                    0,
                    &query_exprs,
                    &factor_facts,
                    &mut chosen,
                    *nvars,
                    &mut want,
                );
                assert_eq!(
                    got, want,
                    "seed {seed} query {qi}: leapfrog and the stock-unify nested loop must agree"
                );
            }
        }
    }

    /// A generated fact column for the compound-adversarial differential: a ground symbol, a fact
    /// variable slot, or a compound `(k <sub>)` wrapping one of those.
    enum SCol {
        G(Vec<u8>),
        V(usize),
        C(Box<SCol>),
    }

    fn encode_scol(col: &SCol, out: &mut Vec<u8>, introduced: &mut Vec<usize>) {
        match col {
            SCol::G(g) => out.extend_from_slice(g),
            SCol::V(slot) => match introduced.iter().position(|s| s == slot) {
                Some(idx) => out.push(item_byte(Tag::VarRef(idx as u8))),
                None => {
                    introduced.push(*slot);
                    out.push(item_byte(Tag::NewVar));
                }
            },
            SCol::C(sub) => {
                out.push(item_byte(Tag::Arity(2)));
                out.extend(sym("k"));
                encode_scol(sub, out, introduced);
            }
        }
    }

    /// Encode a fact whose HEAD is itself a column, so facts can carry wildcard or compound
    /// heads; slots are shared across the whole fact, head included.
    fn encode_sfact(cols: &[SCol]) -> Vec<u8> {
        let mut v = vec![item_byte(Tag::Arity(cols.len() as u8))];
        let mut introduced = Vec::new();
        for col in cols {
            encode_scol(col, &mut v, &mut introduced);
        }
        v
    }

    /// A fact head: usually the relation symbol, sometimes a wildcard slot, rarely a compound.
    fn gen_head(rng: &mut Lcg, rel: &str) -> SCol {
        match rng.below(10) {
            0..=6 => SCol::G(sym(rel)),
            7 | 8 => SCol::V(rng.below(2)),
            _ => SCol::C(Box::new(SCol::G(sym(rel)))),
        }
    }

    fn gen_scol(rng: &mut Lcg, syms: &[Vec<u8>], depth: usize) -> SCol {
        match rng.below(if depth > 0 { 4 } else { 3 }) {
            0 => SCol::V(rng.below(2)),
            1 | 2 => SCol::G(syms[rng.below(syms.len())].clone()),
            _ => SCol::C(Box::new(gen_scol(rng, syms, depth - 1))),
        }
    }

    /// A factor expression for the naive reference with every variable occurrence rewritten to a
    /// VarRef of its GLOBAL id, so a compound column's NewVar (body numbering) does not renumber
    /// when the factor is read standalone.
    fn globalize_term_vars(term: &EncodedTerm, out: &mut Vec<u8>) {
        let mut intro = term.intro;
        let mut ez = ExprZipper::new(term.expr());
        loop {
            match ez.item() {
                Ok(Tag::NewVar) => {
                    out.push(item_byte(Tag::VarRef(intro)));
                    intro += 1;
                }
                Ok(Tag::VarRef(i)) => out.push(item_byte(Tag::VarRef(i))),
                Ok(Tag::Arity(a)) => out.push(item_byte(Tag::Arity(a))),
                Err(symbol) => {
                    out.push(item_byte(Tag::SymbolSize(symbol.len() as u8)));
                    out.extend_from_slice(symbol);
                }
                Ok(Tag::SymbolSize(_)) => unreachable!(),
            }
            if !ez.next() {
                return;
            }
        }
    }

    fn naive_query_expr_globalized(factor: &Factor) -> Vec<u8> {
        let mut v = factor.prefix.clone();
        for col in &factor.cols {
            match col {
                FactorColumn::Var(id) => v.push(item_byte(Tag::VarRef(*id as u8))),
                FactorColumn::Term(term) => globalize_term_vars(term, &mut v),
            }
        }
        v
    }

    /// Render query variable `v` under `bindings` the way the join's emit does: `None` while it
    /// dereferences to a variable, else the applied bytes, recording cut cycles in `cycled`.
    fn naive_component(
        bindings: &Bindings,
        v: usize,
        cycled: &mut BTreeMap<BindingKey, u8>,
    ) -> Option<Vec<u8>> {
        let mut env = ExprEnv {
            n: QUERY_NS,
            v: v as u8,
            offset: 0,
            base: expr_from_bytes(&NEW_VAR_EXPR_BYTES),
        };
        loop {
            match env.var_opt() {
                Some(var) => match bindings.get(&var) {
                    Some(next) => env = *next,
                    None => return None,
                },
                None => break,
            }
        }
        let mut buf = vec![0u8; 512];
        let mut ez = ExprZipper::new(env.subsexpr());
        let mut oz = ExprZipper::new(Expr {
            ptr: buf.as_mut_ptr(),
        });
        let mut stack = Vec::new();
        let mut assignments = Vec::new();
        #[allow(deprecated)]
        mork_expr::apply(
            env.n,
            env.v,
            0,
            &mut ez,
            bindings,
            &mut oz,
            cycled,
            &mut stack,
            &mut assignments,
        );
        assert!(oz.loc <= buf.len(), "naive render overflow");
        buf.truncate(oz.loc);
        Some(buf)
    }

    /// Nested-loop reference over stock `unify`, keeping PARTIAL rows the way
    /// [`unify_join_zipper_partial`] does, and rejecting a row whose emit cuts a cycle, the way
    /// `Expr::_unify` rejects after apply. This is whole-tuple unification semantics.
    fn naive_partial_rec(
        fi: usize,
        query_exprs: &[Vec<u8>],
        factor_facts: &[Vec<Vec<u8>>],
        chosen: &mut Vec<Vec<u8>>,
        nvars: usize,
        out: &mut BTreeSet<Vec<Option<Vec<u8>>>>,
    ) {
        let mut pairs: Vec<(ExprEnv, ExprEnv)> = query_exprs[..fi]
            .iter()
            .zip(chosen.iter())
            .enumerate()
            .map(|(i, (q, f))| {
                (
                    ExprEnv::new(QUERY_NS, expr_from_bytes(q)),
                    ExprEnv::new(1 + i as u8, expr_from_bytes(f)),
                )
            })
            .collect();
        let Ok(bindings) = unify(&mut pairs) else {
            return;
        };
        if fi == query_exprs.len() {
            let mut cycled = BTreeMap::new();
            let row: Vec<Option<Vec<u8>>> = (0..nvars)
                .map(|v| naive_component(&bindings, v, &mut cycled))
                .collect();
            if cycled.is_empty() {
                out.insert(row);
            }
            return;
        }
        for fact in &factor_facts[fi] {
            chosen.push(fact.clone());
            naive_partial_rec(fi + 1, query_exprs, factor_facts, chosen, nvars, out);
            chosen.pop();
        }
    }

    fn row_str(row: &[Option<Vec<u8>>]) -> String {
        row.iter()
            .map(|c| match c {
                Some(bytes) => format!("{bytes:?}"),
                None => "free".to_string(),
            })
            .collect::<Vec<_>>()
            .join(" | ")
    }

    /// The adversarial differential around the routing boundary: compound-schematic facts against
    /// query shapes centered on join-propagated capture, RAW join (no router) versus the
    /// whole-tuple-unification reference. `ADV_N` overrides the seed count for deep runs.
    #[test]
    fn raw_join_matches_naive_on_compound_capture_shapes() {
        let seeds: u64 = std::env::var("ADV_N")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(300);
        // (name, body): variables number in first-occurrence order.
        let templates: Vec<(&str, Vec<u8>)> = vec![
            (
                "flat-swap",
                conj(&[
                    nest("e", &[new_var(), new_var()]),
                    nest("h", &[var_ref(1), var_ref(0)]),
                ]),
            ),
            (
                "propagated-3",
                conj(&[
                    nest("e", &[nest("k", &[new_var()]), new_var()]),
                    nest("e", &[nest("k", &[var_ref(1)]), new_var()]),
                    nest("h", &[var_ref(2), var_ref(0)]),
                ]),
            ),
            (
                "propagated-2",
                conj(&[
                    nest("e", &[nest("k", &[new_var()]), new_var()]),
                    nest("h", &[nest("k", &[var_ref(1)]), var_ref(0)]),
                ]),
            ),
            (
                "self-capture",
                conj(&[nest("e", &[nest("k", &[new_var()]), var_ref(0)])]),
            ),
            (
                "late-compound",
                conj(&[
                    nest("e", &[new_var(), new_var()]),
                    nest("h", &[nest("k", &[var_ref(0)]), var_ref(1)]),
                ]),
            ),
            (
                "two-compounds",
                conj(&[
                    nest("e", &[nest("k", &[new_var()]), nest("k", &[new_var()])]),
                    nest("h", &[var_ref(1), var_ref(0)]),
                ]),
            ),
            (
                "nested-compound",
                conj(&[
                    nest("e", &[nest("k", &[nest("k", &[new_var()])]), new_var()]),
                    nest("h", &[var_ref(1), var_ref(0)]),
                ]),
            ),
            (
                "ground-and-compound",
                conj(&[
                    nest("e", &[nest("k", &[new_var()]), sym("a")]),
                    nest("h", &[var_ref(0), new_var()]),
                ]),
            ),
            ("variable-head", {
                let mut v = vec![item_byte(Tag::Arity(3)), item_byte(Tag::NewVar)];
                v.extend(sym("a"));
                v.push(item_byte(Tag::NewVar));
                conj(&[v])
            }),
            ("variable-head-join", {
                let mut v = vec![item_byte(Tag::Arity(3)), item_byte(Tag::NewVar)];
                v.push(item_byte(Tag::NewVar));
                v.extend(sym("b"));
                conj(&[v, nest("e", &[var_ref(1), var_ref(0)])])
            }),
            // Total arity 4 with a coreferent tail: the shape the example harness must exclude
            // (it would match the harness's own machinery atoms); here the reference is machinery-free.
            ("variable-head-4", {
                let mut v = vec![item_byte(Tag::Arity(4)), item_byte(Tag::NewVar)];
                v.push(item_byte(Tag::NewVar));
                v.push(item_byte(Tag::NewVar));
                v.push(item_byte(Tag::VarRef(2)));
                conj(&[v])
            }),
        ];
        let syms: Vec<Vec<u8>> = vec![sym("a"), sym("b")];
        for seed in 0..seeds {
            let mut rng = Lcg::new(seed.wrapping_add(101));
            let mut map = PathMap::<()>::new();
            let mut e_facts: Vec<Vec<u8>> = Vec::new();
            let mut h_facts: Vec<Vec<u8>> = Vec::new();
            let nfacts = 3 + rng.below(5);
            for _ in 0..nfacts {
                let mut ecols = vec![
                    gen_head(&mut rng, "e"),
                    gen_scol(&mut rng, &syms, 2),
                    gen_scol(&mut rng, &syms, 2),
                ];
                if rng.below(3) == 0 {
                    ecols.push(gen_scol(&mut rng, &syms, 1));
                }
                let fe = encode_sfact(&ecols);
                if map.insert(&fe, ()).is_none() {
                    e_facts.push(fe);
                }
                let fh = encode_sfact(&[
                    gen_head(&mut rng, "h"),
                    gen_scol(&mut rng, &syms, 2),
                    gen_scol(&mut rng, &syms, 2),
                ]);
                if map.insert(&fh, ()).is_none() {
                    h_facts.push(fh);
                }
            }
            // Guaranteed cycle-stress: the coreferent wildcard facts the propagated capture needs.
            for (rel, facts) in [("e", &mut e_facts), ("h", &mut h_facts)] {
                if rng.below(2) == 0 {
                    let f = encode_sfact(&[SCol::G(sym(rel)), SCol::V(0), SCol::V(0)]);
                    if map.insert(&f, ()).is_none() {
                        facts.push(f);
                    }
                }
            }
            let all_facts: Vec<Vec<u8>> = e_facts.iter().chain(h_facts.iter()).cloned().collect();

            for (name, body) in &templates {
                let Some((factors, nvars)) = parse_body_factors(body) else {
                    panic!("{name}: template must parse");
                };
                let order: Vec<usize> = (0..nvars).collect();
                let got = catch_unwind(AssertUnwindSafe(|| {
                    unify_join_zipper_partial(&map, &factors, &order, nvars)
                }))
                .unwrap_or_else(|_| panic!("seed {seed} {name}: raw join panicked"));

                let query_exprs: Vec<Vec<u8>> =
                    factors.iter().map(naive_query_expr_globalized).collect();
                let factor_facts: Vec<Vec<Vec<u8>>> =
                    factors.iter().map(|_| all_facts.clone()).collect();
                let mut want = BTreeSet::new();
                let mut chosen = Vec::new();
                naive_partial_rec(
                    0,
                    &query_exprs,
                    &factor_facts,
                    &mut chosen,
                    nvars,
                    &mut want,
                );

                if got != want {
                    let missing: Vec<String> = want.difference(&got).map(|r| row_str(r)).collect();
                    let extra: Vec<String> = got.difference(&want).map(|r| row_str(r)).collect();
                    panic!(
                        "seed {seed} {name}: raw join != whole-tuple unification\n  naive-only: {missing:?}\n  zipper-only: {extra:?}"
                    );
                }
            }
        }
    }
    /// The head position is a join column like any other. A variable query head ranges over
    /// stored heads, and a wildcard stored head is captured under a ground query head; with the
    /// head baked into the seek prefix, both directions were silently empty (caught against the
    /// ProductZipper, which unifies at the head).
    #[test]
    fn head_position_unifies_both_directions() {
        // ($p a $x) over (e a b), (f a c): the variable head takes each stored head.
        let mut m1 = PathMap::<()>::new();
        m1.insert(&nest("e", &[sym("a"), sym("b")]), ());
        m1.insert(&nest("f", &[sym("a"), sym("c")]), ());
        let body1 = conj(&[{
            let mut v = vec![item_byte(Tag::Arity(3)), item_byte(Tag::NewVar)];
            v.extend(sym("a"));
            v.push(item_byte(Tag::NewVar));
            v
        }]);
        let rows1 = unify_join_zipper_body_safe(&m1, &body1).expect("variable head routes");
        let expected1 = BTreeSet::from([vec![sym("e"), sym("b")], vec![sym("f"), sym("c")]]);
        assert_eq!(
            rows1, expected1,
            "variable head must unify with stored heads"
        );

        // (e a $x) over ($u a b), (e a c): the wildcard stored head captures the query head.
        let mut m2 = PathMap::<()>::new();
        let mut wild = vec![item_byte(Tag::Arity(3)), item_byte(Tag::NewVar)];
        wild.extend(sym("a"));
        wild.extend(sym("b"));
        m2.insert(&wild, ());
        m2.insert(&nest("e", &[sym("a"), sym("c")]), ());
        let body2 = conj(&[nest("e", &[sym("a"), new_var()])]);
        let rows2 = unify_join_zipper_body_safe(&m2, &body2).expect("ground head routes");
        let expected2 = BTreeSet::from([vec![sym("b")], vec![sym("c")]]);
        assert_eq!(rows2, expected2, "wildcard stored head must be captured");
    }

    // ===== Engine dispatch differentials: the wired `metta_calculus` against the stock path =====

    /// Encode one atom with MORK's own parser: insert it into a scratch space and read the key
    /// back, so the bytes are exactly what the engine stores.
    fn enc(sexpr: &str) -> Vec<u8> {
        let mut s = crate::space::Space::new();
        s.add_all_sexpr(sexpr.as_bytes()).unwrap();
        let mut rz = s.btm.read_zipper();
        assert!(rz.to_next_val(), "one atom expected in {sexpr:?}");
        rz.path().to_vec()
    }

    fn space_paths(space: &crate::space::Space) -> BTreeSet<Vec<u8>> {
        let mut set = BTreeSet::new();
        let mut rz = space.btm.read_zipper();
        while rz.to_next_val() {
            set.insert(rz.path().to_vec());
        }
        set
    }

    /// Run `program` for `steps` with the dispatch pinned off, then on, returning
    /// (performed steps, space paths) for each arm. Leaves the dispatch on, the default.
    fn engine_both_ways(
        program: &str,
        steps: usize,
    ) -> ((usize, BTreeSet<Vec<u8>>), (usize, BTreeSet<Vec<u8>>)) {
        let mut run = |on: bool| {
            let mut s = crate::space::Space::new();
            s.add_all_sexpr(program.as_bytes()).unwrap();
            set_leapfrog_dispatch(on);
            let performed = s.metta_calculus(steps);
            set_leapfrog_dispatch(true);
            (performed, space_paths(&s))
        };
        (run(false), run(true))
    }

    /// Every resource program, run to several depths with the dispatch off and on: the performed
    /// step counts and the full space bytes must agree. The decision-tree programs and the sudoku
    /// get a small step cap to keep the suite fast; the point here is the dispatch decision and
    /// the emit on every body shape the corpus uses, and `run.sh` sweeps the full runs.
    #[test]
    fn engine_dispatch_matches_stock_on_resources() {
        let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/resources");
        let mut checked = 0;
        for entry in std::fs::read_dir(dir).expect("resources dir") {
            let path = entry.expect("dir entry").path();
            if path.extension().and_then(|e| e.to_str()) != Some("mm2") {
                continue;
            }
            let name = path.file_stem().unwrap().to_str().unwrap().to_string();
            let program = std::fs::read_to_string(&path).expect("readable resource");
            let steps_list: &[usize] = if name.starts_with("decision_tree") || name == "ip_sudoku" {
                &[1, 7]
            } else {
                &[1, 7, 40]
            };
            for &steps in steps_list {
                let ((p0, s0), (p1, s1)) = engine_both_ways(&program, steps);
                assert_eq!(p0, p1, "{name} steps={steps}: performed step counts differ");
                assert_eq!(s0, s1, "{name} steps={steps}: spaces differ");
            }
            checked += 1;
        }
        assert!(
            checked >= 8,
            "expected the resource corpus, found {checked}"
        );
    }

    /// The variables of the patterns in first-occurrence order, by `$name`.
    fn dollar_vars_of(patterns: &[String]) -> Vec<String> {
        let mut seen: Vec<String> = Vec::new();
        for p in patterns {
            let b = p.as_bytes();
            let mut i = 0;
            while i < b.len() {
                if b[i] == b'$' {
                    let mut j = i + 1;
                    while j < b.len() && (b[j].is_ascii_alphanumeric() || b[j] == b'_') {
                        j += 1;
                    }
                    let name = p[i..j].to_string();
                    if !seen.contains(&name) {
                        seen.push(name);
                    }
                    i = j;
                } else {
                    i += 1;
                }
            }
        }
        seen
    }

    fn pick<'x>(rng: &mut Lcg, xs: &[&'x str]) -> &'x str {
        xs[rng.below(xs.len())]
    }

    /// A random pattern atom over relation or query-variable heads, constant, variable, and
    /// compound columns, at total arity 2..=4. Unlike the example's generator there is no arity
    /// constraint: both arms run full evaluation, so a variable-headed arity-4 pattern is free to
    /// match the `(exec ..)` machinery and emitted rows, and the arms must still agree.
    fn rand_pattern_atom(rng: &mut Lcg) -> String {
        let rels = ["e", "p", "q"];
        let qvars = ["$x", "$y", "$z"];
        let consts = ["a", "b", "c"];
        let head = if rng.below(8) == 0 {
            pick(rng, &qvars).to_string()
        } else {
            pick(rng, &rels).to_string()
        };
        let arity = 1 + rng.below(3);
        let args: Vec<String> = (0..arity)
            .map(|_| {
                let base = if rng.below(3) == 0 {
                    pick(rng, &consts)
                } else {
                    pick(rng, &qvars)
                }
                .to_string();
                if rng.below(6) == 0 {
                    format!("(k {base})")
                } else {
                    base
                }
            })
            .collect();
        format!("({head} {})", args.join(" "))
    }

    /// A random stored fact: constants, data variables (schematic facts), compound columns, and a
    /// wildcard head one time in eight.
    fn rand_fact_atom(rng: &mut Lcg) -> String {
        let rels = ["e", "p", "q"];
        let dvars = ["$u", "$v"];
        let consts = ["a", "b", "c", "d"];
        let head = if rng.below(8) == 0 {
            pick(rng, &dvars).to_string()
        } else {
            pick(rng, &rels).to_string()
        };
        let arity = 1 + rng.below(3);
        let args: Vec<String> = (0..arity)
            .map(|_| {
                let base = if rng.below(4) == 0 {
                    pick(rng, &dvars)
                } else {
                    pick(rng, &consts)
                }
                .to_string();
                if rng.below(6) == 0 {
                    format!("(k {base})")
                } else {
                    base
                }
            })
            .collect();
        format!("({head} {})", args.join(" "))
    }

    /// A random template: body variables, constants, fresh variables, compounds, or one time in
    /// six a further `(exec ..)` atom whose body consumes this exec's output relation, so a later
    /// step chains on the first one's writes.
    fn rand_template(rng: &mut Lcg, body_vars: &[String], j: usize) -> String {
        if rng.below(6) == 0 && !body_vars.is_empty() {
            let v = &body_vars[rng.below(body_vars.len())];
            return format!("(exec zc{j} (, (out{j} {v} $cw)) (, (chain{j} $cw {v})))");
        }
        let n = 1 + rng.below(3);
        let parts: Vec<String> = (0..n)
            .map(|_| {
                let piece = if !body_vars.is_empty() && rng.below(3) != 0 {
                    body_vars[rng.below(body_vars.len())].clone()
                } else if rng.below(4) == 0 {
                    "$fresh".to_string()
                } else {
                    pick(rng, &["a", "b", "c"]).to_string()
                };
                if rng.below(6) == 0 {
                    format!("(k {piece})")
                } else {
                    piece
                }
            })
            .collect();
        format!("(out{j} {})", parts.join(" "))
    }

    /// A random whole program: facts, then one to three exec atoms with distinct priorities, each
    /// with one to three patterns and one or two templates, run for one to five steps.
    fn random_program(rng: &mut Lcg) -> (String, usize) {
        let mut prog = String::new();
        for _ in 0..rng.below(9) {
            prog.push_str(&rand_fact_atom(rng));
            prog.push('\n');
        }
        let nexec = 1 + rng.below(3);
        for j in 0..nexec {
            let npat = 1 + rng.below(3);
            let pats: Vec<String> = (0..npat).map(|_| rand_pattern_atom(rng)).collect();
            let vars = dollar_vars_of(&pats);
            let ntpl = 1 + rng.below(2);
            let tpls: Vec<String> = (0..ntpl)
                .map(|t| rand_template(rng, &vars, j * 4 + t))
                .collect();
            prog.push_str(&format!(
                "(exec pr{j} (, {}) (, {}))\n",
                pats.join(" "),
                tpls.join(" ")
            ));
        }
        (prog, 1 + rng.below(5))
    }

    /// Whole random programs through full `metta_calculus`, dispatch off and on: multi-step runs,
    /// chained exec atoms, machinery collisions and all, the arms must agree byte for byte.
    /// `MORK_DISPATCH_N` scales the seed count; the sealing run used a much larger one.
    #[test]
    fn engine_dispatch_matches_stock_on_random_programs() {
        let n: usize = std::env::var("MORK_DISPATCH_N")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(600);
        let mut rng = Lcg(0x9E3779B97F4A7C15);
        for i in 0..n {
            let (prog, steps) = random_program(&mut rng);
            let ((p0, s0), (p1, s1)) = engine_both_ways(&prog, steps);
            assert_eq!(p0, p1, "trial {i}: performed step counts differ on\n{prog}");
            assert_eq!(s0, s1, "trial {i}: spaces differ on\n{prog}");
        }
    }

    /// The dispatch policy is cyclicity modulo functional dependencies, refined by the instance:
    /// tiny queries decline, deep cyclic bodies dispatch, shallow ones dispatch only on a sampled
    /// heavy hitter, and functionally determined bodies decline after the data probe. Correctness
    /// never depends on this routing, but the boundary is the performance contract, so pin every
    /// clause.
    #[test]
    fn dispatch_policy_follows_cyclicity_modulo_fds() {
        // A hub graph (the skewed instance), a branching uniform graph (non-functional, low
        // degree), and four functional 12x12 tables for the FD diamond.
        let mut text = String::new();
        for k in 0..64 {
            text.push_str(&format!("(hub h o{k})\n(hub i{k} h)\n"));
        }
        for k in 0..128 {
            text.push_str(&format!("(uni n{k} n{})\n(uni n{k} m{k})\n", (k + 1) % 128));
        }
        for x in 0..12 {
            for y in 0..12 {
                text.push_str(&format!(
                    "(fa {x} {y} = r{})\n(fb {x} {y} = r{})\n",
                    (x + y) % 12,
                    (x * y) % 12
                ));
                text.push_str(&format!(
                    "(fc r{x} r{y} = s{})\n(fd r{x} r{y} = s{})\n",
                    (x + y) % 12,
                    (x + 2 * y) % 12
                ));
            }
        }
        text.push_str("(e a b)\n(e a c)\n(e b c)\n");
        let mut s = crate::space::Space::new();
        s.add_all_sexpr(text.as_bytes()).unwrap();
        let case = |body: &str| -> bool {
            let b = enc(body);
            let (factors, nvars) = parse_body_factors(&b).unwrap();
            body_factors_profit_from_leapfrog(&s.btm, &factors, nvars)
        };
        assert!(
            case("(, (hub $x $y) (hub $y $z) (hub $x $z))"),
            "a triangle through a sampled heavy hitter must dispatch"
        );
        assert!(
            !case("(, (uni $x $y) (uni $y $z) (uni $x $z))"),
            "a uniform triangle has no heavy hitter and must decline"
        );
        assert!(
            case("(, (uni $a $b) (uni $b $c) (uni $c $d) (uni $d $a))"),
            "a deep cyclic body dispatches on product depth alone"
        );
        assert!(
            !case("(, (fa $x $y = $u) (fb $x $y = $v) (fc $u $v = $w) (fd $u $v = $z))"),
            "a functional diamond is FD-acyclic and must decline"
        );
        assert!(
            !case("(, (e $x $y) (e $y $z) (e $x $z))"),
            "a tiny query declines whatever its shape"
        );
        assert!(
            !case("(, (uni $x $y) (uni $y $z))"),
            "an acyclic path must decline on GYO alone"
        );
        assert!(
            !case("(, (p $x (q $y)) (r $y (s $z)) (t $z (u $x)))"),
            "a cycle carried only inside compounds has nothing the leapfrog can seek"
        );
    }

    /// Bodies the router does not own (a bare-variable factor, the empty conjunction) must fall
    /// back to the stock path and agree with it exactly; the bare variable also matches the exec
    /// atom itself in the read copy, both ways.
    #[test]
    fn nonroutable_bodies_take_the_stock_path_identically() {
        for (prog, steps) in [
            ("(m a)\n(exec 0 (, $x) (, (saw $x)))\n", 1usize),
            ("(m a)\n(exec 0 (,) (, (once)))\n", 1),
        ] {
            let ((p0, s0), (p1, s1)) = engine_both_ways(prog, steps);
            assert_eq!(p0, p1, "performed step counts differ on\n{prog}");
            assert_eq!(s0, s1, "spaces differ on\n{prog}");
        }
    }

    /// Model 14 in the running engine: for a cyclic body the GHD's full tuples (a matched fact per
    /// factor, joined across the bags) equal the global WCO join's full tuples as a set. This is
    /// the correctness gate for `query_multi_ghd`: identical tuples feed the identical unify+effect.
    #[test]
    fn ghd_full_tuples_match_global_join_on_cycles() {
        let mut s = crate::space::Space::new();
        s.add_all_sexpr(
            "(e a b)\n(e b c)\n(e c a)\n(e a c)\n(e c b)\n(e b a)\n\
             (e a d)\n(e d c)\n(e c d)\n(e d a)\n(e b d)\n(e d b)\n"
                .as_bytes(),
        )
        .unwrap();
        for body_str in [
            "(, (e $x $y) (e $y $z) (e $z $x))",           // triangle, ghw 2
            "(, (e $a $b) (e $b $c) (e $c $d) (e $d $a))", // 4-cycle, ghw 2
        ] {
            let body = enc(body_str);
            let (factors, nvars) = parse_body_factors(&body).unwrap();

            let var_order: Vec<usize> = (0..nvars).collect();
            let mut global: BTreeSet<Vec<Vec<u8>>> = BTreeSet::new();
            run_unify_join_stream(&s.btm, &factors, &var_order, nvars, &mut |t| {
                global.insert(t.to_vec());
                true
            });

            let edges = crate::ghd::hypergraph(&factors);
            let ghd = crate::ghd::decompose(&edges, 3).expect("cyclic body decomposes");
            assert_eq!(ghd.width, 2, "{body_str}: cyclic body has width 2");
            let bags_mat: Vec<_> = ghd
                .bags
                .iter()
                .map(|b| (b.clone(), crate::ghd::materialize_bag(&s.btm, &factors, b, nvars)))
                .collect();
            let ghd_tuples: BTreeSet<Vec<Vec<u8>>> =
                crate::ghd::join_bags(&bags_mat, factors.len()).into_iter().collect();

            assert_eq!(global, ghd_tuples, "{body_str}: GHD tuples must equal the global join");
            assert!(!global.is_empty(), "{body_str}: the test must exercise non-empty results");
        }
    }

    /// Factorized aggregation (Model 17): the factorized COUNT equals enumerate-and-count, while
    /// touching only the input rows. The 2-path has O(N^2) output but O(N) input, so the factorized
    /// count does asymptotically less work for the same answer.
    #[test]
    fn ghd_count_matches_enumerate_count() {
        let mut s = crate::space::Space::new();
        let mut prog = String::new();
        for a in 0..5 {
            for h in 0..4 {
                prog.push_str(&format!("(r a{a} h{h})\n"));
            }
        }
        for h in 0..4 {
            for z in 0..5 {
                prog.push_str(&format!("(s h{h} z{z})\n"));
            }
        }
        s.add_all_sexpr(prog.as_bytes()).unwrap();
        for body_str in [
            "(, (r $x $y) (s $y $z))", // 2-path: output 100, inputs 40
            "(, (r $x $y))",           // single relation
        ] {
            let body = enc(body_str);
            let (factors, nvars) = parse_body_factors(&body).unwrap();
            let var_order: Vec<usize> = (0..nvars).collect();
            let mut enum_count = 0u64;
            run_unify_join_stream(&s.btm, &factors, &var_order, nvars, &mut |_t| {
                enum_count += 1;
                true
            });
            let fact_count = crate::ghd::ghd_count(&s.btm, &factors, nvars, &var_order);
            assert_eq!(fact_count, enum_count, "{body_str}: factorized != enumerate count");
            assert!(enum_count > 0, "{body_str}: the test must exercise non-empty results");
        }
    }

    /// A disconnected body is a Cartesian product and still factorizes: `(foo $x)(bar $y)(baz $z)`
    /// -- the `sink_count_literal` shape -- has no shared variable, so its count is |foo|*|bar|*|baz|
    /// computed in O(sum) not O(product) (Yan-Larson "double eager"). Before the connected-components
    /// split, gyo rejected the disconnected hypergraph and ghd_aggregate_auto returned None; now each
    /// component decomposes on its own and ghd_aggregate multiplies the per-component scalars.
    #[test]
    fn ghd_count_cartesian_product_factorizes() {
        let mut s = crate::space::Space::new();
        s.add_all_sexpr(b"(foo 1) (foo 2) (foo 3) (bar x) (bar y) (baz P) (baz Q) (baz R)")
            .unwrap();
        let body = enc("(, (foo $x) (bar $y) (baz $z))");
        let (factors, nvars) = parse_body_factors(&body).unwrap();
        let var_order: Vec<usize> = (0..nvars).collect();
        let mut enum_count = 0u64;
        run_unify_join_stream(&s.btm, &factors, &var_order, nvars, &mut |_t| {
            enum_count += 1;
            true
        });
        let fact_count = crate::ghd::ghd_aggregate_auto::<u64>(&s.btm, &factors, nvars, |_| 1)
            .expect("the disconnected body factorizes per connected component");
        assert_eq!(enum_count, 18, "3*2*3 Cartesian product");
        assert_eq!(fact_count, enum_count, "factorized Cartesian count != enumerate");
    }

    /// Run a count-sink program to fixpoint with the factorized fast path forced on/off and return
    /// the whole-space dump, for the differential oracles below.
    fn count_diff_run(prog: &str, factorized: bool) -> String {
        crate::space::set_factorized_count_override(Some(factorized));
        let mut s = crate::space::Space::new();
        s.add_all_sexpr(prog.as_bytes()).unwrap();
        s.metta_calculus(1_000_000);
        let mut v = vec![];
        s.dump_all_sexpr(&mut v).unwrap();
        crate::space::set_factorized_count_override(None);
        String::from_utf8(v).unwrap()
    }

    /// A CONNECTED multi-factor join routed through the count sink: the flybase P1 star
    /// `(gene $x)(rel1 $x $y)(rel2 $x $z)`, full projection, no grouping. Unlike the Cartesian case
    /// this exercises the connected GHD decomposition end to end. 1 gene * 2 rel1 * 3 rel2 = 6.
    #[test]
    fn factorized_count_sink_routes_connected_star() {
        const PROG: &str = r#"
(gene x)
(rel1 x a) (rel1 x b)
(rel2 x p) (rel2 x q) (rel2 x r)
(exec 0 (, (gene $x) (rel1 $x $y) (rel2 $x $z)) (O (count (star $c) $c (out $x $y $z))))
"#;
        let enumerated = count_diff_run(PROG, false);
        let factorized = count_diff_run(PROG, true);
        assert!(enumerated.contains("(star 6)"), "1*2*3 star count:\n{enumerated}");
        assert_eq!(factorized, enumerated, "connected-star factorized diverged from enumerate");
    }

    /// Proof the wired fast path is actually taken and wins through the exec, not silently falling
    /// back: the same count exec at growing scale, factorized vs enumerate. The star has k*k output
    /// but O(k) inputs, so a routed factorized count grows its lead (a dropped exponent); if it did
    /// not route, both would be O(k^2) and the speedup would stay ~1x. Byte-identical each k.
    #[test]
    #[ignore = "timing: the wired count sink, factorized vs enumerate through the exec"]
    fn factorized_count_sink_win_scales() {
        for k in [50usize, 100, 200, 400, 800] {
            let mut prog = String::from("(gene x)\n");
            for y in 0..k {
                prog.push_str(&format!("(rel1 x a{y})\n"));
            }
            for z in 0..k {
                prog.push_str(&format!("(rel2 x b{z})\n"));
            }
            prog.push_str(
                "(exec 0 (, (gene $x) (rel1 $x $y) (rel2 $x $z)) (O (count (star $c) $c (out $x $y $z))))\n",
            );
            let t = std::time::Instant::now();
            let enumerated = count_diff_run(&prog, false);
            let enum_us = t.elapsed().as_micros().max(1);
            let t = std::time::Instant::now();
            let factorized = count_diff_run(&prog, true);
            let fact_us = t.elapsed().as_micros().max(1);
            assert_eq!(factorized, enumerated, "diverged at k={k}");
            assert!(enumerated.contains(&format!("(star {})", k * k)), "count k*k at k={k}");
            eprintln!(
                "k={k:4} count={:8}  enumerate {enum_us:9}us  factorized {fact_us:7}us  speedup {:.1}x",
                k * k,
                enum_us as f64 / fact_us as f64
            );
        }
    }

    /// Differential oracle for the wired count sink: the same count exec, run with the factorized
    /// fast path off (enumerate) and on, must leave a byte-identical space. The body
    /// `(foo $x)(bar $y)(baz $z)` is a 3-way Cartesian counted with full projection and no grouping
    /// -- the routable case (Alloy fac18). `(total $c)` emits the actual count so the value is
    /// compared, not just presence; the `(all eighteen)`/`(all sixteen)` literal guards check the
    /// count-equals-literal emit both ways. This is the gate that must be green before any default
    /// flip of `MORK_FACTORIZED_COUNT`.
    #[test]
    fn factorized_count_sink_matches_enumerate() {
        const PROG: &str = r#"
(foo 1) (foo 2) (foo 3)
(bar x) (bar y)
(baz P) (baz Q) (baz R)
(exec 0 (, (foo $x) (bar $y) (baz $z)) (O (count (total $c) $c (cux $z $y $x))))
(exec 0 (, (foo $x) (bar $y) (baz $z)) (O (count (all eighteen) 18 (cux $z $y $x))))
(exec 0 (, (foo $x) (bar $y) (baz $z)) (O (count (all sixteen) 16 (cux $z $y $x))))
"#;
        let enumerated = count_diff_run(PROG, false);
        let factorized = count_diff_run(PROG, true);
        assert!(
            enumerated.contains("(total 18)"),
            "enumerate must emit the actual count:\n{enumerated}"
        );
        assert_eq!(
            factorized, enumerated,
            "factorized COUNT diverged from the enumerate CountSink"
        );
    }

    /// Adversarial half of the corpus: the gate must DECLINE counts where match-count != distinct
    /// output and fall back to enumerate, so the space stays byte-identical with the fast path on.
    /// A grouped count `(grouped $g $c)` (a pattern variable in the template) is per-group, not a
    /// scalar; a projected count `(only $x)` drops join variables so distinct-output < matches. If
    /// the gate wrongly routed either, the factorized match-count (18) would replace the true
    /// grouped/distinct counts and this differential would fail.
    #[test]
    fn factorized_count_gate_declines_grouped_and_projected() {
        const PROG: &str = r#"
(foo 1) (foo 2) (foo 3)
(bar x) (bar y)
(baz P) (baz Q) (baz R)
(rel a m) (rel a n) (rel b m)
(rel2 m p) (rel2 n q) (rel2 m r)
(exec 0 (, (foo $x) (bar $y) (baz $z)) (O (count (sound-total $c) $c (cux $z $y $x))))
(exec 0 (, (rel $g $h) (rel2 $h $k)) (O (count (grouped $g $c) $c ($h $k))))
(exec 0 (, (foo $x) (bar $y) (baz $z)) (O (count (projected $c) $c (only $x))))
"#;
        let enumerated = count_diff_run(PROG, false);
        let factorized = count_diff_run(PROG, true);
        // the sound one routes; distinct x is 3 not 18 (projection drops y,z); grouping is per g.
        assert!(enumerated.contains("(sound-total 18)"), "sound count:\n{enumerated}");
        assert!(enumerated.contains("(projected 3)"), "distinct x is 3:\n{enumerated}");
        assert_eq!(
            factorized, enumerated,
            "the gate must decline grouped/projected counts and stay byte-identical"
        );
    }

    /// One sum-product engine, many semirings: COUNT (naturals), EXISTS (booleans), and a weighted
    /// SUM all run through `ghd_aggregate` with only the element type and per-fact weight changing.
    /// This is the FAQ generalization -- weighted joins and existence share the factorization.
    #[test]
    fn ghd_aggregate_over_semirings() {
        let mut s = crate::space::Space::new();
        let mut prog = String::new();
        for a in 0..5 {
            for h in 0..3 {
                prog.push_str(&format!("(r a{a} h{h})\n"));
            }
        }
        for h in 0..3 {
            for z in 0..4 {
                prog.push_str(&format!("(s h{h} z{z})\n"));
            }
        }
        s.add_all_sexpr(prog.as_bytes()).unwrap();
        let body = enc("(, (r $x $y) (s $y $z))");
        let (factors, nvars) = parse_body_factors(&body).unwrap();
        let order: Vec<usize> = (0..nvars).collect();

        let count = crate::ghd::ghd_aggregate::<u64>(&s.btm, &factors, nvars, &order, |_| 1);
        let exists = crate::ghd::ghd_aggregate::<bool>(&s.btm, &factors, nvars, &order, |_| true);
        let wsum = crate::ghd::ghd_aggregate::<u64>(&s.btm, &factors, nvars, &order, |_| 2);

        assert!(count > 0, "the test must exercise matches");
        assert!(exists, "EXISTS holds when there is a match");
        assert_eq!(wsum, count * (1u64 << factors.len()), "weight 2 per fact gives 2^m * count");
    }

    /// The elimination order comes from the join tree, not the caller: a 3-chain r-s-t decomposes
    /// to a width-1 GHD, `ghd_aggregate_auto` derives a leaf-first order, and the factorized count
    /// equals enumerate-and-count.
    #[test]
    fn ghd_aggregate_auto_derives_order_on_a_chain() {
        let mut s = crate::space::Space::new();
        let mut prog = String::new();
        for x in 0..3 {
            for y in 0..3 {
                prog.push_str(&format!("(r x{x} y{y})\n"));
            }
        }
        for y in 0..3 {
            for z in 0..3 {
                prog.push_str(&format!("(s y{y} z{z})\n"));
            }
        }
        for z in 0..3 {
            for w in 0..3 {
                prog.push_str(&format!("(t z{z} w{w})\n"));
            }
        }
        s.add_all_sexpr(prog.as_bytes()).unwrap();
        let body = enc("(, (r $x $y) (s $y $z) (t $z $w))");
        let (factors, nvars) = parse_body_factors(&body).unwrap();
        let var_order: Vec<usize> = (0..nvars).collect();
        let mut ec = 0u64;
        run_unify_join_stream(&s.btm, &factors, &var_order, nvars, &mut |_t| {
            ec += 1;
            true
        });
        let fc = crate::ghd::ghd_aggregate_auto::<u64>(&s.btm, &factors, nvars, |_| 1)
            .expect("the chain decomposes");
        assert_eq!(fc, ec, "auto factorized count must equal enumerate");
        assert!(ec > 0, "the test must exercise matches");
    }

    /// The asymptotic separation: on a hub 2-path (k inputs, k^2 output) enumerate-and-count is
    /// O(k^2) while the factorized count is O(k), so the speedup grows with k. This is the win the
    /// WCO join cannot match: the same COUNT, without touching the output.
    #[test]
    #[ignore = "timing: run explicitly for the factorized-count separation"]
    fn ghd_count_win_scales() {
        for k in [50usize, 100, 200, 400, 800] {
            let mut s = crate::space::Space::new();
            let mut prog = String::new();
            for a in 0..k {
                prog.push_str(&format!("(r a{a} hub)\n"));
            }
            for z in 0..k {
                prog.push_str(&format!("(s hub z{z})\n"));
            }
            s.add_all_sexpr(prog.as_bytes()).unwrap();
            let body = enc("(, (r $x $y) (s $y $z))");
            let (factors, nvars) = parse_body_factors(&body).unwrap();
            let var_order: Vec<usize> = (0..nvars).collect();

            let t = std::time::Instant::now();
            let mut ec = 0u64;
            run_unify_join_stream(&s.btm, &factors, &var_order, nvars, &mut |_t| {
                ec += 1;
                true
            });
            let enum_us = t.elapsed().as_micros().max(1);

            let t = std::time::Instant::now();
            let fc = crate::ghd::ghd_count(&s.btm, &factors, nvars, &var_order);
            let fact_us = t.elapsed().as_micros().max(1);

            assert_eq!(fc, ec, "factorized count must equal enumerate count");
            eprintln!(
                "k={k:4} output={ec:9}  enumerate {enum_us:8}us  factorized {fact_us:6}us  speedup {:.1}x",
                enum_us as f64 / fact_us as f64
            );
        }
    }

    /// The flybase query shape (main.rs `bench_flybase` P1): a star join
    /// `(gene_name_of TP g $x)(SPO $x includes $y)(SPO $x transcribed_from $z)` whose COUNT the
    /// CountSink computes today by enumerating the O(k^2) product into a PathMap. `$y` and `$z` are
    /// independent given `$x`, so `ghd_aggregate_auto` counts it in O(k) via Sum_x deg_y(x)*deg_z(x).
    #[test]
    #[ignore = "timing: the flybase star-join COUNT win vs the enumerate CountSink"]
    fn ghd_count_flybase_star_shape() {
        for k in [50usize, 100, 200, 400, 800] {
            let mut s = crate::space::Space::new();
            let mut prog = String::from("(gene_name_of TP g x)\n");
            for y in 0..k {
                prog.push_str(&format!("(SPO x includes y{y})\n"));
            }
            for z in 0..k {
                prog.push_str(&format!("(SPO x transcribed_from z{z})\n"));
            }
            s.add_all_sexpr(prog.as_bytes()).unwrap();
            let body =
                enc("(, (gene_name_of TP g $x) (SPO $x includes $y) (SPO $x transcribed_from $z))");
            let (factors, nvars) = parse_body_factors(&body).unwrap();
            let order: Vec<usize> = (0..nvars).collect();

            // enumerate the join (what the CountSink dedups today)
            let t = std::time::Instant::now();
            let mut ec = 0u64;
            run_unify_join_stream(&s.btm, &factors, &order, nvars, &mut |_t| {
                ec += 1;
                true
            });
            let enum_us = t.elapsed().as_micros().max(1);

            // factorized count via the auto-derived elimination order
            let t = std::time::Instant::now();
            let fc = crate::ghd::ghd_aggregate_auto::<u64>(&s.btm, &factors, nvars, |_| 1)
                .expect("the star decomposes");
            let fact_us = t.elapsed().as_micros().max(1);

            assert_eq!(fc, ec, "factorized star count must equal the enumerated count");
            eprintln!(
                "k={k:4} output={ec:9}  enumerate {enum_us:8}us  factorized {fact_us:6}us  speedup {:.1}x",
                enum_us as f64 / fact_us as f64
            );
        }
    }

    /// An inverted factor is re-indexed with permuted, renumbered columns; a streamed leaf must
    /// hand back the fact's original stored bytes, coreference included: `(f $u $u)` must come
    /// back as NewVar then VarRef, not two fresh variables.
    #[test]
    fn streamed_tuples_reconstruct_reindexed_facts() {
        let mut s = crate::space::Space::new();
        s.add_all_sexpr("(e a a)\n(e b a)\n(f $u $u)\n(f a b)\n".as_bytes())
            .unwrap();
        let body = enc("(, (e $x $y) (f $y $x))");
        let (factors, nvars) = parse_body_factors(&body).unwrap();
        let var_order: Vec<usize> = (0..nvars).collect();
        {
            let mut var_pos = vec![0usize; nvars];
            for (pos, &v) in var_order.iter().enumerate() {
                var_pos[v] = pos;
            }
            assert!(
                is_inverted(&factors[1], &var_pos),
                "test premise: (f $y $x) is inverted under (x, y) order"
            );
        }
        let mut tuples: Vec<Vec<Vec<u8>>> = Vec::new();
        let mut cb = |t: &[Vec<u8>]| {
            tuples.push(t.to_vec());
            true
        };
        run_unify_join_stream(&s.btm, &factors, &var_order, nvars, &mut cb);
        tuples.sort();
        assert_eq!(
            tuples,
            vec![
                vec![enc("(e a a)"), enc("(f $u $u)")],
                vec![enc("(e b a)"), enc("(f a b)")],
            ],
            "leaves must reconstruct the original stored facts"
        );
    }

    /// The dispatched transform must agree with the stock transform on the match count `touched`
    /// and the changed flag, not only on the final bytes: the join streams one callback per
    /// product tuple, so the multiplicities match, including the cyclic assignment the emit-side
    /// check skips after `unify` accepted it.
    #[cfg(feature = "specialize_io")]
    #[test]
    fn dispatch_touched_parity_on_transform() {
        let cases: &[(&str, &str, &str)] = &[
            (
                "(e a b)\n(e a c)\n(e b c)\n(e b d)\n",
                "(, (e $x $y) (e $y $z) (e $x $z))",
                "(, (outt $x $y $z))",
            ),
            (
                "(r $d b)\n(r a b)\n",
                "(, (r (a $p) b) (r (b) $p))",
                "(, (outt $p))",
            ),
            (
                "(e (k $s2) v0)\n(e $s1 $s1)\n(h $s0 $s0)\n(h junk junk)\n",
                "(, (e (k $x0) $x1) (e (k $x1) $x2) (h $x2 $x0))",
                "(, (outt $x0 $x1 $x2))",
            ),
            (
                "(p a)\n(p b)\n(q a)\n(q $w)\n",
                "(, (p $x) (q $x))",
                "(, (outt $x))",
            ),
        ];
        for (facts, body, tpl) in cases {
            // One exec atom encoded whole, then destructured in place, so the template's VarRefs
            // stay relative to the pattern's variables exactly as the engine sees them.
            let atom = enc(&format!("(exec 0 {body} {tpl})"));
            let head_len = 1 + expr_span_len(expr_from_bytes(&atom[1..]));
            let loc_len = expr_span_len(expr_from_bytes(&atom[head_len..]));
            let pat_off = head_len + loc_len;
            let pat_len = expr_span_len(expr_from_bytes(&atom[pat_off..]));
            let tpl_off = pat_off + pat_len;
            let mut run = |on: bool| {
                let mut s = crate::space::Space::new();
                s.add_all_sexpr(facts.as_bytes()).unwrap();
                let bytes = atom.clone();
                set_leapfrog_dispatch(on);
                let res = s.transform_multi_multi_(
                    expr_from_bytes(&bytes[pat_off..]),
                    expr_from_bytes(&bytes[tpl_off..]),
                    expr_from_bytes(&bytes[..]),
                );
                set_leapfrog_dispatch(true);
                (res, space_paths(&s))
            };
            let (r0, s0) = run(false);
            let (r1, s1) = run(true);
            assert_eq!(r0, r1, "(touched, any_new) differ on {body}");
            assert_eq!(s0, s1, "spaces differ on {body}");
        }
    }
}
