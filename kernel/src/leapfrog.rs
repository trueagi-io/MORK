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

use mork_expr::{byte_item, item_byte, unify, unify_into, Expr, ExprEnv, ExprZipper, Tag};
use pathmap::utils::{BitMask, ByteMask};
use pathmap::zipper::{
    ReadZipperUntracked, Zipper, ZipperAbsolutePath, ZipperIteration, ZipperMoving, ZipperValues,
};
use pathmap::PathMap;
use std::collections::{BTreeMap, BTreeSet};
use std::marker::PhantomData;
use std::panic::{catch_unwind, AssertUnwindSafe};

const QUERY_NS: u8 = 0;

/// Marks a parse record whose byte may have a sibling in the trie, i.e. a position no bulk move
/// covered. A symbol payload is at most 63 bytes, so the record's payload field has a spare bit.
const BRANCH_CANDIDATE: u8 = 0x80;

/// Every byte value, so that `single_byte` can hand out a `'static` one-byte slice.
static BYTE_VALUES: [u8; 256] = {
    let mut t = [0u8; 256];
    let mut i = 0;
    while i < 256 {
        t[i] = i as u8;
        i += 1;
    }
    t
};

/// The one-byte term `b` as a slice with `'static` lifetime. A stored wildcard is a complete
/// one-byte subterm, and the env built over it outlives the expression that produced it, so the
/// bytes cannot be a caller's temporary.
#[inline]
fn single_byte(b: u8) -> &'static [u8] {
    &BYTE_VALUES[b as usize..b as usize + 1]
}

/// The least byte present in `mask` that is `>= k`, or `None` if every set bit is below `k`. This
/// is the per-byte leapfrog seek on a trie node's children.
#[inline]
pub fn least_ge(mask: &ByteMask, k: u8) -> Option<u8> {
    if mask.test_bit(k) {
        Some(k)
    } else {
        // next_bit is strictly above its argument, so k itself needs the separate test above.
        mask.next_bit(k)
    }
}

/// Whether `bytes` (from the column-start focus) spell exactly one complete subterm, by replaying
/// the parse from scratch. [`SubtermCursor`] tracks this incrementally instead — replaying it per
/// descent step made completing an L-byte subterm O(L^2), which dominated the join on MORK's real
/// (hundreds-of-bytes) symbolic terms. Kept as the reference the cursor's incremental state is
/// cross-checked against under `debug_assertions`, and for out-of-cursor callers.
#[cfg_attr(not(debug_assertions), allow(dead_code))]
#[inline]
fn is_complete(bytes: &[u8]) -> bool {
    let (mut subterms, mut payload) = (1u32, 0u32);
    for &b in bytes {
        mork_expr::subterm_parse_step(b, &mut subterms, &mut payload);
    }
    subterms == 0 && payload == 0
}

/// A cursor over the complete variable-width subterms branching from a PathMap zipper's focus, in
/// ascending lexicographic order, with a leapfrog `seek`. This is the zipper-native replacement for
/// a materialized per-variable domain: it seeks on the live byte-trie instead of scanning a `Vec`.
///
/// The cursor is a non-empty stack of [`Column`]s over one held zipper: `col` is the column being
/// enumerated and `floor_stack` the columns already consumed below it. The current subterm is
/// `z.path()[col.floor..]` -- the zipper's own path IS the key -- and the walk never ascends above
/// that floor, so the zipper is left at the floor between re-seeks and at the subterm boundary
/// while positioned.
pub struct SubtermCursor<Z> {
    z: Z,
    col: Column,
    /// Exhaustion, read as a field: the leapfrog's candidate loop tests it while `seek` takes
    /// OTHER cursors mutably, which a `key().is_some()` borrow would forbid.
    pub at_end: bool,
    /// The columns already descended past, below the zipper's creation focus. `descend_floor`
    /// locks the current subterm as a column value and lowers the floor into it (so the next
    /// enumeration is of the following column); `ascend_floor` restores it. This lets one cursor
    /// walk a factor's successive columns with the zipper HELD -- descended and ascended in
    /// place, never re-opened from the trie root (which is the join's dominant cost).
    floor_stack: Vec<Column>,
}

/// One column of the enumeration: where its key starts, plus the incremental parse of that key.
/// A column parked by `descend_floor` restores under `ascend_floor` exactly (including the
/// per-byte record the subsequent `next` retreats through) without replaying the parse. The key
/// bytes themselves are never saved: they are still on the zipper's path.
struct Column {
    /// Absolute length of `z.path()` at this column's start. The subterm under enumeration is
    /// `z.path()[floor..]`: the zipper's own path IS the key, and the cursor keeps no copy of it
    /// -- one integer replaces the byte-for-byte mirror this used to maintain (and the join's
    /// `bound[f]` mirror above it, which was provably always equal to `z.path()[..floor]` by the
    /// old drift assertions).
    floor: usize,
    /// Running incremental parse of the key: how many complete subterms and how many raw
    /// symbol-payload bytes it still owes, i.e. the fold of [`subterm_parse_step`] over
    /// `z.path()[floor..]` starting from `(1, 0)`. The key spells exactly one complete subterm
    /// iff both are zero, so the boundary test is O(1) instead of an O(len) replay per descent
    /// step. An expression is at most `u32::MAX - 1` bytes, which bounds the owed subterms; owed
    /// payload is one symbol's, <= 63.
    owed_subterms: u32,
    owed_payload: u32,
    /// The `(owed_subterms, owed_payload)` that stood BEFORE each key byte was consumed. SOME
    /// record is irreducible: popping byte `b` with payload `P` owed cannot tell "b is
    /// `SymbolSize(P)`" from "b is a payload byte and `P+1` was owed" -- both are legal for the
    /// same bytes -- so the reverse is not derivable from content alone. The pre-payload alone
    /// (one byte) would suffice logically, with the subterm count inverted arithmetically from
    /// the byte, but the measured cost of that reversal's branches exceeds the branchless
    /// two-field restore, so the record keeps both fields at their natural widths.
    parse_stack: Vec<(u32, u8)>,
    /// NewVar and total variable tags in the key, maintained by the same per-byte advance and
    /// retreat that drive the incremental parse -- the parse already distinguishes tag positions
    /// from symbol payload, so the counts are EXACT, and they make the candidate's groundness and
    /// its variable-introduction delta free byproducts of the enumeration walk instead of a
    /// rescan. At most 64 variables exist per expression, so a byte each.
    key_newvars: u8,
    key_vars: u8,
}

impl Column {
    fn new(floor: usize) -> Self {
        Column {
            floor,
            owed_subterms: 1,
            owed_payload: 0,
            parse_stack: Vec::new(),
            key_newvars: 0,
            key_vars: 0,
        }
    }

    /// Whether the key is empty, i.e. nothing has been parsed since the floor. The state the
    /// column is parked in between enumerations, which the raw descend/ascend pair relies on.
    #[cfg_attr(not(debug_assertions), allow(dead_code))]
    fn is_at_floor(&self) -> bool {
        self.parse_stack.is_empty() && self.owed_subterms == 1 && self.owed_payload == 0
    }

    /// Back to an empty key at `floor`, keeping the parse stack's allocation.
    fn reset_with_floor(&mut self, floor: usize) {
        self.floor = floor;
        self.owed_subterms = 1;
        self.owed_payload = 0;
        self.key_newvars = 0;
        self.key_vars = 0;
        self.parse_stack.clear();
    }
}

impl<Z: Zipper + ZipperMoving + ZipperIteration> SubtermCursor<Z> {
    /// Build a cursor at the zipper's current focus. Not positioned until `first`/`seek` is called.
    pub fn new(z: Z) -> Self {
        let floor = z.path().len();
        SubtermCursor {
            z,
            col: Column::new(floor),
            at_end: true,
            floor_stack: Vec::new(),
        }
    }

    #[inline]
    fn key_len(&self) -> usize {
        self.z.path().len() - self.col.floor
    }

    /// `(NewVar count, total variable count)` of the current key, exact.
    #[inline]
    fn key_var_counts(&self) -> (u8, u8) {
        (self.col.key_newvars, self.col.key_vars)
    }

    /// Everything consumed below the zipper's creation focus and above the current column: the
    /// factor's bound column values, concatenated. What the join's `bound[f]` used to mirror.
    #[inline]
    fn consumed_bytes(&self) -> &[u8] {
        &self.z.path()[..self.col.floor]
    }

    /// Whether the key currently spells exactly one complete subterm, read off the incremental
    /// state. Cross-checked against the from-scratch replay under `debug_assertions` so the
    /// property tests catch any divergence.
    #[inline]
    fn key_is_complete(&self) -> bool {
        let complete = self.col.owed_subterms == 0 && self.col.owed_payload == 0;
        debug_assert_eq!(
            self.col.parse_stack.len(),
            self.key_len(),
            "parse stack out of lockstep with key"
        );
        debug_assert_eq!(
            complete,
            is_complete(&self.z.path()[self.col.floor..]),
            "incremental subterm-parse state diverged from the replay"
        );
        complete
    }

    /// Account for one byte the zipper just descended, advancing the incremental parse.
    #[inline]
    fn advance_parse(&mut self, b: u8) {
        self.advance_parse_at(b, true)
    }

    /// [`Self::advance_parse`], recording whether a sibling byte may exist at this position. A bulk
    /// move only crosses positions with a single child, so the bytes it produces are marked `false`
    /// and the ascending backtrack skips them without asking the zipper.
    #[inline]
    fn advance_parse_at(&mut self, b: u8, branch: bool) {
        let flag = if branch { BRANCH_CANDIDATE } else { 0 };
        self.col
            .parse_stack
            .push((self.col.owed_subterms, self.col.owed_payload as u8 | flag));
        // A byte is a tag exactly when no symbol payload is owed; the parse state answers that
        // BEFORE consuming the byte, which is what makes the variable counts exact.
        if self.col.owed_payload == 0 {
            match byte_item(b) {
                Tag::NewVar => { self.col.key_newvars += 1; self.col.key_vars += 1; }
                Tag::VarRef(_) => { self.col.key_vars += 1; }
                _ => {}
            }
        }
        mork_expr::subterm_parse_step(b, &mut self.col.owed_subterms, &mut self.col.owed_payload);
    }

    /// Account for the key's last byte `b` leaving (the caller moves the zipper), restoring the
    /// parse state that preceded it.
    #[inline]
    fn retreat_parse(&mut self, b: u8) {
        let (pre_subterms, pre_payload) = self
            .col
            .parse_stack
            .pop()
            .expect("parse stack out of lockstep with key");
        let pre_payload = pre_payload & !BRANCH_CANDIDATE;
        self.col.owed_subterms = pre_subterms;
        // The restored state classifies `b`: a tag position mirrors its variable count back out.
        if pre_payload == 0 {
            match byte_item(b) {
                Tag::NewVar => { self.col.key_newvars -= 1; self.col.key_vars -= 1; }
                Tag::VarRef(_) => { self.col.key_vars -= 1; }
                _ => {}
            }
        }
        self.col.owed_payload = pre_payload as u32;
    }

    /// Ascend back to the floor (column start), clearing the key.
    fn reset_to_floor(&mut self) {
        let n = self.key_len();
        if n > 0 {
            let ok = self.z.ascend(n);
            debug_assert!(ok, "the floor is above the zipper's root by construction");
        }
        self.col.reset_with_floor(self.col.floor);
        self.at_end = false;
    }

    /// Lock the current complete subterm as a consumed column value: the floor descends into it
    /// so subsequent enumeration is of the NEXT column. The zipper stays put (it is already
    /// descended into the key); only the floor bookkeeping moves. Pairs with `ascend_floor`.
    pub fn descend_floor(&mut self) {
        let next = Column::new(self.z.path().len());
        self.floor_stack.push(std::mem::replace(&mut self.col, next));
        self.at_end = false;
    }

    /// Undo the most recent `descend_floor`: the floor rises back to this column and the cursor
    /// is repositioned at the value it held (still on the zipper's path), ready to advance via
    /// `next`. Requires the zipper to be back at this column's floor plus that value, which
    /// holds because a fully-exhausted deeper column leaves its cursor at its own floor
    /// (== this value's end).
    pub fn ascend_floor(&mut self) {
        self.col = self
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

    /// Descend the zipper by raw `bytes` — NOT necessarily a complete subterm (the unification
    /// join pushes a lone arity byte when it walks into a compound column) — lowering the floor
    /// past them. This holds the zipper across the join instead of re-opening it from the trie
    /// root per probe. Requires the cursor to be at its floor (empty key); pairs with `ascend_raw`.
    fn descend_raw(&mut self, bytes: &[u8]) {
        debug_assert!(
            self.key_len() == 0,
            "descend_raw must start at the column floor"
        );
        // The raw fragment is NOT part of the key (it lowers the floor past itself), so the
        // incremental parse state is untouched: an empty key still owes exactly one subterm,
        // now measured from the new, deeper floor.
        debug_assert!(self.col.is_at_floor());
        self.z.descend_to(bytes);
        self.col.floor += bytes.len();
        self.at_end = false;
    }

    /// Undo the most recent `descend_raw` of `n` bytes: raise the floor back past them. Requires
    /// the cursor to be back at its (lowered) floor, which holds because every enumeration and
    /// deeper descend/ascend pair restores it.
    fn ascend_raw(&mut self, n: usize) {
        debug_assert!(
            self.key_len() == 0,
            "ascend_raw must start at the column floor"
        );
        debug_assert!(self.col.is_at_floor());
        self.z.ascend(n);
        self.col.floor -= n;
        self.at_end = false;
    }

    /// The trie children at the floor (the current column start). Requires the cursor to be at
    /// its floor.
    fn floor_child_mask(&self) -> ByteMask {
        debug_assert!(
            self.key_len() == 0,
            "floor_child_mask read off-floor"
        );
        self.z.child_mask()
    }

    /// Descend the least child at each step until the key forms a complete subterm. Returns false
    /// if a node runs out of children before completion (malformed/empty branch).
    fn complete_leftmost(&mut self) -> bool {
        while !self.key_is_complete() {
            // A symbol's payload is a run whose length the parse already knows, and no decision is
            // taken inside it, so take all of it in ONE zipper move. `descend_first_k_path` walks
            // the trie a node at a time (it extends the path by a whole node key), where the
            // per-byte descent below pays a node lookup, a regularize and a key memcmp for every
            // byte. The records the run owes are the arithmetic sequence the parse would have
            // produced, and payload bytes are not tags, so no variable count moves.
            let owed = self.col.owed_payload as usize;
            if owed > 1 {
                let before = self.z.path().len();
                if !self.z.descend_first_k_path(owed) {
                    self.at_end = true;
                    return false;
                }
                debug_assert_eq!(self.z.path().len(), before + owed);
                for i in 0..owed {
                    self.col
                        .parse_stack
                        .push((self.col.owed_subterms, (owed - i) as u8 | BRANCH_CANDIDATE));
                }
                self.col.owed_payload = 0;
                continue;
            }
            // The trie is path-compressed, so a span with no branching IS one node key: take the
            // whole span in one move and run the (allocation-free) byte parse over what it
            // produced, ascending back if it ran past the subterm boundary. `descend_until` would
            // be wrong to use here -- its ReadZipper override is a per-byte loop, while
            // `descend_until_max_bytes` extends by whole node keys.
            let before = self.z.path().len();
            if self.z.descend_until_max_bytes(64) {
                let end = self.z.path().len();
                let mut i = before;
                while i < end {
                    let b = self.z.path()[i];
                    self.advance_parse_at(b, false);
                    i += 1;
                    if self.col.owed_subterms == 0 && self.col.owed_payload == 0 {
                        break;
                    }
                }
                if i < end {
                    let ok = self.z.ascend(end - i);
                    debug_assert!(ok, "ascending back inside a span we just descended");
                }
                continue;
            }
            // The leftmost child, straight off the node's iterator: materializing a full
            // 256-bit child mask and scanning it for the least bit, then re-finding that byte
            // with descend_to_byte, re-derived per byte what the zipper answers in one step.
            if !self.z.descend_first_byte() {
                self.at_end = true;
                return false;
            }
            let b = *self.z.path().last().expect("descend_first_byte grew the path");
            self.advance_parse(b);
        }
        true
    }

    /// From the current complete subterm, move to the least subterm strictly greater: ascend until a
    /// level offers a larger sibling, take the least such, then complete leftmost. False = exhausted.
    fn backtrack_then_leftmost(&mut self) -> bool {
        loop {
            // Ascend straight to the deepest position a bulk move did not cover. Everything below
            // it has a single child by construction, so no sibling can exist there and the probe
            // this used to make at every depth could only fail. The scan walks the records the
            // retreat has to walk anyway, so it costs no zipper call and no extra state.
            let mut n = self.col.parse_stack.len();
            while n > 0 && self.col.parse_stack[n - 1].1 & BRANCH_CANDIDATE == 0 {
                n -= 1;
            }
            if n == 0 {
                self.at_end = true;
                return false;
            }
            let cur = self.z.path().len();
            let target = self.col.floor + n;
            debug_assert!(target <= cur, "the record stack ran below the focus");
            if cur > target {
                for i in (target..cur).rev() {
                    let b = self.z.path()[i];
                    self.retreat_parse(b);
                }
                let ok = self.z.ascend(cur - target);
                debug_assert!(ok, "ascending inside the column");
            }
            // The byte about to leave must be read BEFORE the zipper moves: with the path as the
            // only representation, it lives nowhere else.
            let old = *self.z.path().last().expect("above the floor");
            // In-place sibling switch on the node's iterator, replacing the ascend + full child
            // mask + next-bit scan + descend round trip. The parse mirrors it: undo the byte the
            // switch replaced, consume the byte it produced. (A nondeterministic mork-test
            // failure was at first attributed to this switch; bisection showed the failure is a
            // pre-existing upstream flake in the anti-unify sink on the ProductZipper path, and a
            // 4000-seed property harness against PathMap vindicated to_next_sibling_byte.)
            if self.z.to_next_sibling_byte() {
                let b = *self.z.path().last().expect("sibling switch kept the depth");
                self.retreat_parse(old);
                self.advance_parse(b);
                return self.complete_leftmost();
            }
            self.retreat_parse(old);
            self.z.ascend_byte();
        }
    }

    /// Position at the least subterm.
    pub fn first(&mut self) {
        self.reset_to_floor();
        self.complete_leftmost();
    }

    /// Advance to the next subterm.
    pub fn next(&mut self) {
        if self.at_end {
            return;
        }
        self.backtrack_then_leftmost();
    }

    /// The current subterm bytes, or `None` when exhausted: the enumeration's read API, a view
    /// of the zipper's own path.
    pub fn key(&self) -> Option<&[u8]> {
        if self.at_end {
            None
        } else {
            Some(&self.z.path()[self.col.floor..])
        }
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
            if self.key_is_complete() {
                self.at_end = false;
                return;
            }
            let mask = self.z.child_mask();
            if ti < target.len() {
                let t = target[ti];
                if mask.test_bit(t) {
                    self.z.descend_to_byte(t);
                    self.advance_parse(t);
                    ti += 1;
                    continue;
                }
                match mask.next_bit(t) {
                    Some(b) => {
                        self.z.descend_to_byte(b);
                        self.advance_parse(b);
                        self.complete_leftmost();
                        return;
                    }
                    None => {
                        self.backtrack_then_leftmost();
                        return;
                    }
                }
            } else {
                self.complete_leftmost();
                return;
            }
        }
    }
}


use mork_expr::{Bindings, ExprVar, NEW_VAR_EXPR_BYTES};

/// A materialized encoded term plus the query-variable intro count before it in the original body.
/// The bytes stay in MORK's native encoding; unification and substitution operate through
/// [`ExprEnv`] views over them.
#[derive(Clone, Debug)]
pub struct EncodedTerm<'a> {
    /// The column's subterm, pointing straight into the body being evaluated (which outlives the
    /// join, witnessed by the lifetime). The encoding is trusted: every consumer walks it by
    /// structure, so no length rides along.
    pub expr: Expr,
    pub intro: u8,
    /// Bitmask of the query variables this term mentions, filled in by the single parse scan so
    /// groundness and variable-position queries need no further traversal. The parser caps an
    /// expression at 63 variables (a body that exceeds it is not routable), so the mask is total.
    vars: u64,
    _borrow: PhantomData<&'a [u8]>,
}

impl<'a> EncodedTerm<'a> {
    fn is_ground(&self) -> bool {
        self.vars == 0
    }

    fn min_var_pos(&self, var_pos: &[usize]) -> Option<usize> {
        let mut best: Option<usize> = None;
        let mut m = self.vars;
        while m != 0 {
            let v = m.trailing_zeros() as usize;
            m &= m - 1;
            let pos = var_pos[v];
            best = Some(best.map_or(pos, |b: usize| b.min(pos)));
        }
        best
    }
}

/// One query argument column in a factor. Top-level variables are exposed so the leapfrog order can
/// seek them directly; every structured or ground column stays as native encoded bytes.
#[derive(Clone, Debug)]
pub enum FactorColumn<'a> {
    Var(usize),
    Term(EncodedTerm<'a>),
}

impl<'a> FactorColumn<'a> {
    fn min_var_pos(&self, var_pos: &[usize]) -> Option<usize> {
        match self {
            FactorColumn::Var(v) => Some(var_pos[*v]),
            FactorColumn::Term(term) => term.min_var_pos(var_pos),
        }
    }

}

/// One seek position in the pre-order walk of a factor's query columns -- the unit the join
/// schedules and consumes, generalizing "a top-level argument column" to "any position at any
/// depth".
///
/// Flattening is what lets a variable nested inside a namespace wrapper, say `$x` in
/// `(data (e $x $y))`, be scheduled and intersected across factors instead of being enumerated by
/// the structural descent inside one factor (which is the ProductZipper's nested-loop algorithm).
///
/// The ground structure around a variable is NOT absorbed into the cursor's seek prefix. Each
/// `Sym`/`Compound` position stays its own step precisely so the descent can take the stored
/// WILDCARD branch there: a fact `(data $w)` whose `$w` captures the whole `(e a b)` must still
/// unify, and only a per-position mask read can find it. Taking that branch consumes the position's
/// whole subtree, which is what `Compound::end` records.
#[derive(Clone, Copy, Debug)]
enum Step<'a> {
    /// Query variable `v` occupies this position: the schedulable slot.
    Var(usize),
    /// A ground symbol leaf. The env is the position in the column, exactly what the recursive
    /// descent used to derive with `ExprEnv::args` (a stored wildcard here unifies against the
    /// same pattern it always did); the symbol's byte length reads off its tag in O(1).
    Sym(ExprEnv, PhantomData<&'a [u8]>),
    /// A compound node; its children are the steps `s+1 .. end`. Arity reads off the tag byte.
    Compound { env: ExprEnv, end: usize, _borrow: PhantomData<&'a [u8]> },
}

/// Flatten one column's encoded subterm at `base[offset..]` into steps, returning the offset and
/// introduced-variable count just past it. `None` on a truncated term or a variable overflow, which
/// the caller turns into "not routable".
fn push_steps<'a>(
    base: Expr,
    mut offset: usize,
    mut intro: u8,
    out: &mut Vec<Step<'a>>,
) -> (usize, u8) {
    // The body is engine-produced and already validated by the factor parse; the encoding is
    // trusted, so this walk reads it raw.
    let b = unsafe { *base.ptr.add(offset) };
    let env = ExprEnv::with_intro(QUERY_NS, intro, base).offset(offset as u32);
    match byte_item(b) {
        Tag::NewVar => {
            out.push(Step::Var(intro as usize));
            (offset + 1, intro + 1)
        }
        Tag::VarRef(id) => {
            out.push(Step::Var(id as usize));
            (offset + 1, intro)
        }
        Tag::SymbolSize(size) => {
            out.push(Step::Sym(env, PhantomData));
            (offset + 1 + size as usize, intro)
        }
        Tag::Arity(arity) => {
            let at = out.len();
            out.push(Step::Compound {
                env,
                end: 0,
                _borrow: PhantomData,
            });
            offset += 1;
            for _ in 0..arity {
                let (next_offset, next_intro) = push_steps(base, offset, intro, out);
                offset = next_offset;
                intro = next_intro;
            }
            let end = out.len();
            match &mut out[at] {
                Step::Compound { end: slot, .. } => *slot = end,
                _ => unreachable!("the pushed step is the compound just written"),
            }
            (offset, intro)
        }
    }
}

/// The factor's columns flattened into one ordered step list. A top-level `Var` column is one slot,
/// exactly as before; a `Term` column expands into its own pre-order walk.
fn factor_steps<'a>(factor: &Factor<'a>) -> Vec<Step<'a>> {
    let mut out = Vec::with_capacity(factor.cols.len());
    for col in &factor.cols {
        match col {
            FactorColumn::Var(v) => out.push(Step::Var(*v)),
            FactorColumn::Term(term) => {
                push_steps(term.expr, 0, term.intro, &mut out);
            }
        }
    }
    out
}

/// A query factor: its seek prefix in the PathMap, and every column in syntactic order. For a
/// compound conjunct the body parser emits the arity byte alone as the prefix, with the relation
/// head as column 0 (a direct construction may bake a ground head into the prefix instead, at the
/// cost of never matching a wildcard stored head). For a conjunct that is not a compound the
/// prefix is EMPTY and the conjunct itself is the single column, so the cursor opens at the trie
/// root where whole facts live. Ground columns stay columns so they can unify with stored data
/// variables at their trie position.
#[derive(Clone, Debug)]
pub struct Factor<'a> {
    /// The relation's seek prefix: TRIE PATH bytes, not an expression, which is why this stays a
    /// slice while the columns hold `Expr`s. The body parser emits the conjunct's arity byte
    /// alone (empty for a whole-atom factor, whose cursor opens at the trie root, and for a
    /// re-indexed factor, whose columns were permuted into a private map); a direct construction
    /// may bake a ground head into the prefix instead, at the cost of never matching a wildcard
    /// stored head.
    pub prefix: &'a [u8],
    pub cols: Vec<FactorColumn<'a>>,
}








// ---- unification layer: schematic data (stored variables in facts act as wildcards) ----

#[inline]
fn is_wildcard_term(k: u8) -> bool {
    matches!(byte_item(k), Tag::NewVar | Tag::VarRef(_))
}

/// Whether a subterm's head byte makes it symbol-headed, hence ground and a leaf of the encoding.
/// Symbol tags sort above every compound and variable tag, so a column's ascending enumeration ends
/// in a contiguous run of ground symbols -- which is the run an exact-match intersection may prune,
/// since over ground terms unifiability is byte equality.
#[inline]
fn is_symbol_head(head: u8) -> bool {
    matches!(byte_item(head), Tag::SymbolSize(_))
}

/// Whether a position whose trie children are `mask` stores a wildcard, i.e. a variable that
/// unifies with whatever the query has here -- a complete one-byte subterm, so exactly a variable
/// tag among the children. A position that has one must never restrict an intersection; one that
/// has none can only match by equality. Reserved bytes answer "has a wildcard", the conservative
/// side.
#[inline]
fn mask_has_wildcard(mask: &ByteMask) -> bool {
    matches!(
        least_ge(mask, item_byte(Tag::VarRef(0))),
        Some(b) if b <= item_byte(Tag::NewVar)
    )
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
        let len = unsafe { Expr::from_slice(&bytes[i..]).span().as_ref().unwrap().len() };
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
        let mut ez = ExprZipper::new(Expr::from_slice(col));
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
    let mut renum: HashMap<usize, usize> = HashMap::with_capacity(new_order.len());
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

/// The regions of the source map a factor's re-index has to walk, or `None` when no sound scoping
/// exists and the whole same-arity prefix must be read.
///
/// A parsed factor's `prefix` is the ARITY BYTE ALONE (the relation head is kept as column 0 on
/// purpose, so a stored WILDCARD head still unifies under a ground query head), so "the factor's
/// region" is otherwise every same-arity fact in the space — unrelated relations included.
///
/// Scoping is sound exactly when the head column is a ground SYMBOL. At that trie position a
/// stored subterm is a symbol, a compound, or a top-level wildcard, and a ground symbol query
/// column unifies only with the identical symbol bytes or with a wildcard (see
/// [`UnifyJoin::match_expr_at_current`]'s `Tag::SymbolSize` arm: an exact `ground_probe` hit plus
/// the wildcard bytes of the child mask). So the union of `prefix + head bytes` and
/// `prefix + w` for every wildcard byte `w` present at that position holds every fact the factor
/// can ever match, and nothing outside it is reachable. Re-emitting preserves each column's shape
/// (a stored variable stays a variable, a symbol stays the same symbol), so no excluded fact could
/// re-enter through the re-indexed key either.
///
/// A ground COMPOUND head is deliberately NOT scoped: a stored compound head may carry variables
/// inside it (`(g $x)` unifies with `(g a)`) and would live outside `prefix + head bytes`. A
/// variable or compound head column is not scoped either.
///
/// Related to [`factor_scan_path`], which the dispatch gate uses for approximate counts and
/// samples; that one accepts any ground head and does not take the wildcard union, so it is not
/// sound for this purpose and is left alone.
fn reindex_regions(map: &PathMap<()>, factor: &Factor) -> Option<Vec<Vec<u8>>> {
    let FactorColumn::Term(head) = factor.cols.first()? else {
        return None;
    };
    let head_tag = unsafe { byte_item(*head.expr.ptr) };
    let Tag::SymbolSize(hsize) = head_tag else {
        return None;
    };
    // The head column IS the symbol: tag byte plus payload, read off the trusted encoding.
    let head_bytes = unsafe { core::slice::from_raw_parts(head.expr.ptr, 1 + hsize as usize) };
    let mut regions = Vec::new();
    let mut ground = factor.prefix.to_vec();
    ground.extend_from_slice(head_bytes);
    regions.push(ground);
    let mask = map.read_zipper_at_path(factor.prefix).child_mask();
    for w in mask.iter() {
        if is_wildcard_term(w) {
            let mut wild = factor.prefix.to_vec();
            wild.push(w);
            regions.push(wild);
        }
    }
    Some(regions)
}

/// Fold every fact under `region` into `reindex`, permuted by `new_order`. `plen` is the factor's
/// prefix length, so the column bytes start at `plen` of the absolute path regardless of how deep
/// `region` reaches.
fn fold_region_into_reindex(
    map: &PathMap<()>,
    region: &[u8],
    plen: usize,
    ncols: usize,
    new_order: &[usize],
    reindex: &mut PathMap<()>,
) {
    let mut insert = |col_bytes: &[u8]| {
        let cols = split_columns(col_bytes, ncols);
        let items = columns_to_items(&cols);
        reindex.insert(&emit_reordered(&items, new_order), ());
    };
    let mut rz = map.read_zipper_at_path(region);
    // `to_next_val` starts strictly below the zipper's root, so a fact stored exactly AT the region
    // root needs folding explicitly. Only a single-column factor can reach that, and a
    // single-column factor is never inverted, but the walk stays total either way.
    if rz.val().is_some() {
        insert(&region[plen..]);
    }
    while rz.to_next_val() {
        let full = rz.origin_path();
        insert(&full[plen..]);
    }
}

/// Re-index an inverted factor: copy its facts into a fresh PathMap with the columns permuted into
/// `var_order` position order (variables renumbered to stay canonical). Returns that map, the new
/// column-variable list, now non-decreasing, so the join seeks it like any compatible factor, and
/// the permutation itself (`new_order[j]` = original column at re-indexed position `j`) so a leaf
/// can reconstruct the stored fact's original bytes. This is the one partial materialization the
/// cyclic case needs, and only the inverted factor pays it; re-keying into another attribute order
/// is the standard worst-case-optimal answer to a cycle.
///
/// The walk is scoped to the factor's OWN relation whenever [`reindex_regions`] can prove that
/// sound, instead of re-materializing every same-arity fact in the space.
fn build_reindex<'a>(
    map: &PathMap<()>,
    factor: &Factor<'a>,
    var_pos: &[usize],
) -> (PathMap<()>, Vec<FactorColumn<'a>>, Vec<usize>) {
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
    let regions = reindex_regions(map, factor).unwrap_or_else(|| vec![factor.prefix.to_vec()]);
    for region in &regions {
        fold_region_into_reindex(map, region, plen, ncols, &new_order, &mut reindex);
    }
    (reindex, new_cols, new_order)
}

/// Worst-case-optimal leapfrog-UNIFICATION join directly on the PathMap byte-trie, returning the
/// fully-ground answer rows (`row[v]` = global variable `v`'s value). A row with any still-free query
/// variable is dropped here; the live route uses [`unify_join_zipper_partial`] instead, to keep it
/// and bind only its ground components, exactly as the materialized route does.
/// TEST tooling over the streaming join.
#[cfg(test)]
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
                .map(|component| component.filter(|bytes| Expr::from_slice(bytes).variables() == 0))
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
/// TEST tooling over the streaming join.
#[cfg(test)]
pub fn unify_join_zipper_partial(
    map: &PathMap<()>,
    factors: &[Factor],
    var_order: &[usize],
    nvars: usize,
) -> BTreeSet<Vec<Option<Vec<u8>>>> {
    run_unify_join(map, factors, var_order, nvars, false).0
}

/// As [`unify_join_zipper_partial`], but returns each answer as one variable-coordinated tuple
/// encoding (query variables `0..nvars` in order, sharing one intro map), so a free variable that
/// spans answer positions renders with coordinated NewVar/VarRef the way MORK's emit does.
/// TEST tooling over the streaming join.
#[cfg(test)]
fn unify_join_zipper_coordinated(
    map: &PathMap<()>,
    factors: &[Factor],
    var_order: &[usize],
    nvars: usize,
) -> BTreeSet<Vec<u8>> {
    run_unify_join(map, factors, var_order, nvars, true).1
}

/// The per-run inputs the join state borrows: the re-indexed copies of inverted factors and the
/// per-factor plumbing derived from them. Built BEFORE [`UnifyJoin`] so the held per-factor
/// zippers can borrow the re-indexed maps — a zipper into a map owned by the state itself would
/// be a self-reference.
struct JoinPlan<'a> {
    /// Re-indexed copies of inverted factors; `factor_src[f] = Some(i)` reads `reindexes[i]`.
    reindexes: Vec<PathMap<()>>,
    factor_src: Vec<Option<usize>>,
    /// Per factor, `Some((original_prefix, new_order))` when re-indexed: the original relation
    /// prefix and the column permutation `build_reindex` applied (`new_order[j]` = original column
    /// at re-indexed position `j`), enough to reconstruct the stored fact's original bytes at a
    /// leaf.
    originals: Vec<Option<(Vec<u8>, Vec<usize>)>>,
    /// Owned because a re-indexed factor's prefix and columns differ from the input factor's;
    /// the column bytes are still borrowed from the body.
    factors: Vec<Factor<'a>>,
    /// Per factor, its columns flattened into the pre-order seek positions the join schedules and
    /// consumes ([`Step`]). Derived from `factors`, so a re-indexed factor's steps follow its
    /// permuted column order.
    steps: Vec<Vec<Step<'a>>>,
    /// `var_pos[v]` = position of global variable `v` in `var_order`, for the catch-up test.
    var_pos: Vec<usize>,
}

/// Build the join's borrowed inputs: re-index inverted factors so the join can seek them in
/// var_order; a compatible factor keeps its live-map prefix and pays nothing. `factor_src[f]`
/// selects which map factor `f` reads from. `None` when a factor's column bytes do not flatten
/// into seek positions (a truncated term, or more than `u8::MAX` variables), which the caller
/// sends down the ProductZipper path.
fn join_plan<'a>(
    map: &PathMap<()>,
    factors: &[Factor<'a>],
    var_order: &[usize],
    nvars: usize,
) -> Option<JoinPlan<'a>> {
    let nf = factors.len();
    let mut var_pos = vec![0usize; nvars];
    for (pos, &v) in var_order.iter().enumerate() {
        var_pos[v] = pos;
    }

    let mut owned: Vec<Factor<'a>> = Vec::with_capacity(nf);
    let mut reindexes: Vec<PathMap<()>> = Vec::new();
    let mut factor_src: Vec<Option<usize>> = Vec::with_capacity(nf);
    let mut originals: Vec<Option<(Vec<u8>, Vec<usize>)>> = Vec::with_capacity(nf);
    for factor in factors {
        if is_inverted(factor, &var_pos) {
            let (ri, new_cols, new_order) = build_reindex(map, factor, &var_pos);
            factor_src.push(Some(reindexes.len()));
            originals.push(Some((factor.prefix.to_vec(), new_order)));
            reindexes.push(ri);
            owned.push(Factor {
                prefix: &[],
                cols: new_cols,
            });
        } else {
            factor_src.push(None);
            originals.push(None);
            owned.push(factor.clone());
        }
    }

    let steps = owned.iter().map(factor_steps).collect::<Vec<Vec<Step<'a>>>>();

    Some(JoinPlan {
        reindexes,
        factor_src,
        originals,
        factors: owned,
        steps,
        var_pos,
    })
}

/// Build the join state over a prepared plan without running it. One zipper per factor is opened
/// HERE, at the factor's relation prefix, and then only descended/ascended in place for the whole
/// join. When `want_coordinated`, a run also collects each answer as one variable-coordinated
/// tuple encoding (see [`unify_join_zipper_coordinated`]).
fn join_state<'a>(
    map: &'a PathMap<()>,
    plan: &'a JoinPlan,
    var_order: &'a [usize],
    nvars: usize,
) -> UnifyJoin<'a> {
    let nf = plan.factors.len();
    let cursors = (0..nf)
        .map(|f| {
            let src: &'a PathMap<()> = match plan.factor_src[f] {
                Some(ri) => &plan.reindexes[ri],
                None => map,
            };
            SubtermCursor::new(src.read_zipper_at_path(plan.factors[f].prefix))
        })
        .collect();

    UnifyJoin {
        map,
        originals: &plan.originals,
        factors: &plan.factors,
        steps: &plan.steps,
        var_order,
        var_pos: &plan.var_pos,
        cursors,
        nvars,
        next_step: vec![0; nf],
        data_intro: vec![0; nf],
        bindings: Bindings::new(),
        trail: Vec::new(),
        unify_stack: Vec::new(),
        free_bufs: Vec::new(),
        free_child_bufs: Vec::new(),
        lead_max: Vec::new(),
        on_match: None,
        loc_buf: Vec::new(),
        stopped: false,

        #[cfg(test)]
        out: BTreeSet::new(),
        #[cfg(test)]
        want_coordinated: false,
        #[cfg(test)]
        coordinated: BTreeSet::new(),
        #[cfg(test)]
        on_tuple: None,
    }
}

/// Build the join state and run it, collecting answer rows (and coordinated tuples when asked).
/// Materialization is TEST tooling: the live dispatch always streams (`on_match`), so the
/// collecting fields, the row renderer and this runner compile only for tests.
#[cfg(test)]
fn run_unify_join(
    map: &PathMap<()>,
    factors: &[Factor],
    var_order: &[usize],
    nvars: usize,
    want_coordinated: bool,
) -> (BTreeSet<Vec<Option<Vec<u8>>>>, BTreeSet<Vec<u8>>) {
    let plan = join_plan(map, factors, var_order, nvars)
        .expect("parsed factors must flatten into steps");
    let mut state = join_state(map, &plan, var_order, nvars);
    state.want_coordinated = want_coordinated;
    state.recurse(0);
    (state.out, state.coordinated)
}

/// Run the join streaming each accepted assignment's own solved bindings (and factor 0's stored
/// fact, the `loc` the stock callback contract carries) to `on_match` instead of collecting rows.
/// Flattening the plan is a precondition: the factors came from `parse_body_factors`, which has
/// already walked the whole body and rejected the encodings `push_steps` could fail on.
fn run_unify_join_stream_bindings(
    map: &PathMap<()>,
    factors: &[Factor],
    var_order: &[usize],
    nvars: usize,
    on_match: &mut dyn FnMut(&Bindings, Expr) -> bool,
) {
    let plan = join_plan(map, factors, var_order, nvars)
        .expect("parsed factors must flatten into steps");
    let mut state = join_state(map, &plan, var_order, nvars);
    state.on_match = Some(on_match);
    state.recurse(0);
}

/// Run the join streaming each accepted assignment's per-factor original fact bytes to `on_tuple`.
/// Only [`tests::streamed_tuples_reconstruct_reindexed_facts`] uses this: it pins
/// [`UnifyJoin::original_fact_bytes`] on a re-indexed factor, which the dispatch itself only ever
/// reconstructs for factor 0 (never re-indexed under the identity variable order).
#[cfg(test)]
fn run_unify_join_stream(
    map: &PathMap<()>,
    factors: &[Factor],
    var_order: &[usize],
    nvars: usize,
    on_tuple: &mut dyn FnMut(&[Vec<u8>]) -> bool,
) {
    let plan = join_plan(map, factors, var_order, nvars).expect("test factors must flatten");
    let mut state = join_state(map, &plan, var_order, nvars);
    state.on_tuple = Some(on_tuple);
    state.recurse(0);
}

/// Parse an encoded conjunction body `(, p1 .. pk)` into factors, threading the body's variable
/// numbering (a NewVar takes the next id in first-occurrence order, a VarRef back-references one).
/// Returns the factors and the variable count.
/// Parse an encoded conjunction body `(, p1 .. pk)` into factors in ONE pass.
///
/// Every column is a slice of `body`, never a copy: the body outlives the join, so the plan can
/// borrow it. The same scan that finds each column's span also validates the variable numbering
/// (a `VarRef` must name an already-introduced variable), counts the body's variables, and records
/// each column's variable mask -- work that used to cost a separate traversal apiece
/// (a variable-numbering validation, a groundness walk, a variable-position walk apiece) on top
/// of three rounds of copying. Every byte of the body is visited exactly once.
///
/// EVERY conjunct shape is a factor; see the per-conjunct comment below for the two encodings.
/// A body with no conjunct at all (`(,)`, arity 1) parses to zero factors, which the join reads as
/// "match once, unconditionally" exactly as [`crate::space::Space::query_multi`] does.
///
/// Returns the factors and the variable count, or `None` if the body is not a well-formed
/// conjunction: a non-compound body, the arity-0 body `()`, a truncated term, a `VarRef` naming a
/// variable the body never introduced, or more than `u8::MAX` variables.
pub fn parse_body_factors<'a>(body: &'a Expr) -> Option<(Vec<Factor<'a>>, usize)> {
    let Tag::Arity(nconj) = byte_item(unsafe { *body.ptr }) else {
        return None;
    };
    if nconj == 0 {
        return None;
    }
    let mut intro: u8 = 0;
    let mut pos = 1usize;
    let mut factors = Vec::with_capacity(nconj.saturating_sub(1) as usize);
    for ci in 0..nconj {
        let conj_start = pos;
        if ci == 0 {
            // The `,` head itself carries no factor.
            let scan = scan_subterm(*body, pos, &mut intro)?;
            pos += scan.len;
            continue;
        }
        // Two ways to spread a whole stored fact over seekable columns. A COMPOUND conjunct
        // `(rel arg..)` seeks under its arity byte with every top-level argument a column, the
        // relation head being column 0 so query and stored heads unify either way round. Anything
        // else -- a bare symbol, a bare variable, `()` -- has no arguments to spread and becomes a
        // WHOLE-ATOM factor: empty prefix, so the cursor opens at the root where complete facts
        // live, and one column holding the conjunct. Both then take the ordinary paths, and a
        // single-column factor is never inverted, so neither reaches the re-index.
        let (prefix, ncols): (&'a [u8], usize) = match byte_item(unsafe { *body.ptr.add(pos) }) {
            Tag::Arity(arity) if arity != 0 => {
                let prefix: &'a [u8] =
                    unsafe { core::slice::from_raw_parts(body.ptr.add(conj_start), 1) };
                pos += 1;
                (prefix, arity as usize)
            }
            _ => (&[], 1),
        };
        let mut cols = Vec::with_capacity(ncols);
        for _ in 0..ncols {
            let col_intro = intro;
            let col_start = pos;
            let scan = scan_subterm(*body, pos, &mut intro)?;
            let col_expr = Expr { ptr: unsafe { body.ptr.add(col_start) } };
            cols.push(if scan.len == 1 {
                match byte_item(unsafe { *col_expr.ptr }) {
                    Tag::NewVar => FactorColumn::Var(col_intro as usize),
                    Tag::VarRef(id) => FactorColumn::Var(id as usize),
                    Tag::SymbolSize(_) | Tag::Arity(_) => FactorColumn::Term(EncodedTerm {
                        expr: col_expr,
                        intro: col_intro,
                        vars: scan.vars,
                        _borrow: PhantomData,
                    }),
                }
            } else {
                FactorColumn::Term(EncodedTerm {
                    expr: col_expr,
                    intro: col_intro,
                    vars: scan.vars,
                    _borrow: PhantomData,
                })
            });
            pos += scan.len;
        }
        factors.push(Factor { prefix, cols });
    }
    // The conjunct scans consumed exactly the body's own span: an engine-produced body is one
    // complete subterm by construction, so there is no trailing-byte case left to reject.
    Some((factors, intro as usize))
}

/// What one pass over a subterm yields.
struct SubtermScan {
    len: usize,
    vars: u64,
}

/// Walk the complete subterm at `bytes[at..]` once, returning its byte length and the mask of
/// query variables it mentions. `intro` is the running count of variables introduced by the body
/// so far and is advanced past this subterm's own `NewVar`s, which is what gives each variable its
/// body-global id. Returns `None` on a truncated term, a `VarRef` naming a variable that has not
/// been introduced, or more than `u8::MAX` variables.
fn scan_subterm(body: Expr, at: usize, intro: &mut u8) -> Option<SubtermScan> {
    let mut i = at;
    let mut pending = 1usize;
    let mut vars = 0u64;
    while pending != 0 {
        // The body is engine-produced: the encoding is trusted and read raw. What remains
        // fallible is the SEMANTIC validation -- variable numbering and the 63-variable cap.
        let b = unsafe { *body.ptr.add(i) };
        i += 1;
        pending -= 1;
        match byte_item(b) {
            Tag::Arity(arity) => pending += arity as usize,
            Tag::SymbolSize(size) => {
                i += size as usize;
            }
            Tag::NewVar => {
                let id = *intro;
                // The parser caps an expression at 63 variables, so an id never escapes the
                // mask; a body that violates that is simply not routable.
                if id >= 64 {
                    return None;
                }
                *intro = intro.checked_add(1)?;
                vars |= 1u64 << id;
            }
            Tag::VarRef(id) => {
                if id >= *intro {
                    return None;
                }
                vars |= 1u64 << id;
            }
        }
    }
    Some(SubtermScan {
        len: i - at,
        vars,
    })
}









/// The engine-facing dispatch entry: stream every product tuple the leapfrog accepts through the
/// stock `query_multi` callback contract. Each accepted assignment hands `effect` the join's OWN
/// solved bindings -- the join already carries the ProductZipper's namespace convention (query
/// variables in `QUERY_NS` = 0, factor `f`'s data in `1 + f`), and `apply` observes a binding only
/// by dereference, so this map drives the stock template emit exactly as a re-unification of the
/// same tuple would (see the leaf in [`UnifyJoin::recurse_after_catch_up`]). `loc` is factor 0's
/// stored fact, as stock passes. Returns the successful-match count, or `None` for a body that is
/// not a well-formed conjunction at all -- see [`parse_body_factors`] -- which the caller sends
/// down the ProductZipper path. Every CONJUNCT shape is handled here, including the degenerate
/// body with no conjunct. A `false` from `effect` stops the search, as it stops the stock scan.
pub fn query_multi_leapfrog<F: FnMut(Result<&[u32], &Bindings>, Expr) -> bool>(
    map: &PathMap<()>,
    pat_expr: Expr,
    mut effect: F,
) -> usize {
    // The join owns every body the engine hands it, so parsing is a precondition rather than a
    // decline: every conjunct shape is a factor, and the frontend does not emit the encodings that
    // would fail here (a `VarRef` naming a variable the body never introduced, more than 63
    // variables). A probe over the differential corpus, every resource program and the CLI suite
    // saw no body fail. A violation is a bug in the producer and should surface as one, not as a
    // silent detour to a different engine.
    let (factors, nvars) =
        parse_body_factors(&pat_expr).expect("a transform body must be a well-formed conjunction");
    if factors.is_empty() {
        // `(,)`: nothing constrains anything, so the body matches exactly once with empty
        // bindings. This mirrors `Space::query_multi`'s `n_factors == 1` arm byte for byte,
        // including that it calls `effect` once, ignores the answer, and returns 1 -- and that it
        // does NOT bump the `unifications` counter, so the printed statistics stay identical.
        effect(Err(&Bindings::new()), pat_expr);
        return 1;
    }
    let var_order: Vec<usize> = (0..nvars).collect();
    #[cfg(debug_assertions)]
    {
        // The factor count the stock path would pair up (`pat_args[1..]`, the conjunction's
        // arguments) is the parsed factor count; the per-factor data namespaces `1 + f` line
        // up with it positionally.
        let mut pat_args = Vec::new();
        ExprEnv::new(0, pat_expr).args(&mut pat_args);
        debug_assert_eq!(pat_args.len() - 1, factors.len());
    }
    let mut candidate = 0usize;
    let mut on_match = |bindings: &Bindings, loc: Expr| -> bool {
        unsafe { crate::space::unifications += 1 };
        candidate += 1;
        // The effect borrows the join's live map for the duration of the answer -- the last
        // per-answer allocation of the emit path (a BTreeMap deep clone) is gone.
        effect(Err(bindings), loc)
    };
    run_unify_join_stream_bindings(map, &factors, &var_order, nvars, &mut on_match);
    candidate
}



















/// A reusable candidate list for one recursion depth of the lead enumeration. `entries[..len]`
/// are the live candidates; entries past `len` are retained allocations whose capacity the next
/// fill reuses, so a node's enumeration allocates only when a candidate outgrows a recycled
/// buffer. Pure storage reuse: the candidates and their order are exactly what a fresh
/// `Vec<Vec<u8>>` collection produced.
#[derive(Default)]
struct CandidateBuf {
    entries: Vec<Vec<u8>>,
    /// Per entry, `(NewVar count, total variable count)` read off the enumerating cursor, so the
    /// consumer never rescans the bytes for what the enumeration walk already knew.
    meta: Vec<(u8, u8)>,
    len: usize,
}

impl CandidateBuf {
    fn push_from(&mut self, bytes: &[u8], vars: (u8, u8)) {
        if self.len < self.entries.len() {
            let entry = &mut self.entries[self.len];
            entry.clear();
            entry.extend_from_slice(bytes);
            self.meta[self.len] = vars;
        } else {
            self.entries.push(bytes.to_vec());
            self.meta.push(vars);
        }
        self.len += 1;
    }
}



struct UnifyJoin<'a> {
    map: &'a PathMap<()>,
    /// Per factor, `Some((original_prefix, new_order))` when re-indexed: the original relation
    /// prefix and the column permutation `build_reindex` applied (`new_order[j]` = original column
    /// at re-indexed position `j`), enough to reconstruct the stored fact's original bytes at a
    /// leaf.
    originals: &'a [Option<(Vec<u8>, Vec<usize>)>],
    factors: &'a [Factor<'a>],
    /// Per factor, its columns flattened into pre-order seek positions ([`Step`]). This, not
    /// `factors[f].cols`, is what the join walks: a variable at ANY depth is its own position, so
    /// it can be scheduled and intersected across factors.
    steps: &'a [Vec<Step<'a>>],
    var_order: &'a [usize],
    /// `var_pos[v]` = position of global variable `v` in `var_order`, for the catch-up test.
    var_pos: &'a [usize],
    /// One held zipper per factor, wrapped in the subterm cursor. Every consumed column value
    /// is descended in place and ascended on unwind, so the cursor's floor always sits at
    /// prefix + consumed columns and no probe pays an O(path) re-descent from the trie root.
    /// The consumed bytes themselves live on the zipper's path (`consumed_bytes`); the join
    /// keeps no mirror of them.
    cursors: Vec<SubtermCursor<ReadZipperUntracked<'a, 'static, ()>>>,
    nvars: usize,
    /// Per factor, the index of the seek position it is currently at in `steps[f]`.
    next_step: Vec<usize>,
    data_intro: Vec<u8>,
    bindings: Bindings,
    /// Keys inserted into `bindings` by incremental unification, in order; `match_candidate`
    /// unwinds to its mark on backtrack. See [`mork_expr::unify_into`].
    trail: Vec<ExprVar>,
    /// Scratch equation stack for [`mork_expr::unify_into`], reused across candidates.
    unify_stack: Vec<(ExprEnv, ExprEnv)>,
    /// Pool of [`CandidateBuf`]s for the lead enumeration, one in flight per active recursion
    /// depth; released buffers return here with their allocations intact.
    free_bufs: Vec<CandidateBuf>,
    /// Pool of child-env buffers for compounds that must still be walked per candidate (a compound
    /// reached by dereferencing a bound variable). `match_compound_children` recurses while holding
    /// its slice, so one buffer is in flight per active depth; released buffers return here with
    /// their allocations intact. Pure storage reuse: the children and their order are exactly what
    /// a fresh `Vec<ExprEnv>` collection produced.
    free_child_bufs: Vec<Vec<ExprEnv>>,
    /// Reusable scratch for the mutual seek's running key in [`Self::fill_lead_candidates`]. Only
    /// live inside that call, which completes before the node recurses, so one buffer serves every
    /// depth.
    lead_max: Vec<u8>,
    /// When set, each accepted assignment streams the join's OWN bindings (plus factor 0's stored
    /// fact as the stock contract's `loc`) here instead of collecting rows, and a `false` return
    /// stops the search. The engine dispatch uses this.
    on_match: Option<&'a mut dyn FnMut(&Bindings, Expr) -> bool>,
    /// Scratch for the streamed `loc`: factor 0's stored fact bytes, refilled per accepted
    /// assignment so the stream costs no allocation per answer.
    loc_buf: Vec<u8>,
    /// Set when a stream callback asked to stop; the recursion unwinds without visiting more
    /// candidates.
    stopped: bool,

    /// Answer rows, one `Option` per query variable: `Some(bytes)` for a resolved term, `None` for
    /// a still-free variable. TEST-ONLY: the live dispatch always streams.
    #[cfg(test)]
    out: BTreeSet<Vec<Option<Vec<u8>>>>,
    /// When set, also collect each answer as one variable-coordinated tuple encoding. TEST-ONLY.
    #[cfg(test)]
    want_coordinated: bool,
    /// Answer tuples encoded through one shared intro map, so free-variable coreference across
    /// answer positions survives. TEST-ONLY.
    #[cfg(test)]
    coordinated: BTreeSet<Vec<u8>>,
    /// Test-only tuple stream (see [`run_unify_join_stream`]).
    #[cfg(test)]
    on_tuple: Option<&'a mut dyn FnMut(&[Vec<u8>]) -> bool>,
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
            #[cfg(test)]
            if self.on_tuple.is_some() {
                // Test-only tuple stream: reconstruct every factor's stored fact (see
                // `run_unify_join_stream`). Never set by the dispatch.
                let tuple: Vec<Vec<u8>> = (0..self.factors.len())
                    .map(|f| self.original_fact_bytes(f))
                    .collect();
                let cb = self.on_tuple.as_mut().unwrap();
                if !cb(&tuple) {
                    self.stopped = true;
                }
                return;
            }
            if self.on_match.is_some() {
                // Hand over the bindings this join already solved, in the namespaces the stock
                // path uses (query variables in `QUERY_NS`, factor `f`'s data in `1 + f`), rather
                // than rebuilding every fact and re-unifying per tuple. `apply` observes a binding
                // only by dereferencing it, so map shape -- path compression, which end of a
                // var-var equation survived -- is invisible downstream, and a cyclic assignment is
                // handed over exactly as stock hands one over, for the engine's post-apply
                // `cycled` check to drop (`dispatch_touched_parity_on_transform` pins the counts).
                // `loc` is factor 0's stored fact; refill the scratch instead of allocating.
                let mut buf = std::mem::take(&mut self.loc_buf);
                buf.clear();
                self.original_fact_bytes_into(0, &mut buf);
                let loc = Expr {
                    ptr: buf.as_ptr().cast_mut(),
                };
                let keep = {
                    let bindings = &self.bindings;
                    let cb = self.on_match.as_mut().unwrap();
                    cb(bindings, loc)
                };
                self.loc_buf = buf;
                if !keep {
                    self.stopped = true;
                }
                return;
            }
            // TEST-ONLY materialization below: the live dispatch always installs `on_match`.
            #[cfg(not(test))]
            unreachable!("the live join always streams through on_match");
            // Keep every component that resolved to a term, ground or schematic. A variable that is
            // still free is None; the live emit can then render schematic compounds and leave free
            // variables fresh, matching the ProductZipper's byte output.
            //
            #[cfg(test)]
            {
                // `mork_expr::unify` checks occurs only per equation, so a cycle can arrive
                // through a chain of columns (the join-propagated capture builds x0 = (k (k x0))).
                // `apply` records in `cycled` every variable whose cycle it had to cut;
                // `Expr::_unify` rejects exactly that after its own apply. Mirror it per answer
                // row: a cyclic assignment is an occurs violation and yields no answer, as the
                // ProductZipper's full unification does.
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
            }
            #[cfg(test)]
            return;
        }
        let v = self.var_order[i];
        // The participating factors are those whose CURRENT seek position is this variable --
        // wherever that position sits in the term. Before flattening this asked only about
        // top-level argument columns, so under a namespace wrapper no factor ever qualified, the
        // multiway intersection never engaged, and the structural descent degenerated into the
        // ProductZipper's nested loop with the join's machinery on top.
        let mut parts: Vec<usize> = (0..self.factors.len())
            .filter(|&f| {
                let ns = self.next_step[f];
                matches!(self.steps[f].get(ns), Some(Step::Var(cv)) if *cv == v)
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
        // few candidates and the rest seek. This is what makes a selective factor, say (e a $y)
        // with a few edges, drive the join instead of the whole relation.
        self.rank_parts(&mut parts);
        let nr = self.partition_restrictors(&mut parts);
        self.consume_lead(&parts, nr, v, i);
    }

    /// Order the participating factors by domain size, smallest first, so `parts[0]` leads.
    ///
    /// The count is a ROUND ROBIN: every participating cursor is stepped one value per round, and
    /// counting stops at the end of the round in which some cursor runs out. That cursor is the
    /// exact argmin, so a tiny domain wins the lead even against a domain of millions. The former
    /// per-factor count-to-32 could not: it scored every domain over the cap equal and left the
    /// choice to syntactic factor order, so a 100k-value factor beat a 100-value one and the join
    /// enumerated 100k candidates to keep 100.
    ///
    /// The bound is self-financing rather than a fixed cap. The scan costs
    /// `parts.len() * (min_domain + 1)` cursor steps, and the node then enumerates the lead's
    /// `min_domain` candidates, matching every other participating factor against each one -- at
    /// least `min_domain * (parts.len() - 1)` steps. So the estimate stays within a constant factor
    /// of the enumeration it is choosing, and it never scales with the total space size: nothing
    /// here reads more than the SMALLEST participating domain (plus one step per larger one), which
    /// is why a full `val_count` (O(subtree), climbing with the whole relation) is still refused.
    /// `HARD_ROUNDS` only stops a node whose EVERY domain is huge from an unbounded pre-scan; that
    /// node is about to enumerate at least that many candidates anyway.
    fn rank_parts(&mut self, parts: &mut [usize]) {
        const HARD_ROUNDS: usize = 512;
        if parts.len() < 2 {
            return;
        }
        // (values counted, exhausted, factor). One allocation, as the former keyed sort had.
        let mut rows: Vec<(usize, bool, usize)> = parts.iter().map(|&f| (0usize, false, f)).collect();
        for row in rows.iter() {
            self.cursors[row.2].first();
        }
        let mut round = 0usize;
        loop {
            round += 1;
            let mut alive = false;
            let mut exhausted = false;
            for row in rows.iter_mut() {
                if row.1 {
                    continue;
                }
                let cur = &mut self.cursors[row.2];
                if cur.at_end {
                    row.1 = true;
                    exhausted = true;
                    continue;
                }
                row.0 += 1;
                cur.next();
                alive = true;
            }
            if !alive || exhausted || round >= HARD_ROUNDS {
                break;
            }
        }
        for row in rows.iter() {
            self.cursors[row.2].reset_to_floor();
        }
        // A cursor that ran out carries its EXACT domain size, and one still alive carries the
        // round count, which is strictly larger, so exact counts always sort first. The sort is
        // stable, so equal counts keep syntactic factor order, as the former estimate sort did.
        rows.sort_by_key(|row| row.0);
        for (j, row) in rows.iter().enumerate() {
            parts[j] = row.2;
        }
    }

    /// Stable-partition `parts[1..]` so the factors whose current column matches only by equality
    /// come first, and return how many there are. Those are the ones the mutual seek in
    /// [`Self::fill_lead_candidates`] may intersect the lead against; a factor holding a stored
    /// variable at this column unifies with anything and stays in the ordinary cascade.
    /// Every cursor sits at its column floor here, which is where the child mask is read.
    fn partition_restrictors(&mut self, parts: &mut [usize]) -> usize {
        // Only symbol-headed lead values are prunable, so a lead column offering none (a column of
        // compounds, say) has nothing to intersect: answer 0 off ONE mask read instead of scanning
        // every other factor's.
        if least_ge(
            &self.cursors[parts[0]].floor_child_mask(),
            item_byte(Tag::SymbolSize(1)),
        )
        .is_none()
        {
            return 0;
        }
        let mut nr = 0usize;
        for j in 1..parts.len() {
            if !mask_has_wildcard(&self.cursors[parts[j]].floor_child_mask()) {
                nr += 1;
                // Rotate the entry down to the end of the restrictor group, keeping both groups'
                // relative order.
                parts[nr..=j].rotate_right(1);
            }
        }
        nr
    }

    /// The stored fact factor `f` sits on at a leaf, in its original encoding. A factor read from
    /// the live map is its prefix plus the bound column bytes. A re-indexed factor's bound bytes
    /// are its permuted, canonically renumbered columns; putting the columns back in original
    /// order and renumbering again (first reference NewVar, later ones VarRef of the new index) is
    /// exactly the stored encoding, because a stored fact is itself numbered canonically in column
    /// order.
    #[cfg(test)]
    fn original_fact_bytes(&self, f: usize) -> Vec<u8> {
        let mut out = Vec::new();
        self.original_fact_bytes_into(f, &mut out);
        out
    }

    /// [`Self::original_fact_bytes`] appending into a caller-owned buffer, so the streaming
    /// dispatch reuses one allocation for every answer's `loc`.
    fn original_fact_bytes_into(&self, f: usize, out: &mut Vec<u8>) {
        match &self.originals[f] {
            None => {
                out.extend_from_slice(self.factors[f].prefix);
                out.extend_from_slice(self.cursors[f].consumed_bytes());
            }
            Some((orig_prefix, new_order)) => {
                let ncols = self.factors[f].cols.len();
                let spans = split_columns(self.cursors[f].consumed_bytes(), ncols);
                let items = columns_to_items(&spans);
                // `orig_positions[c]` = where original column `c` sits in the re-indexed layout,
                // so emitting in that order restores the original column order.
                let mut orig_positions = vec![0usize; ncols];
                for (j, &c) in new_order.iter().enumerate() {
                    orig_positions[c] = j;
                }
                let mark = out.len();
                out.extend_from_slice(orig_prefix);
                out.extend_from_slice(&emit_reordered(&items, &orig_positions));
                debug_assert!(
                    self.map.read_zipper_at_path(&out[mark..]).val().is_some(),
                    "re-indexed leaf must reconstruct a fact stored in the source map"
                );
            }
        }
    }

    fn factor_has_value(&self, f: usize) -> bool {
        if self.next_step[f] != self.steps[f].len() {
            return false;
        }
        self.cursors[f].has_value()
    }

    /// Fill `buf` with the children of factor `f`'s current column, for the lead whose join
    /// variable is still free (structured children and wildcards alike), in the cursor's
    /// ascending subterm order. Enumerates on the held cursor and restores it to the column
    /// floor.
    fn fill_free_candidates(&mut self, f: usize, buf: &mut CandidateBuf) {
        let cur = &mut self.cursors[f];
        cur.first();
        while let Some(k) = cur.key() {
            let vars = cur.key_var_counts();
            buf.push_from(k, vars);
            cur.next();
        }
        cur.reset_to_floor();
    }

    /// Fill `buf` with the LEAD's candidate values for a still-free join variable and return the
    /// index of the first candidate the mutual seek confirmed present in every restrictor.
    ///
    /// This is the true leapfrog intersection, modelled on [`GroundJoin::leapfrog`]: seek every
    /// restrictor to the candidate, and when one answers with a larger value, leap the lead
    /// straight there instead of walking (and then unifying, binding, and unwinding) the values in
    /// between. `restrictors` are the other participating factors whose column matches only by
    /// equality (see [`mask_has_wildcard`]).
    ///
    /// Soundness, which is the whole subtlety here, rests on [`is_symbol_head`]: this join UNIFIES,
    /// so a stored value may match a candidate without equalling it, and an exact intersection would
    /// silently drop answers. A candidate is prunable only where unifiability IS equality. Symbol-
    /// headed candidates are ground, and a restrictor's column holds no stored variable, so at that
    /// column only the same symbol unifies with them (a stored compound cannot unify with a symbol
    /// at all). Symbol bytes sort above every compound and variable byte, so those candidates form
    /// a SUFFIX of the enumeration: everything before it -- stored wildcards, and compounds that a
    /// stored schematic compound like `(f $x)` unifies with without equalling -- is pushed
    /// unfiltered, and the seek never skips over any of it. The surviving candidates are therefore a
    /// subsequence of the unfiltered ones in the same order, so the join's visit order is unchanged.
    fn fill_lead_candidates(
        &mut self,
        f: usize,
        restrictors: &[usize],
        buf: &mut CandidateBuf,
    ) -> usize {
        {
            let cur = &mut self.cursors[f];
            cur.first();
            while let Some(k) = cur.key() {
                if is_symbol_head(k[0]) {
                    break;
                }
                let vars = cur.key_var_counts();
                buf.push_from(k, vars);
                cur.next();
            }
        }
        let confirmed_from = buf.len;
        if restrictors.is_empty() {
            let cur = &mut self.cursors[f];
            while let Some(k) = cur.key() {
                let vars = cur.key_var_counts();
                buf.push_from(k, vars);
                cur.next();
            }
            cur.reset_to_floor();
            return confirmed_from;
        }
        'candidates: while !self.cursors[f].at_end {
            // Copy the candidate out once so `seek` can take the cursors mutably below.
            let (lead_max, cursors) = (&mut self.lead_max, &self.cursors);
            lead_max.clear();
            lead_max.extend_from_slice(cursors[f].key().unwrap());
            for &r in restrictors {
                let (cursors, lead_max) = (&mut self.cursors, &self.lead_max);
                cursors[r].seek(lead_max);
                if cursors[r].at_end {
                    // Nothing stored at or above the candidate: every remaining candidate is a
                    // ground symbol at least as large, so none of them can match this factor.
                    break 'candidates;
                }
                if cursors[r].key().unwrap() != self.lead_max.as_slice() {
                    // The restrictor's least value at or above the candidate is larger, so every
                    // lead value in between is a ground symbol absent from this factor. Leap there.
                    // The target is a symbol, so the lead lands on a symbol too and skips nothing
                    // outside the prunable suffix.
                    let (lead_max, cursors) = (&mut self.lead_max, &self.cursors);
                    lead_max.clear();
                    lead_max.extend_from_slice(cursors[r].key().unwrap());
                    let (cursors, lead_max) = (&mut self.cursors, &self.lead_max);
                    cursors[f].seek(lead_max);
                    continue 'candidates;
                }
            }
            // The confirmed candidate IS the lead cursor's current key, so its counts are too.
            buf.push_from(&self.lead_max, self.cursors[f].key_var_counts());
            self.cursors[f].next();
        }
        self.cursors[f].reset_to_floor();
        for &r in restrictors {
            self.cursors[r].reset_to_floor();
        }
        confirmed_from
    }

    /// Probe factor `f`'s current ground column: whether the trie holds the exact ground subterm,
    /// plus the column's child mask. The stored wildcards at this position are exactly the
    /// wildcard tag bytes set in that mask: a wildcard is a complete single-byte subterm, so its
    /// presence as a child byte at the column start is its presence as a stored subterm (the
    /// compound path in [`Self::match_compound_at_current`] relies on the same fact). The mask
    /// iterates in ascending byte order, the order the former seek-to-`VarRef(0)`-and-scan
    /// produced. Probes on the held cursor (mask read at the floor, then one exact seek) and
    /// restores it to the column floor.
    fn ground_probe(&mut self, f: usize, ground: &[u8]) -> (bool, ByteMask) {
        let cur = &mut self.cursors[f];
        let mask = cur.floor_child_mask();
        cur.seek(ground);
        let exact = cur.key() == Some(ground);
        cur.reset_to_floor();
        (exact, mask)
    }

    /// The counts a single stored wildcard byte contributes: it IS one variable.
    #[inline]
    fn wildcard_counts(w: u8) -> (u8, u8) {
        match byte_item(w) {
            Tag::NewVar => (1, 1),
            Tag::VarRef(_) => (0, 1),
            _ => unreachable!("wildcard branches descend only variable tag bytes"),
        }
    }

    fn query_var_env(&self, v: usize) -> ExprEnv {
        ExprEnv::with_intro(QUERY_NS, v as u8, Expr::from_slice(&NEW_VAR_EXPR_BYTES))
    }

    #[allow(dead_code)]
    fn var_env(&self, (n, v): ExprVar) -> ExprEnv {
        ExprEnv::with_intro(n, v, Expr::from_slice(&NEW_VAR_EXPR_BYTES))
    }

    /// An env viewing `bytes` where they already are. The candidate's bytes always live in memory
    /// that outlives the env: a pooled [`CandidateBuf`] entry, held by the enumerating frame for
    /// the whole subtree that can observe the binding, or a `'static` one-byte wildcard (see
    /// [`single_byte`]). So this used to copy each candidate into an arena of boxed slices -- one
    /// allocation per candidate, and a drop per entry when the arena unwound -- to buy a lifetime
    /// it already had.
    ///
    /// The requirement is on the CALLER, and `ExprEnv` holds a raw `Expr`, so the compiler will not
    /// state it: the bytes must outlive every use of the returned env, including the answer emit
    /// that reads it out of `bindings`.
    fn env_over(&mut self, namespace: u8, intro: u8, bytes: &[u8], ground: bool) -> ExprEnv {
        // Groundness arrives from whoever walked the bytes (the enumerating cursor's exact tag
        // counts, or a wildcard branch that knows it descended a variable) -- never from a rescan.
        let mut env = ExprEnv::with_intro(namespace, intro, Expr::from_slice(bytes));
        if ground && bytes.len() <= u16::MAX as usize {
            // SAFETY: `bytes` IS the subterm (the enumeration copied exactly one complete value),
            // and `ground` came from the walk that produced it, not from a guess.
            unsafe { env.stamp_ground(bytes.len() as u16) };
        }
        env
    }

    fn data_env_for(&mut self, f: usize, bytes: &[u8], vars: (u8, u8)) -> ExprEnv {
        // Factor f's data lives in namespace 1 + f; QUERY_NS = 0 is the query's own.
        self.env_over(1 + f as u8, self.data_intro[f], bytes, vars.1 == 0)
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

    #[cfg(test)]
    fn query_component(&self, v: usize, cycled: &mut BTreeMap<ExprVar, u8>) -> Option<Vec<u8>> {
        let env = self.query_var_env(v);
        if self.deref_env(env).var_opt().is_some() {
            None
        } else {
            Some(self.emit_env_bytes(env, cycled))
        }
    }

    #[cfg(test)]
    fn applied_var_len(&self, key: ExprVar, stack: &mut Vec<ExprVar>) -> usize {
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

    #[cfg(test)]
    fn applied_len_inner(&self, env: ExprEnv, stack: &mut Vec<ExprVar>) -> usize {
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

    #[cfg(test)]
    fn applied_len(&self, env: ExprEnv) -> usize {
        self.applied_len_inner(env, &mut Vec::new())
    }

    #[allow(deprecated)]
    #[cfg(test)]
    fn apply_env_into(
        &self,
        env: ExprEnv,
        new_intros: u8,
        out: &mut Vec<u8>,
        cycled: &mut BTreeMap<ExprVar, u8>,
        stack: &mut Vec<ExprVar>,
        assignments: &mut Vec<ExprVar>,
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

    #[cfg(test)]
    fn emit_env_bytes(&self, env: ExprEnv, cycled: &mut BTreeMap<ExprVar, u8>) -> Vec<u8> {
        let mut out = Vec::new();
        let mut stack = Vec::new();
        let mut assignments = Vec::new();
        self.apply_env_into(env, 0, &mut out, cycled, &mut stack, &mut assignments);
        out
    }

    #[cfg(test)]
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
        self.consume_col(f, v, &mut |this| {
            this.consume_var_parts(parts, pi + 1, v, i);
        });
    }

    /// The lead level for a still-free join variable `v`: `parts[0]` offers its column's values and
    /// the remaining participating factors match against each accepted value.
    ///
    /// `parts[1..][..nr]` are the equality-matching restrictors ([`Self::partition_restrictors`]),
    /// which the mutual seek in [`Self::fill_lead_candidates`] has already intersected with the lead
    /// over the ground-symbol candidates. For those candidates the restrictors' columns are consumed
    /// right here -- their only possible match is that exact value, already located -- and the
    /// cascade handles only the rest; every other candidate goes through the full cascade over all
    /// of `parts[1..]`, so stored wildcards and schematic compounds keep the unchanged path.
    ///
    /// The binding of the lead's own candidate is exactly what [`Self::match_expr_at_current`]'s
    /// free-variable branch does, including its ground fast bind.
    fn consume_lead(&mut self, parts: &[usize], nr: usize, v: usize, i: usize) {
        if self.stopped {
            return;
        }
        let f = parts[0];
        let pattern = self.query_var_env(v);
        let free_key = self
            .deref_env(pattern)
            .var_opt()
            .expect("the lead level runs only for a still-free join variable");
        let mut buf = self.free_bufs.pop().unwrap_or_default();
        let confirmed_from = self.fill_lead_candidates(f, &parts[1..1 + nr], &mut buf);
        for ci in 0..buf.len {
            if self.stopped {
                break;
            }
            let (restrictors, rest) = if ci >= confirmed_from {
                (&parts[1..1 + nr], &parts[1 + nr..])
            } else {
                (&parts[..0], &parts[1..])
            };
            let cand = &buf.entries[ci];
            let mut cont = |this: &mut Self| {
                this.next_step[f] += 1;
                this.descend_restrictors(restrictors, 0, cand, &mut |this| {
                    this.consume_var_parts(rest, 0, v, i);
                });
                this.next_step[f] -= 1;
            };
            let vars = buf.meta[ci];
            if vars.1 == 0 {
                // The ground fast bind, with the same precondition and reasoning as the general
                // free-variable branch in `match_expr_at_current`. Groundness is the cursor's
                // exact count, not a rescan of the candidate.
                let data_env = self.data_env_for(f, cand, vars);
                let previous = self.bindings.insert(free_key, data_env);
                debug_assert!(previous.is_none(), "deref ended at a bound var");
                self.with_bound_path_bytes(f, cand, 0, &mut cont);
                self.bindings.remove(&free_key);
            } else {
                self.match_candidate(f, pattern, cand, vars, &mut cont);
            }
        }
        buf.len = 0;
        self.free_bufs.push(buf);
    }

    /// Consume the confirmed column of each restrictor in turn, then continue. The mutual seek
    /// established that `value` -- a ground symbol -- is stored at this column and that the column
    /// holds no stored variable, so `consume_col` would seek to exactly this value, bind it with no
    /// intro of its own, and find no wildcard alternative: that is what happens here, without the
    /// mask read and the ascend-then-re-descend the general path pays. The cursor's FLOOR descends
    /// into the value it is already positioned on, in place, and `bound[r]` grows by the same bytes
    /// `with_bound_path_bytes` would have appended. Every exit leaves the cursor back at its column
    /// floor, which the ancestors' `ascend_raw` requires.
    fn descend_restrictors(
        &mut self,
        restrictors: &[usize],
        j: usize,
        value: &[u8],
        cont: &mut dyn FnMut(&mut Self),
    ) {
        if j == restrictors.len() {
            cont(self);
            return;
        }
        let r = restrictors[j];
        self.cursors[r].seek(value);
        if self.cursors[r].key() != Some(value) {
            // Unreachable given the mutual seek's agreement; treated as "no match", which is what
            // the general path would conclude from the same probe.
            debug_assert!(false, "the mutual seek's agreement must still hold");
            self.cursors[r].reset_to_floor();
            return;
        }
        self.cursors[r].descend_floor();
        self.next_step[r] += 1;
        self.descend_restrictors(restrictors, j + 1, value, cont);
        self.next_step[r] -= 1;
        self.cursors[r].ascend_floor();
        self.cursors[r].reset_to_floor();
    }

    /// Match `env` against factor `f`'s current seek position and recurse with that position
    /// consumed (`next_step` advanced by one), stack-disciplined. Used for a [`Step::Var`] slot,
    /// whose value may be anything the variable is bound to, so the dynamic descent in
    /// [`Self::match_expr_at_current`] does the work.
    fn consume_env(
        &mut self,
        f: usize,
        env: ExprEnv,
        cont: &mut dyn FnMut(&mut Self),
    ) {
        self.match_expr_at_current(f, env, &mut |this| {
            this.next_step[f] += 1;
            cont(this);
            this.next_step[f] -= 1;
        });
    }

    fn consume_col(&mut self, f: usize, v: usize, cont: &mut dyn FnMut(&mut Self)) {
        self.consume_env(f, self.query_var_env(v), cont);
    }

    /// Consume factor `f`'s current seek position, calling `cont` once per way the stored data can
    /// match it, with `next_step[f]` advanced past exactly what that match covered.
    fn consume_step(&mut self, f: usize, cont: &mut dyn FnMut(&mut Self)) {
        let s = self.next_step[f];
        match self.steps[f][s] {
            Step::Var(v) => self.consume_col(f, v, cont),
            Step::Sym(env, _) => self.consume_sym(f, s, env, cont),
            Step::Compound { env, end, .. } => self.consume_compound(f, s, env, end, cont),
        }
    }

    /// A ground symbol position. Byte equality is unifiability on ground terms, so an exact probe
    /// hit binds the bytes directly; and a stored WILDCARD at this position unifies with the symbol
    /// too, so every variable tag byte in the column's child mask is its own branch. Both are what
    /// [`Self::match_expr_at_current`]'s `Tag::SymbolSize` arm did for a top-level symbol column;
    /// the only change is that this now also runs at depth.
    fn consume_sym(
        &mut self,
        f: usize,
        s: usize,
        env: ExprEnv,
        cont: &mut dyn FnMut(&mut Self),
    ) {
        // The symbol's span reads off its own tag: the encoding is trusted.
        let bytes = unsafe {
            let p = env.base.ptr.add(env.offset as usize);
            let Tag::SymbolSize(size) = byte_item(*p) else {
                unreachable!("a Sym step points at a symbol tag");
            };
            core::slice::from_raw_parts(p, 1 + size as usize)
        };
        let (exact, mask) = self.ground_probe(f, bytes);
        if exact {
            self.with_bound_path_bytes(f, bytes, 0, &mut |this| {
                this.next_step[f] = s + 1;
                cont(this);
                this.next_step[f] = s;
            });
        }
        if mask_has_wildcard(&mask) {
            for w in mask.iter() {
                if is_wildcard_term(w) {
                    self.match_candidate(f, env, single_byte(w), Self::wildcard_counts(w), &mut |this| {
                        this.next_step[f] = s + 1;
                        cont(this);
                        this.next_step[f] = s;
                    });
                }
            }
        }
    }

    /// A compound position. THE trap this module keeps re-learning: the ground structure must NOT
    /// be absorbed into a seek prefix. A stored variable at this very position is a wildcard that
    /// captures the WHOLE subterm -- `(data $w)` must match a query `(data (e a b))` -- so the
    /// child mask is read here and every wildcard byte becomes its own branch, unified against the
    /// whole query subterm and skipping the subtree's steps (`end`). Only then is the arity byte
    /// descended, with the children left to the following steps, so a variable inside them is
    /// schedulable.
    fn consume_compound(
        &mut self,
        f: usize,
        s: usize,
        env: ExprEnv,
        end: usize,
        cont: &mut dyn FnMut(&mut Self),
    ) {
        // Arity reads off the tag byte: the encoding is trusted.
        let arity = unsafe {
            let Tag::Arity(arity) = byte_item(*env.base.ptr.add(env.offset as usize)) else {
                unreachable!("a Compound step points at an arity tag");
            };
            arity
        };
        // One mask read serves both the wildcard candidates and the arity-byte test: each
        // `match_candidate` restores `bound[f]`, so the zipper position is the same throughout.
        let mask = self.cursors[f].floor_child_mask();
        if mask_has_wildcard(&mask) {
            for w in mask.iter() {
                if is_wildcard_term(w) {
                    self.match_candidate(f, env, single_byte(w), Self::wildcard_counts(w), &mut |this| {
                        this.next_step[f] = end;
                        cont(this);
                        this.next_step[f] = s;
                    });
                }
            }
        }
        let arity_byte = item_byte(Tag::Arity(arity));
        if mask.test_bit(arity_byte) {
            self.with_bound_path_bytes(f, &[arity_byte], 0, &mut |this| {
                this.next_step[f] = s + 1;
                cont(this);
                this.next_step[f] = s;
            });
        }
    }

    fn with_bound_path_bytes(
        &mut self,
        f: usize,
        bytes: &[u8],
        intro_delta: u8,
        cont: &mut dyn FnMut(&mut Self),
    ) {
        let intro = self.data_intro[f];
        self.data_intro[f] += intro_delta;
        // The held cursor's floor IS prefix+bound: descend the fragment in place on entry,
        // ascend it on exit, with no root re-open and no byte mirror to keep in step.
        self.cursors[f].descend_raw(bytes);
        cont(self);
        self.cursors[f].ascend_raw(bytes.len());
        self.data_intro[f] = intro;
    }

    fn match_candidate(
        &mut self,
        f: usize,
        pattern: ExprEnv,
        bytes: &[u8],
        vars: (u8, u8),
        cont: &mut dyn FnMut(&mut Self),
    ) {
        if self.stopped {
            return;
        }
        // Bind the ONE new equation against the live map, and unwind by trail instead of cloning
        // the whole map and re-solving every prior equation per candidate. The 3-axiom step trace
        // showed the same binding re-derived up to 18x per answer under the old scheme, and on the
        // big.metta self-join the re-solving cost 11.6x the ProductZipper's unification work.
        let data_env = self.data_env_for(f, bytes, vars);
        let mark = self.trail.len();
        self.unify_stack.clear();
        self.unify_stack.push((pattern, data_env));
        let mut stack = std::mem::take(&mut self.unify_stack);
        let mut trail = std::mem::take(&mut self.trail);
        let ok = unify_into(&mut self.bindings, &mut stack, &mut trail).is_ok();
        self.unify_stack = stack;
        self.trail = trail;
        if ok {
            // The intro delta is the candidate's NewVar count, which the enumeration walk already
            // counted exactly -- no rescan, no `newvars` item walk.
            self.with_bound_path_bytes(f, bytes, vars.0, cont);
        }
        // A failed unify may have inserted before failing; unwind either way. An insert target is
        // always a previously-unbound key, so removal restores the map exactly.
        for k in self.trail.split_off(mark) {
            self.bindings.remove(&k);
        }
    }

    fn match_expr_at_current(
        &mut self,
        f: usize,
        pattern: ExprEnv,
        cont: &mut dyn FnMut(&mut Self),
    ) {
        let resolved = self.deref_env(pattern);
        if let Some(free_key) = resolved.var_opt() {
            // The lead enumeration: refill a pooled buffer instead of collecting a fresh
            // `Vec<Vec<u8>>` at every node; candidates and their order are unchanged.
            let mut buf = self.free_bufs.pop().unwrap_or_default();
            self.fill_free_candidates(f, &mut buf);
            for ci in 0..buf.len {
                if self.stopped {
                    break;
                }
                let vars = buf.meta[ci];
                if vars.1 == 0 {
                    // Free variable against a GROUND candidate: unification degenerates to one
                    // binding, so skip the full re-unify. Precondition: `pattern` derefs (through
                    // `self.bindings`) to the free var `free_key` (so `free_key` is absent from
                    // the map) and the candidate is ground (no vars, so no occurs check and no
                    // constraint on any other binding). `mork_expr::unify` on the same equations
                    // would bind the pattern's own var key to the data env first (its `derefBound`
                    // walks the map it is building, which starts empty) and then, re-solving the
                    // existing bindings' equations, bind `free_key` to the same ground env while
                    // path-compressing entries that deref through the chain. Inserting only
                    // `free_key -> data_env` yields the same deref closure — every chain still
                    // resolves to the same ground bytes — so accept/reject decisions and emitted
                    // bytes are unchanged; like the ground-symbol direct bind below, we keep the
                    // uncompressed (deref-equivalent) map shape. Non-ground candidates (stored
                    // wildcards, schematic compounds) keep the general path.
                    let data_env = self.data_env_for(f, &buf.entries[ci], vars);
                    let previous = self.bindings.insert(free_key, data_env);
                    debug_assert!(previous.is_none(), "deref ended at a bound var");
                    self.with_bound_path_bytes(f, &buf.entries[ci], 0, cont);
                    self.bindings.remove(&free_key);
                } else {
                    self.match_candidate(f, pattern, &buf.entries[ci], vars, cont);
                }
            }
            buf.len = 0;
            self.free_bufs.push(buf);
            return;
        }
        match byte_item(unsafe { *resolved.subsexpr().ptr }) {
            Tag::Arity(_) => self.match_compound_at_current(f, pattern, resolved, cont),
            Tag::NewVar | Tag::VarRef(_) => unreachable!(),
            Tag::SymbolSize(_) => {
                // A symbol holds no variables, so the resolved value needs no substitution: its
                // bytes are the subexpression span itself. `apply` stays for compound values.
                let bytes = unsafe { resolved.subsexpr().span().as_ref().unwrap() }.to_vec();
                let (exact, mask) = self.ground_probe(f, &bytes);
                if exact {
                    // Ground against ground: the seek established byte equality, and on ground
                    // terms byte equality is unifiability (RoutingSafe.thy,
                    // `ground_unifiable_iff_eq`), so `unify` would return the bindings unchanged.
                    // Bind the column directly; a wildcard candidate still unifies through
                    // `mork_expr::unify` below.
                    self.with_bound_path_bytes(f, &bytes, 0, cont);
                }
                for w in mask.iter() {
                    if is_wildcard_term(w) {
                        self.match_candidate(f, pattern, single_byte(w), Self::wildcard_counts(w), cont);
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
        // One mask read serves both the wildcard candidates and the arity-byte test: the zipper
        // position is the same before and after the wildcard branches (each `match_candidate`
        // restores `bound[f]`), so the mask is unchanged between them.
        let mask = self.cursors[f].floor_child_mask();
        for w in mask.iter() {
            if is_wildcard_term(w) {
                self.match_candidate(f, pattern, single_byte(w), Self::wildcard_counts(w), cont);
            }
        }
        let Some(arity) = resolved.subsexpr().arity() else {
            return;
        };
        let arity_byte = item_byte(Tag::Arity(arity));
        if mask.test_bit(arity_byte) {
            // Derive the children per visit, into a pooled buffer. Precomputing the whole column
            // subtree at plan time was measurably worse once `ExprEnv::args` stopped being
            // quadratic: the walk it saves per candidate is now cheaper than walking every node of
            // the column once per evaluation, even on the compound-heavy counter machine.
            let mut children = self.free_child_bufs.pop().unwrap_or_default();
            children.clear();
            resolved.args(&mut children);
            self.with_bound_path_bytes(f, &[arity_byte], 0, &mut |this| {
                this.match_compound_children(f, &children, 0, cont);
            });
            children.clear();
            self.free_child_bufs.push(children);
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


    /// Before each scheduled variable, walk every factor forward over the seek positions whose
    /// value is already determined: the query's own ground structure (symbols and compound nodes,
    /// at any depth) and variables an earlier level already bound. A factor stops at the first
    /// position holding a variable this level has not reached yet, which is what leaves that
    /// variable available to `recurse_after_catch_up`'s multiway intersection.
    ///
    /// Every determined position can still BRANCH, because a stored data variable at it is a
    /// wildcard that captures whatever the query has there; the step consumers take those branches.
    fn catch_up(&mut self, i: usize, f: usize) {
        if self.stopped {
            return;
        }
        if f == self.factors.len() {
            self.recurse_after_catch_up(i);
            return;
        }
        let Some(step) = self.steps[f].get(self.next_step[f]).copied() else {
            self.catch_up(i, f + 1);
            return;
        };
        if let Step::Var(vp) = step {
            if self.var_pos[vp] >= i {
                // Scheduled at this level or later: leave it for the intersection.
                self.catch_up(i, f + 1);
                return;
            }
        }
        self.consume_step(f, &mut |this| this.catch_up(i, f));
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Body-level adapters the router used to expose. They are pure test conveniences now: the
    /// shipped surface is `parse_body_factors` plus the join entry points, and the engine reaches
    /// the join only through `query_multi_leapfrog`.
    /// Build a factor whose columns are all plain variables, over a borrowed prefix. Only the
    /// tests construct factors by hand; the engine gets them from `parse_body_factors`, which
    /// borrows the body.
    fn var_cols<'a>(prefix: &'a [u8], cols: Vec<usize>) -> Factor<'a> {
        Factor {
            prefix,
            cols: cols.into_iter().map(FactorColumn::Var).collect(),
        }
    }

    fn body_routable(body: &[u8]) -> bool {
        parse_body_factors(&Expr::from_slice(body)).is_some_and(|(factors, _)| !factors.is_empty())
    }

    fn body_partial(
        map: &PathMap<()>,
        body: &[u8],
    ) -> Option<(usize, BTreeSet<Vec<Option<Vec<u8>>>>)> {
        let be = Expr::from_slice(body);
        let (factors, nvars) = parse_body_factors(&be)?;
        if factors.is_empty() {
            return None;
        }
        let var_order: Vec<usize> = (0..nvars).collect();
        Some((nvars, unify_join_zipper_partial(map, &factors, &var_order, nvars)))
    }

    fn body_safe(map: &PathMap<()>, body: &[u8]) -> Option<BTreeSet<Vec<Vec<u8>>>> {
        let (_, rows) = body_partial(map, body)?;
        rows.into_iter()
            .map(|row| {
                row.into_iter()
                    .map(|component| component.filter(|bytes| Expr::from_slice(bytes).variables() == 0))
                    .collect::<Option<Vec<Vec<u8>>>>()
            })
            .collect()
    }

    fn body_rows_rendered(map: &PathMap<()>, body: &[u8]) -> Option<BTreeSet<Vec<u8>>> {
        let be = Expr::from_slice(body);
        let (factors, nvars) = parse_body_factors(&be)?;
        if factors.is_empty() {
            return None;
        }
        let var_order: Vec<usize> = (0..nvars).collect();
        Some(unify_join_zipper_coordinated(map, &factors, &var_order, nvars))
    }

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

        let rows = body_safe(&map, &body).expect("flat body routes");
        let expected = BTreeSet::from([vec![sym("a"), sym("b"), sym("c")]]);
        assert_eq!(rows, expected);
    }

    #[test]
    fn safe_body_routes_single_ground_answer() {
        let mut map = PathMap::<()>::new();
        map.insert(&nest("p", &[sym("a"), sym("b")]), ());
        let body = conj(&[nest("p", &[sym("a"), new_var()])]);

        let rows = body_safe(&map, &body).expect("flat body routes");
        let expected = BTreeSet::from([vec![sym("b")]]);
        assert_eq!(rows, expected);
    }

    #[test]
    fn safe_body_partial_routes_when_all_ground_entry_cannot_represent_rows() {
        let mut map = PathMap::<()>::new();
        map.insert(&nest("r", &[new_var()]), ());
        map.insert(&nest("r", &[nest("a", &[sym("v0")])]), ());
        let body = conj(&[nest("r", &[nest("a", &[new_var()])])]);

        assert!(body_routable(&body));
        let (_nvars, rows) =
            body_partial(&map, &body).expect("partial route is safe");
        assert!(
            rows.iter()
                .any(|row| row.iter().any(|component| component.is_none())),
            "the live renderer must preserve the free non-ground row"
        );
        assert!(
            body_safe(&map, &body).is_none(),
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
        let rows = body_rows_rendered(&coref, &body).expect("flat body routes");
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
            body_rows_rendered(&indep, &body).expect("flat body routes");
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
                body_routable(body),
                "{name} must be inside the zipper-owned route"
            );
            assert!(
                body_partial(map, body).is_some(),
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
        let be = Expr::from_slice(&body);
        let (factors, nvars) = parse_body_factors(&be).expect("body parses");
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
            cur.at_end,
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
                        if unsafe { term.expr.span().as_ref().unwrap() } != &row[ci][..] {
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

    /// Every conjunct shape is a factor. A compound keeps the arity-byte prefix with one column
    /// per argument; a bare symbol, a bare variable, and the empty compound become WHOLE-ATOM
    /// factors -- empty prefix (so the cursor opens at the trie root, where complete facts live)
    /// and the conjunct itself as the single column, `Term` for a constant and `Var` for a
    /// variable, including a `VarRef` back to a variable an earlier conjunct introduced.
    #[test]
    fn non_compound_conjuncts_parse_as_whole_atom_factors() {
        let body = conj(&[
            nest("e", &[new_var(), new_var()]),
            sym("present"),
            var_ref(0),
            new_var(),
            vec![item_byte(Tag::Arity(0))],
        ]);
        let be = Expr::from_slice(&body);
        let (factors, nvars) = parse_body_factors(&be).expect("every conjunct shape must parse");
        assert_eq!(nvars, 3, "the trailing NewVar conjunct introduces a variable");
        assert_eq!(factors.len(), 5);

        assert_eq!(factors[0].prefix, &[item_byte(Tag::Arity(3))]);
        assert_eq!(factors[0].cols.len(), 3, "head plus two argument columns");

        for (i, f) in factors[1..].iter().enumerate() {
            assert!(
                f.prefix.is_empty(),
                "whole-atom factor {i} must open at the trie root"
            );
            assert_eq!(f.cols.len(), 1, "whole-atom factor {i} has one column");
        }
        let FactorColumn::Term(present) = &factors[1].cols[0] else {
            panic!("a bare symbol conjunct is a ground Term column");
        };
        assert_eq!(unsafe { present.expr.span().as_ref().unwrap() }, &sym("present")[..]);
        assert!(present.is_ground());
        assert!(
            matches!(factors[2].cols[0], FactorColumn::Var(0)),
            "a bare VarRef conjunct is the same join variable its introducer named"
        );
        assert!(matches!(factors[3].cols[0], FactorColumn::Var(2)));
        let FactorColumn::Term(nil) = &factors[4].cols[0] else {
            panic!("the empty compound is a ground Term column");
        };
        assert_eq!(unsafe { nil.expr.span().as_ref().unwrap() }, &[item_byte(Tag::Arity(0))]);
    }

    /// `(,)` is a body with no conjunct. It parses to zero factors, which the dispatch reads as
    /// "match once, unconditionally" -- `Space::query_multi`'s own reading of it.
    #[test]
    fn empty_conjunction_parses_to_no_factors() {
        let empty = conj(&[]);
        let be = Expr::from_slice(&empty);
        let (factors, nvars) = parse_body_factors(&be).expect("`(,)` is well formed");
        assert!(factors.is_empty());
        assert_eq!(nvars, 0);
        // A body that is not a conjunction at all is still declined, and is the only thing that is.
        let nb = sym("nope");
        assert!(parse_body_factors(&Expr::from_slice(&nb)).is_none());
        assert!(parse_body_factors(&Expr::from_slice(&[item_byte(Tag::Arity(0))])).is_none());
    }

    /// A constant conjunct is an existence check on that atom, and a fact stored as a bare
    /// VARIABLE is a top-level wildcard that unifies with it. The whole-atom factor's empty prefix
    /// puts the ground path's floor at the ROOT, so its candidates are the exact atom plus every
    /// wildcard byte in the root's child mask -- which is exactly the set of facts that can unify
    /// with the constant. Pin all three cases: atom stored, atom absent but a wildcard present,
    /// and neither.
    #[test]
    fn constant_conjunct_takes_the_exact_atom_and_top_level_wildcards() {
        let edges = |map: &mut PathMap<()>| {
            map.insert(&nest("e", &[sym("a"), sym("b")]), ());
            map.insert(&nest("e", &[sym("b"), sym("c")]), ());
        };
        let body = conj(&[nest("e", &[new_var(), new_var()]), sym("present")]);
        let both = BTreeSet::from([
            vec![sym("a"), sym("b")],
            vec![sym("b"), sym("c")],
        ]);

        let mut stored = PathMap::<()>::new();
        edges(&mut stored);
        stored.insert(&sym("present"), ());
        assert_eq!(body_safe(&stored, &body).unwrap(), both);

        let mut wildcard = PathMap::<()>::new();
        edges(&mut wildcard);
        wildcard.insert(&new_var(), ());
        assert_eq!(
            body_safe(&wildcard, &body).unwrap(),
            both,
            "a fact stored as a bare variable unifies with the constant conjunct"
        );

        let mut absent = PathMap::<()>::new();
        edges(&mut absent);
        assert!(
            body_safe(&absent, &body).unwrap().is_empty(),
            "an absent atom blocks the body"
        );
    }

    /// A bare VARIABLE conjunct matches any atom and binds the variable to it, and the variable is
    /// a first-class join variable: sharing it with a compound conjunct's column restricts both
    /// sides, so `(, (e $x $y) $x)` keeps only the edges whose source is itself a stored atom.
    #[test]
    fn variable_conjunct_is_a_first_class_join_variable() {
        let mut map = PathMap::<()>::new();
        map.insert(&nest("e", &[sym("a"), sym("b")]), ());
        map.insert(&nest("e", &[sym("b"), sym("c")]), ());
        map.insert(&sym("a"), ());
        map.insert(&sym("c"), ());

        let shared = conj(&[nest("e", &[new_var(), new_var()]), var_ref(0)]);
        assert_eq!(
            body_safe(&map, &shared).unwrap(),
            BTreeSet::from([vec![sym("a"), sym("b")]]),
            "only (e a b) has a source that is also a stored atom"
        );

        // Unshared, the conjunct matches ANY atom: the full cross product of the two edges with
        // every one of the four stored facts, compound facts included.
        let free = conj(&[nest("e", &[new_var(), new_var()]), new_var()]);
        let atoms = [
            nest("e", &[sym("a"), sym("b")]),
            nest("e", &[sym("b"), sym("c")]),
            sym("a"),
            sym("c"),
        ];
        let mut want = BTreeSet::new();
        for (x, y) in [(sym("a"), sym("b")), (sym("b"), sym("c"))] {
            for z in &atoms {
                want.insert(vec![x.clone(), y.clone(), z.clone()]);
            }
        }
        assert_eq!(body_safe(&map, &free).unwrap(), want);
    }

    /// The lead's mutual-seek intersection prunes exactly the symbol-headed (hence ground)
    /// candidates, and it may only skip forward over them, so it needs every symbol byte to sort
    /// above every compound and variable byte -- otherwise the leap could jump a compound the
    /// intersection is not allowed to prune. Pin that property of the tag encoding, and pin
    /// `mask_has_wildcard`'s mask test against the variable byte range it stands for.
    #[test]
    fn symbol_terms_sort_above_every_other_tag() {
        use mork_expr::maybe_byte_item;
        for b in 0u8..=255 {
            // Reserved bytes are not a valid encoding and never reach a stored subterm.
            let Ok(tag) = maybe_byte_item(b) else { continue };
            let symbol = matches!(tag, Tag::SymbolSize(_));
            assert_eq!(symbol, is_symbol_head(b), "byte {b}");
            let variable = matches!(tag, Tag::NewVar | Tag::VarRef(_));
            // A single variable byte is a complete subterm; nothing else one byte long is.
            assert_eq!(variable, is_wildcard_term(b), "byte {b}");
            if symbol {
                // Every non-symbol byte is strictly below every symbol byte.
                for c in 0u8..=255 {
                    if matches!(
                        maybe_byte_item(c),
                        Ok(Tag::NewVar | Tag::VarRef(_) | Tag::Arity(_))
                    ) {
                        assert!(c < b, "tag byte {c} must sort below symbol byte {b}");
                    }
                }
            }
            // The mask test sees a variable byte exactly when one is present.
            assert_eq!(mask_has_wildcard(&mask_of(&[b])), variable, "byte {b}");
        }
        assert!(!mask_has_wildcard(&mask_of(&[])));
        assert!(mask_has_wildcard(&mask_of(&[
            item_byte(Tag::Arity(2)),
            item_byte(Tag::NewVar),
            item_byte(Tag::SymbolSize(3)),
        ])));
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
        let mut v = factor.prefix.to_vec();
        for col in &factor.cols {
            match col {
                FactorColumn::Var(id) => v.push(item_byte(Tag::VarRef(*id as u8))),
                FactorColumn::Term(term) => v.extend_from_slice(unsafe { term.expr.span().as_ref().unwrap() }),
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
                    ExprEnv::new(QUERY_NS, Expr::from_slice(q)),
                    ExprEnv::new(1 + i as u8, Expr::from_slice(f)),
                )
            })
            .collect();
        let Ok(bindings) = unify(&mut pairs) else {
            return;
        };
        if fi == query_exprs.len() {
            let mut row = Vec::with_capacity(nvars);
            for v in 0..nvars {
                let mut env =
                    ExprEnv::with_intro(QUERY_NS, v as u8, Expr::from_slice(&NEW_VAR_EXPR_BYTES));
                loop {
                    let Some(var) = env.var_opt() else { break };
                    match bindings.get(&var) {
                        Some(next) => env = *next,
                        None => return, // still free: the all-ground join drops this row
                    }
                }
                let bytes = unsafe { env.subsexpr().span().as_ref().unwrap() }.to_vec();
                if Expr::from_slice(&bytes).variables() != 0 {
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
                    vec![var_cols(&pe, vec![0, 1])],
                    vec![0, 1],
                    2,
                ),
                // path  (e $0 $1)(e $1 $2)
                (
                    vec![
                        var_cols(&pe, vec![0, 1]),
                        var_cols(&pe, vec![1, 2]),
                    ],
                    vec![0, 1, 2],
                    3,
                ),
                // star  (e $0 $1)(e $0 $2)
                (
                    vec![
                        var_cols(&pe, vec![0, 1]),
                        var_cols(&pe, vec![0, 2]),
                    ],
                    vec![0, 1, 2],
                    3,
                ),
                // two-relation path  (e $0 $1)(f $1 $2)
                (
                    vec![
                        var_cols(&pe, vec![0, 1]),
                        var_cols(&pf, vec![1, 2]),
                    ],
                    vec![0, 1, 2],
                    3,
                ),
                // cyclic triangle over schematic edges (the re-index + catch-up path).
                (
                    vec![
                        var_cols(&pe, vec![0, 1]),
                        var_cols(&pe, vec![1, 2]),
                        var_cols(&pe, vec![2, 0]),
                    ],
                    vec![0, 1, 2],
                    3,
                ),
                // cyclic four-cycle over schematic edges.
                (
                    vec![
                        var_cols(&pe, vec![0, 1]),
                        var_cols(&pe, vec![1, 2]),
                        var_cols(&pe, vec![2, 3]),
                        var_cols(&pe, vec![3, 0]),
                    ],
                    vec![0, 1, 2, 3],
                    4,
                ),
                // swap pair  (e $0 $1)(e $1 $0)
                (
                    vec![
                        var_cols(&pe, vec![0, 1]),
                        var_cols(&pe, vec![1, 0]),
                    ],
                    vec![0, 1],
                    2,
                ),
                // intra-factor coreference  (e $0 $0) against schematic facts.
                (vec![var_cols(&pe, vec![0, 0])], vec![0], 1),
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
        let mut ez = ExprZipper::new(term.expr);
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
        let mut v = factor.prefix.to_vec();
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
        cycled: &mut BTreeMap<ExprVar, u8>,
    ) -> Option<Vec<u8>> {
        let mut env =
            ExprEnv::with_intro(QUERY_NS, v as u8, Expr::from_slice(&NEW_VAR_EXPR_BYTES));
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
                    ExprEnv::new(QUERY_NS, Expr::from_slice(q)),
                    ExprEnv::new(1 + i as u8, Expr::from_slice(f)),
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
            // The NAMESPACED shapes: every join variable sits under a wrapper, so no factor has a
            // top-level variable column at all. These are the shapes the flattened seek positions
            // exist for, and they are the ones that would break first if a level ever absorbed the
            // wrapper's structure into a seek prefix instead of branching on the stored wildcard --
            // the generated facts here carry wildcard heads, wildcard columns and compound columns
            // at exactly those positions.
            (
                "namespaced-triangle",
                conj(&[
                    nest("e", &[nest("k", &[new_var()]), nest("k", &[new_var()])]),
                    nest("e", &[nest("k", &[var_ref(1)]), nest("k", &[new_var()])]),
                    nest("h", &[nest("k", &[var_ref(0)]), nest("k", &[var_ref(2)])]),
                ]),
            ),
            (
                "namespaced-deep",
                conj(&[
                    nest("e", &[nest("k", &[nest("k", &[new_var()])]), new_var()]),
                    nest("h", &[nest("k", &[nest("k", &[var_ref(0)])]), var_ref(1)]),
                ]),
            ),
            (
                "namespaced-repeat",
                conj(&[
                    nest("e", &[nest("k", &[new_var()]), nest("k", &[var_ref(0)])]),
                    nest("h", &[nest("k", &[var_ref(0)]), new_var()]),
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
                let be = Expr::from_slice(body);
                let Some((factors, nvars)) = parse_body_factors(&be) else {
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
    /// A variable under a namespace wrapper is its OWN seek position, so it can be scheduled and
    /// intersected across factors. While a "column" meant "a top-level argument",
    /// `(data (e $x $y))` offered no variable column at all: the multiway intersection never
    /// engaged and the wrapper was walked factor-at-a-time, which is the ProductZipper's algorithm
    /// paid for with the join's machinery.
    #[test]
    fn nested_variables_become_seek_positions() {
        let body = conj(&[nest("data", &[nest("e", &[new_var(), new_var()])])]);
        let be = Expr::from_slice(&body);
        let (factors, nvars) = parse_body_factors(&be).expect("body parses");
        assert_eq!(nvars, 2);
        let steps = factor_steps(&factors[0]);
        // The wrapper symbol, the inner compound node, its head symbol, then a position each for
        // `$0` and `$1`. The compound's subtree runs to the end of the factor.
        assert_eq!(steps.len(), 5, "one position per node of the pre-order walk");
        assert!(matches!(steps[0], Step::Sym(..)));
        assert!(matches!(
            steps[1],
            Step::Compound {
                end: 5,
                ..
            }
        ));
        assert!(matches!(steps[2], Step::Sym { .. }));
        assert!(matches!(steps[3], Step::Var(0)));
        assert!(matches!(steps[4], Step::Var(1)));
    }

    /// The trap the flattening must not spring: every level it descends still branches on a stored
    /// wildcard. A fact `(data $w)` whose `$w` captures the whole `(e a b)` unifies with the nested
    /// query, and would vanish the moment the wrapper's structure were absorbed into a seek prefix.
    #[test]
    fn namespaced_query_keeps_wildcard_branches() {
        let mut map = PathMap::<()>::new();
        map.insert(&nest("data", &[nest("e", &[sym("a"), sym("b")])]), ());
        map.insert(&nest("data", &[new_var()]), ());
        let body = conj(&[nest("data", &[nest("e", &[new_var(), new_var()])])]);
        let (nvars, rows) = body_partial(&map, &body).expect("body routes");
        assert_eq!(nvars, 2);
        assert_eq!(
            rows,
            BTreeSet::from([
                vec![Some(sym("a")), Some(sym("b"))],
                vec![None, None],
            ]),
            "the stored wildcard must capture the whole nested subterm"
        );
    }

    /// The namespaced triangle end to end: three conjuncts, every join variable nested, answered
    /// through the multiway intersection over nested positions.
    #[test]
    fn namespaced_triangle_answers() {
        let edge = |a: &str, b: &str| nest("data", &[nest("e", &[sym(a), sym(b)])]);
        let mut map = PathMap::<()>::new();
        for (a, b) in [("a", "b"), ("b", "c"), ("a", "c"), ("c", "a"), ("b", "a")] {
            map.insert(&edge(a, b), ());
        }
        let body = conj(&[
            nest("data", &[nest("e", &[new_var(), new_var()])]),
            nest("data", &[nest("e", &[var_ref(1), new_var()])]),
            nest("data", &[nest("e", &[var_ref(0), var_ref(2)])]),
        ]);
        let rows = body_safe(&map, &body).expect("body routes");
        assert_eq!(
            rows,
            BTreeSet::from([
                vec![sym("a"), sym("b"), sym("c")],
                vec![sym("b"), sym("c"), sym("a")],
                vec![sym("b"), sym("a"), sym("c")],
            ])
        );
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
        let rows1 = body_safe(&m1, &body1).expect("variable head routes");
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
        let rows2 = body_safe(&m2, &body2).expect("ground head routes");
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





    fn pick<'x>(rng: &mut Lcg, xs: &[&'x str]) -> &'x str {
        xs[rng.below(xs.len())]
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
        let be = Expr::from_slice(&body);
        let (factors, nvars) = parse_body_factors(&be).unwrap();
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

}
