use vstd::prelude::*;

verus! {

// The interpreted matcher (`coreferential_transition`) re-checks a repeated
// variable (a `VarRef`) by re-matching the data subterm bound at the variable's
// first occurrence against the data at the current position. The optimization
// replaces that recursive structural re-match with a byte comparison
// (`descend_to_existing` over the bound term's bytes), which is what WAM's
// `unify_value` does for an already-bound variable in read mode.
//
// This proves the EXACT precondition under which the byte comparison is a sound
// AND complete substitute for the structural re-match, and exhibits the witness
// that breaks it otherwise. Empirically the `is_ground(bound)` gate alone was
// insufficient (the `counter_machine` benchmark failed): this proof shows why,
// completeness also requires the matched DATA position to be ground.
//
// A term is a symbol, a variable, or a compound of sub-terms. `Var` models a
// variable occurring in the matched DATA (a wildcard that structurally matches
// anything); the bound value we re-check is always ground.

pub enum Term {
    Sym(nat),
    Var,
    Cmp(Seq<Term>),
}

// `ground(t)`: no `Var` occurs anywhere in `t`. The compound case recurses into
// each child via a quantifier, so `decreases t` (each `ts[i]` is structurally
// smaller than `Cmp(ts)`) is the only measure needed, with no seq helper.
pub open spec fn ground(t: Term) -> bool
    decreases t,
{
    match t {
        Term::Sym(_) => true,
        Term::Var => false,
        Term::Cmp(ts) => forall|i: int| 0 <= i < ts.len() ==> ground(#[trigger] ts[i]),
    }
}

// `unifies(g, d)`: the structural re-match the original matcher performs, the
// bound value `g` against the data `d`. A data `Var` matches any `g` (a
// wildcard); otherwise the shapes must agree and children match pairwise.
pub open spec fn unifies(g: Term, d: Term) -> bool
    decreases d,
{
    match d {
        Term::Var => true,
        Term::Sym(b) => match g {
            Term::Sym(a) => a == b,
            _ => false,
        },
        Term::Cmp(ds) => match g {
            Term::Cmp(gs) => gs.len() == ds.len() && forall|i: int|
                0 <= i < ds.len() ==> unifies(gs[i], #[trigger] ds[i]),
            _ => false,
        },
    }
}

// The byte comparison the fast path performs is exactly term equality `g == d`
// for ground terms: MORK's prefix byte encoding is injective on ground terms, so
// `descend_to_existing` over `g`'s bytes succeeds against `d` iff `g == d`.
//
// THEOREM 1 (the gate is two-sided groundness): when both `g` and `d` are
// ground, the structural re-match agrees with the byte comparison. So with
// ground data the fast path is exactly correct.
pub proof fn ground_match_is_equality(g: Term, d: Term)
    requires
        ground(g),
        ground(d),
    ensures
        unifies(g, d) <==> g == d,
    decreases d,
{
    match d {
        Term::Var => {},
        Term::Sym(_b) => {},
        Term::Cmp(ds) => {
            match g {
                Term::Var => {},
                Term::Sym(_a) => {},
                Term::Cmp(gs) => {
                    if gs.len() != ds.len() {
                        // The length check makes `unifies` false, and unequal
                        // lengths make the terms unequal: both sides false.
                        assert(!unifies(g, d));
                        assert(gs != ds);
                        assert(g != d);
                    } else {
                        // Lengths agree: each child is in range and ground, so the
                        // induction hypothesis gives the per-child equivalence.
                        assert forall|i: int| 0 <= i < ds.len() implies (unifies(gs[i], ds[i])
                            <==> gs[i] == ds[i]) by {
                            assert(ground(gs[i]));
                            assert(ground(ds[i]));
                            ground_match_is_equality(gs[i], ds[i]);
                        }
                        if unifies(g, d) {
                            assert(gs =~= ds);
                        }
                    }
                },
            }
        },
    }
}

// THEOREM 2 (soundness is unconditional on the data): a successful byte
// comparison (`g == d`, ground `g`) always implies a structural match, for any
// `d`. So the fast path never produces a WRONG match; it can only MISS matches.
pub proof fn byte_equal_is_sound(g: Term, d: Term)
    requires
        g == d,
        ground(g),
    ensures
        unifies(g, d),
    decreases d,
{
    match d {
        Term::Var => {},
        Term::Sym(_b) => {},
        Term::Cmp(ds) => {
            let gs = ds;
            assert forall|i: int| 0 <= i < ds.len() implies unifies(gs[i], ds[i]) by {
                if 0 <= i < ds.len() {
                    assert(ground(ds[i]));
                    byte_equal_is_sound(gs[i], ds[i]);
                }
            }
        },
    }
}

// THEOREM 3 (the incompleteness witness = the counter_machine failure mode):
// when the DATA is NOT ground, a structural match can hold while the byte
// comparison fails, so the fast path is INCOMPLETE. Hence the safe gate must
// require the matched data position to be ground, not just the bound value.
pub proof fn nonground_data_breaks_byte_check()
    ensures
        exists|g: Term, d: Term|
            ground(g) && !ground(d) && #[trigger] unifies(g, d) && g != d,
{
    assert(ground(Term::Sym(0)));
    assert(!ground(Term::Var));
    assert(unifies(Term::Sym(0), Term::Var));
    assert(Term::Sym(0) != Term::Var);
    assert(ground(Term::Sym(0)) && !ground(Term::Var) && unifies(Term::Sym(0), Term::Var)
        && Term::Sym(0) != Term::Var);
}

} // verus!

fn main() {}
