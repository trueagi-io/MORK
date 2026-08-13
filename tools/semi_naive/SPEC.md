# Specification: lowering add-only MM2 rules into semi-naive rounds

This document defines the lowering precisely: the accepted input fragment, the
exact statements the lowering emits, the round semantics they implement, the
equivalence theorem that justifies the whole construction, and the conditions
that theorem needs. `transform.py` is the reference implementation of this
specification; `driver.py` is its executable acceptance gate. The
specification is implementation-agnostic: a sink or a compiler pass emitting
the same statements satisfies it identically, and the oracle gates it
unchanged.

## 1. Accepted fragment

A source program is a sequence of top-level expressions, each either a fact or
a rule.

A fact is a list expression whose head is a fixed atom that is not one of the
reserved atoms below. Non-list facts, facts headed by a variable, and facts
headed by a reserved atom are refused.

A rule is a four-field exec statement

```
(exec p (, B1 ... Bk) (, H1 ... Hm))     k >= 1, m >= 1
```

where `p` is a variable-free priority expression, every body factor `Bi` and
every head `Hj` is a list expression headed by a fixed, non-reserved atom, and
every variable occurring in a head also occurs in the body. A rule may
additionally be an exact self-respawn: one body factor is an exec handle that
matches the rule itself, and exactly one emitted head is that same handle,
unchanged. The lowering strips the pair and treats the remainder as the rule;
the generated controller supplies the repetition the self-respawn expressed. A
self-respawn that alters its priority, pattern, or template is refused
(`SELF_MODIFYING_RULE`), and a template emitting any other exec is refused
(`FOREIGN_EXEC_TEMPLATE`).

Reserved atoms: `f`, `d0`, `d1`, `c`, `t`, `s` as relation heads, and `exec`,
`I`, `O` as top-level data. Programs using them where the lowering needs them
fresh are refused. The complete refusal table in README.md is the normative
applicability boundary; everything not accepted by this section is refused
with a named reason and no output.

The source semantics this lowering targets is repeated evaluation: the rules
are treated as persistent and applied to a fixed point, as in Datalog. It does
not model one-shot exec consumption; a rule that should fire once is outside
the fragment.

## 2. The emitted program

Write CUR and NXT for the two delta-parity variables. The lowering emits, in
order:

1. For every source fact `a`: `(f a)`.
2. For every source fact `a`: `(d0 a)`.
3. The initial turn marker: `(t d0 d1)`.
4. One controller statement, defined in section 4, whose template embeds the
   phase statements of section 3.

Phase priorities share the fixed shape `(s PHASE SRC UNIQ)`. `PHASE` is the
round phase, `0` through `4`. `SRC` is the source rule's priority expression,
preserved verbatim, in derive priorities and `0` elsewhere. `UNIQ` is a
tie-breaking atom (the reference implementation uses rule index times 10^6
plus variant index); its only obligation is uniqueness. The encoding relies on
exactly one ordering property: the engine fires all pending phase-`i` execs
before any phase-`j` exec with `i < j`. Order inside one phase is immaterial
to the result, because within a phase all effects are insertions into or
removals from disjoint fact sets (section 5, C4).

## 3. Phase statements

For source rule `r` with priority `p`, factors `B1 ... Bk`, heads
`H1 ... Hm`, and for each variant `j` in `1..k`:

```
(exec (s 0 p UNIQ) (, (f B1) ... (CUR Bj) ... (f Bk)) (, (c H1) ... (c Hm)))
```

Factor order is preserved; factor `j` reads the current delta, every other
factor reads `f`. These are the derive variants: their union over `j` derives
every consequence with at least one premise in the current delta.

The bookkeeping phases, with `$x` a fresh variable:

```
difference   (exec (s 1 0 0) (, (c $x) (f $x)) (O (- (c $x))))
clear delta  (exec (s 2 0 0) (, (CUR $x))      (O (- (CUR $x))))
clear turn   (exec (s 2 0 1) (, (t CUR NXT))   (O (- (t CUR NXT))))
promote      (exec (s 3 0 0) (, (c $x))
               (O (+ (f $x)) (+ (NXT $x)) (+ (t NXT CUR)) (- (c $x))))
```

Difference removes every candidate already known. Promotion moves each
survivor into `f` and into the next delta, re-creates the turn marker with the
parities swapped, and consumes the candidate. Set semantics makes the repeated
`(t NXT CUR)` insertions one fact.

## 4. The controller

Every phase statement above is embedded literally in the controller's
template, with its variables canonicalized into one shared namespace in which
CUR and NXT are the two distinguished parity variables. The controller is

```
(exec (s 4 0 0)
      (, (t CUR NXT) (exec (s 4 0 0) $pat $tpl))
      (, PHASE1 ... PHASEn (exec (s 4 0 0) $pat $tpl)))
```

Its body binds the parities from the live turn marker and binds its own
statement through the generic handle `(exec (s 4 0 0) $pat $tpl)`. Firing it
therefore instantiates and emits every phase exec for one round with the
current parity assignment, plus its own replacement. The replacement fires
after the round's phases. If promotion restored a turn marker, the next round
begins with the parities swapped; if no candidate survived, no turn marker
exists, the replacement matches nothing, is consumed, and the program
quiesces.

Emitted execs are independent facts, so one round's phase statements do not
interfere with the next round's. The canonicalized controller must stay within
MORK's 64-variable form limit; the reference implementation reserves four
variables (two parities, pattern, template) and refuses a source rule needing
more than 60 (`CONTROLLER_VARIABLE_LIMIT`).

## 5. Round semantics and the equivalence theorem

Let `S0` be the source fact set and `T` the immediate-consequence operator of
the rules: `T(S)` is the set of instantiated heads over bindings whose every
factor matches in `S`. The two evaluations are

```
naive        F(0) = S0        F(n+1) = F(n) ∪ T(F(n))
semi-naive   G(0) = S0, D(0) = S0
             C(n+1) = TD(G(n), D(n))          candidates, phase 0
             D(n+1) = C(n+1) \ G(n)           difference,  phase 1
             G(n+1) = G(n) ∪ D(n+1)           promotion,   phase 3
```

where `TD(S, D)` is the union over variants `j` of derivations reading factor
`j` from `D` and every other factor from `S`.

Theorem 1 (round equivalence). For every `n`, `G(n) = F(n)`.

Theorem 2 (quiescence). If `D(n+1)` is empty then `T(F(n)) ⊆ F(n)`: the naive
fixed point is reached, and the controller's stop is exact.

The proof of Theorem 1 is the classical semi-naive argument (Bancilhon 1986;
Bancilhon-Maier-Sagiv-Ullman, PODS 1986) by induction with the invariant that
round `n+1` captures every immediate consequence of `F(n)`. The inclusion
`G(n+1) ⊆ F(n+1)` holds because every delta-restricted derivation is a
derivation. For the converse, take any derivation from `F(n) = G(n) =
G(n-1) ∪ D(n)`. Either every premise lies in `G(n-1)`, in which case the fact
was already captured at round `n`, or some premise lies in `D(n)`, in which
case the variant restricting that factor derives it into `C(n+1)`, and the
difference and promotion phases place it in `G(n+1)` whether or not it was
already known. The base round uses `D(0) = G(0)`, which covers every
derivation only because every rule has at least one body factor; `k >= 1` is
the `EMPTY_RULE_BODY` refusal, not a convention.

The theorem transfers to the emitted program under four conditions, each
pinned by the encoding:

- C1, set semantics: insertion is idempotent, so duplicate candidates and the
  repeated turn-marker insertions collapse. This is MORK's native space
  semantics.
- C2, add-only: no source rule removes facts, so `T` is monotone and the
  accumulation never retracts. Removal templates are refused.
- C3, phase separation: all candidates of a round exist before difference
  runs, difference completes before promotion, and the old delta is cleared
  before the swapped marker exists. The `PHASE` field's dominance in priority
  order is exactly this condition.
- C4, within-phase order freedom: derive variants only insert candidates,
  difference only removes candidates present in `f`, promotion handles each
  candidate independently. All are set operations whose result is independent
  of firing order inside the phase, so the `SRC` and `UNIQ` fields never
  affect the final space.

## 6. Projection and the acceptance gate

The projection of a transformed space is the set of `x` with `(f x)` in the
space; every `d0`, `d1`, `c`, `t` fact and every `(exec (s ...) ...)`
statement is bookkeeping and is erased. Correctness of an implementation of
this specification means: for every accepted program, the sorted projection of
the transformed run at quiescence is byte-identical to the sorted final space
of the source's repeated evaluation, with equal step, unification, and write
counters across engines where those are engine-invariant. `driver.py --all`
checks precisely this over the corpus, the generated workload families, and
the accepted repository programs, under both join engines.

## 7. Non-goals

The lowering does not implement newness detection inside the engine (the
difference phase exists only because insertion does not report it), does not
cover I/O, removal, or counted exec forms, and does not choose whether a
workload benefits: programs reaching their fixed point in one productive
round pay the controller overhead for no saving, as the repository
measurements in README.md show. Those boundaries are deliberate scope, stated
so that an engine-side implementation can widen them knowingly.
