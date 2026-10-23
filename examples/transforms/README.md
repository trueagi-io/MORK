# Semi-join and incrementalization, as source-level MM2 transforms

Both are rewrites of a program into more programs. Neither needs a change to the join. What the
projection cut adds is that the *projections* a semi-join reduction is built out of stop costing
a full pass over the relation.

`generate.py OUTDIR` writes the six measured programs; every measurement below is the query-only
time the CLI reports (`took N ms`), best of three, on the same machine.

## 1. The projection is the shape the cut answers

A semi-join `A ⋉ B` on variable `v` needs `π_v(B)` — in MM2, `(exec _ (, (B $v $_)) (, (Bv $v)))`.
`$_` is mentioned once, no template reads it, and it is the conjunct's last column, so the cut
answers it with one witness per key instead of enumerating every tuple.

| program | leapfrog | ProductZipper |
|---|---|---|
| `proj_keyfirst.mm2` — `(, (S $y $_))` | **0 ms** | **0 ms** |
| `proj_keylast.mm2` — `(, (S $_ $z))` | 22 ms | 26 ms |

80000 tuples over 600 distinct keys. **This is the design rule the transform must follow: emit
reduced relations KEY-FIRST.** With the key last the don't-care is not trailing, the cut correctly
refuses it (pinning `$_` would decide which subtrie `$z` comes from), and the projection pays a
full pass.

## 2. Yannakakis staging

`chain_naive.mm2` joins `(, (R $x $y) (S $y $z) (T $z $w))` directly. `chain_staged.mm2` projects,
semi-joins bottom-up, semi-joins top-down, then joins the reduced relations — nine execs ordered
by `loc`.

| | leapfrog | ProductZipper |
|---|---|---|
| naive chain join | 166 ms | 811 ms |
| Yannakakis staged | 154 ms | **276 ms** |

**2.9× on the ProductZipper, ~1.07× on leapfrog.** On an *acyclic* body leapfrog intersects every
participating factor at each variable, so it is already doing the reduction's work and little is
left to remove. That is a property of acyclic bodies only -- see §5, where the same decomposition
is worth 25x to leapfrog on a cyclic one.

## 3. Incrementalization

`tc_naive.mm2` re-joins the whole `path` relation with `edge` on every iteration.
`tc_delta.mm2` joins only the frontier the previous iteration produced — the wiki's own
generation-labelled idiom, which is semi-naive evaluation written by hand.

| chain of 220 nodes, closure = 24090 pairs | leapfrog | ProductZipper |
|---|---|---|
| naive fixpoint | 19565 ms | 24381 ms |
| semi-naive | **150 ms** | **208 ms** |
| | **130×** | **117×** |

Identical closures on both engines. This one needs no engine support at all: per-iteration work
falls from `O(|path|)` to `O(|Δ|)`, and the two are quadratically apart on a chain.

## 4. Composing them

The two compose and stay correct, but an *inline* semi-join conjunct buys nothing:

| 120 chain nodes × 12 dead-end leaves each | leapfrog | ProductZipper |
|---|---|---|
| semi-naive | 348 ms | 504 ms |
| semi-naive + inline `(esrc $y)` guard | 350 ms | 519 ms |

Both engines already intersect at the shared variable, so the extra conjunct re-derives a
restriction they were performing anyway and costs a third factor to intersect. A reduction only
pays when it is **materialised into an earlier stage**, removing tuples before a later and more
expensive one — which is what §2 does and what §4 does not.

## Two MM2 gotchas these programs ran into

**Loc ordering.** Execs run in byte order of the whole atom, and a *symbol* loc sorts above a
*compound* one: `(exec (2 0) ..)` runs AFTER `(exec (2 (1 Z)) ..)`. Mixing the two shapes inverts
the intended staging — a seed written `(exec (2 0) ..)` fires after the loop that consumes it, so
the loop sees an empty relation and dies silently.

**Self-reproducing execs never stop.** A rule that re-adds itself has no termination condition of
its own, so it monopolises every remaining step and any family ordered after it never runs. Bound
it with Peano fuel consumed through an `O`-form `(+ (fuel $k)) (- (fuel (S $k)))`, as the
Reachability-P2 tutorial does.

`differential/corpus/programs/transform_staging.mm2` carries both transforms at a size the
differential runs on every build, computing each one BOTH ways in a single program so its expected
space pins the staged form equal to the form it replaces.

## 5. Decomposition on a CYCLIC body — where leapfrog does gain

`cyc_naive.mm2` asks for 6-cycles directly. `cyc_staged.mm2` splits the cycle into two bags of
three edges — a generalized hypertree decomposition of width 2, against the query's fractional
edge cover number of 3 — materialising the first bag as its projected endpoints.

| 900 edges, 70 nodes | leapfrog | ProductZipper |
|---|---|---|
| naive 6-cycle join | 5951 ms | 11419 ms |
| two bags, endpoints materialised | **237 ms** | **425 ms** |
| | **25×** | **27×** |

Identical answers. The mechanism is visible in the data: the graph holds 149611 three-paths but
only 4900 distinct endpoint pairs, a 30.5x sharing factor, of which the staging realises 25x. A
worst-case-optimal join re-derives the entire suffix for **every** binding of the variables the
decomposition projects away; materialising the bag pays for the suffix once per distinct endpoint
pair. So the earlier claim that leapfrog is already doing Yannakakis' work holds for acyclic
bodies and does not generalise: on cyclic ones the decomposition is a large win for leapfrog too.

## 6. Incrementalizing the process calculus

The benchmark's communication rule is a self-join on the soup keyed by channel:
`(, (petri (? $c $pl $b)) (petri (! $c $pl))) -> (petri $b)`. It is MONOTONE -- nothing is
removed -- so every past communication is re-derived on every activation, and the cost of a
cascade of length N is quadratic in N.

`pc3_delta.mm2` joins only the messages the previous round produced, with promotion folded into
the rule itself (a separate promotion exec would be starved: this family re-adds itself and sorts
first, so it consumes all the fuel before the promoter ever runs).

`pc3_consume.mm2` instead retires the reagents -- `(- (petri (? ...))) (- (petri (! ...)))` --
which is the faithful reading of a communication and removes the re-derivation at its source
rather than filtering it afterwards.

| chain length | naive | delta | | consuming | |
|---|---|---|---|---|---|
| 200 | 250 ms | 37 ms | 6.8× | 27 ms | 9.3× |
| 400 | 1391 ms | 129 ms | 10.8× | 87 ms | 16.0× |
| 800 | 9452 ms | 479 ms | 19.7× | 313 ms | 30.2× |

All three derive the final message. The ratio roughly doubles as the chain doubles, which is the
signature of removing a quadratic: the uplift is not a constant and has no ceiling.

Consuming beats the delta at every size and leaves a soup of ONE atom against 801, because the
delta still keeps every intermediate and merely avoids re-joining it, while consuming never keeps
one. Where the intermediates are not wanted, that is the transform to reach for.

An earlier version of this section reported ~1.1x. That measurement ran 30 rounds of fuel over a
4000-receiver chain -- under one percent of the cascade -- so the quadratic never developed and
the number was an artifact of the harness, not a property of the transform. The shipped
`process_calculus_bench` rule is monotone in exactly this way, so it is paying the same quadratic.

## 7. Sweep over main.rs and the wiki

Every MM2 program in `kernel/src/main.rs`, `kernel/resources/` and the wiki was inventoried for
the two transforms. Applicability turns on three properties of a rule body: whether it is
ITERATIVE (a self-reproducing exec, so incrementalization applies), whether it is CYCLIC and
PROJECTS variables away (so a decomposition can share the suffix), and whether the relation being
ENUMERATED is the one that grows.

`bench_pairs.py DIR STEPS PREFIXES` measures every `X_naive.mm2` against its `X_<variant>.mm2`
in DIR on both engines and checks the answer spaces agree.

| example | taken from | transform | leapfrog | ProductZipper |
|---|---|---|---|---|
| `tc` | Reachability P1/P3 shape | incrementalization | **130×** | **117×** |
| `cyc` | cyclic body, ghw 2 < ρ* 3 | GHD decomposition | **25.4×** | **27.1×** |
| `craft` | wiki Reachability-P2 `exec (1 3)` | semi-join reduction | **8.5×** | **15.6×** |
| `chain` | acyclic 3-relation join | Yannakakis staging | 1.07× | **2.9×** |
| `lts` | taxi_lts / tile_puzzle / CTL shape | worklist delta | 1.8× | 1.8× |
| `clq` | `bench_clique_no_unify` | triangle staging | 0.9× | **6.9×** |
| `pc2` | `process_calculus_bench` | delta | 1.1× | — |

What separates the top of that table from the bottom is projection, not cyclicity. `cyc` and
`craft` both discard almost every body variable, so materialising a bag pays for the shared
suffix once instead of once per discarded binding. `clq` is just as cyclic but names every
variable in its template, so leapfrog has nothing to share and only the ProductZipper -- which
has no per-level intersection at all -- gains. `lts` and `pc2` grow the relation the join
PROBES rather than the one it ENUMERATES, so a delta barely helps; `tc` grows the enumerated one
quadratically, which is the whole 130×.

Programs that the sweep found and did NOT translate, with the reason: `bench_logic_query`,
`bench_finite_domain`, `pattern_mining`, `bench_lr`, `grounding`, `string_convert` and the
`Sources-and-Sinks` examples are single-shot and non-iterative with nothing projected away;
`decision_tree_learning`, `hexlife` and `ip_sudoku` are driven by aggregating sinks, which the
projection cut may not touch at all (see the sink note in space.rs); `bfc`, `ctl` and the
backward-chaining family are iterative but their rules are generated per-step by meta-execs, so
a delta rewrite has to be applied to the generator rather than the rule and is a larger change
than this file demonstrates.
