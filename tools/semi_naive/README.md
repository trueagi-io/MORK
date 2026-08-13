# MM2-native semi-naive evaluation

A source-to-source transform that turns add-only MM2 rule programs into
MM2-native semi-naive loops, plus the oracle, corpus, generators, and
benchmarks that prove the transformed program equivalent and measure what the
transform saves. No engine code changes: everything here is Python over the
`mork` CLI, standard library only.

Naive repeated evaluation re-derives the whole closure every round. Semi-naive
evaluation restricts each rule application to the facts derived in the previous
round, so every derivation is touched once. The transform expresses that
discipline entirely with existing MM2 machinery: wrapper relations, `O` sinks
for removal, priorities for phase order, and a self-respawning controller for
round choreography. `SPEC.md` is the normative specification of the lowering:
the accepted fragment, the exact emitted statements, and the equivalence
theorem with its conditions. `NOTES.md` holds the executable probes that pin
each piece of kernel semantics the encoding relies on, and the design
decisions built on them.

## Running it

```sh
# transform one program
python3 tools/semi_naive/transform.py source.mm2 transformed.mm2

# build both engines and put them where the tools look by default
cargo build --release -p mork                     && cp target/release/mork target/semi_naive/bin-pz
cargo build --release -p mork --features leapfrog && cp target/release/mork target/semi_naive/bin-lf

# the complete oracle: checked corpus + generated workloads + repository
# programs, each run as source and as transform under both engines
python3 tools/semi_naive/driver.py --all --generate \
  --suite existing --suite repository \
  --binary target/semi_naive/bin-pz --binary target/semi_naive/bin-lf

# unit tests (transform, driver, generators, bench, analyzer, acceptance sweep)
python3 -m unittest discover -s tools/semi_naive
```

With one `--binary`, the driver checks every case against its checked
expectations on that engine alone. With two, it additionally requires
byte-identical projections and equal steps, unifications, writes, and source
rounds across engines. The current gate is `40 cases, 0 failed`: 17 corpus and
generated cases plus the 23 repository programs the transform accepts.

`bench.py` measures the four-quadrant Cartesian product of protocol and engine,
`repository_bench.py` measures the accepted repository programs, and
`analyze.py` validates a complete benchmark matrix before fitting scaling
exponents. Each records exact counters and rejects any cross-repeat or
cross-engine drift in them.

## The encoding

For source facts `fact` and add-only rules `(exec p (, B1 ... Bk) (, H1 ... Hm))`:

1. Seed `(f fact)` and `(d0 fact)` for every source fact, then add `(t d0 d1)`.
2. The controller binds `CURRENT` and `NEXT` from `t` and emits one derive
   variant per body factor of every rule. Exactly one factor reads
   `(CURRENT fact)`; the others read `f`. Heads become candidates `(c H)`.
3. Difference: remove `(c fact)` whenever `(f fact)` already exists.
4. Clear: remove the old `CURRENT` facts and the round's `t` marker.
5. Promote: write each surviving candidate to `f` and `NEXT`, emit
   `(t NEXT CURRENT)`, and remove the candidate.
6. The controller respawns only when promotion restored `t`, so a round that
   promotes nothing quiesces.

The alternating `d0`/`d1` role swap is the MM2 rendering of the semi-naive
table update in Datalog engines (merge new into full, swap delta and new,
clear new; see Soufflé's
[`UnitTranslator.cpp`](https://github.com/souffle-lang/souffle/blob/a1303be3c0166400dee3d1f36f0d96abe03e6901/src/ast2ram/seminaive/UnitTranslator.cpp#L514-L532)).
MM2 has no constant-time relation swap, so the roles alternate instead.

Projection erases the bookkeeping (`f`, `d0`, `d1`, `c`, `t`, controller and
phase execs) and recovers the source space. The oracle sorts both spaces and
compares bytes.

The oracle models source `exec` statements as persistent rules evaluated to a
fixed point, which is the repeated-evaluation discipline the transform targets;
it is not upstream's one-shot `exec` consumption. An exactly self-respawning
rule (its own `exec` handle in body and template, unchanged) is accepted by
stripping the handle; the generated controller supplies the repetition.

## What it refuses

The transform either emits the complete supported translation or exits 2 with
`REFUSE REASON`, never a partial output. The boundary, each row covered by a
checked refusal case:

| Reason | Rejected input |
| :--- | :--- |
| `REMOVAL_TEMPLATE` | Source `O` template containing `(- ...)` |
| `IO_SOURCE` | `I` rule body |
| `IO_SINK` | Source `O` template without a removal |
| `COUNTED_EXEC_HEAD` | `exec` with an extra count or template field |
| `MALFORMED_EXEC` | `exec` missing priority, body, or head |
| `UNCLASSIFIABLE_PATTERN` | Non-list body factor, unsupported variable-headed relation, or reserved relation |
| `UNCLASSIFIABLE_TEMPLATE` | Non-list, dynamic, or reserved head relation |
| `SELF_MODIFYING_RULE` | A self-respawn changes its priority, pattern, or template |
| `FOREIGN_EXEC_TEMPLATE` | A template emits an `exec` other than its exact self-respawn handle |
| `VARIABLE_SOURCE_PRIORITY` | Source priority containing a variable |
| `EMPTY_RULE_BODY` | Comma body without factors |
| `EMPTY_RULE_HEAD` | Comma head without templates |
| `UNBOUND_HEAD_VARIABLE` | Head variable absent from the rule body |
| `TOO_MANY_VARIABLES` | Fact or rule exceeding MORK's 64-variable form limit |
| `CONTROLLER_VARIABLE_LIMIT` | Rule needing more than 60 source variables plus the controller's four bindings |
| `UNCLASSIFIABLE_FACT` | Top-level source value that is not a fixed-head relation |
| `RESERVED_SOURCE_FORM` | Top-level `exec`, `I`, or `O` used as data |
| `NO_RULES` | Program without a transformable rule |
| `PARSE_ERROR` | Malformed S-expression input |

Sweeping `kernel/resources/*.mm2` and `differential/corpus/**/*.mm2` (103
programs) accepts 23: `string_convert`, `transitive`, `cross_join_dict`,
`cross_join_tuple`, `lens_aunt`, `lens_composition`, `pattern_mining`,
`stv_roman`, `coref_absorbed_by_data_varref`, `func_type_unification`,
`two_bipolar_equal_crossed`, and twelve of the wiki examples: `mm2_basics_02`,
`mm2_basics_05`, and the reachability programs `p1_13`, `p2_06`, `p2_07`,
`p2_08`, `p3_03`, `p3_04`, `p3_09`, `p3_12`, `p3_18`, and `p4_03`.
`test_acceptance_sweep.py` pins the exact classification of all 103. The
refusals are dominated by rules that respawn modified copies of themselves or
emit other rules, which is control transfer the round controller cannot
absorb yet. Several accepted wiki snippets carry rules without data, so their
persistent fixpoint is empty; they still gate bookkeeping erasure and
first-round quiescence, an edge class the corpus previously lacked.

## What it saves, measured

All comparisons are deterministic engine counters from `mork run`; both arms
produce byte-identical sorted projections at every size, and process-calculus
cases additionally pin the required `(petri (! result ...))` fact. The source
arm is the materialized repeated-evaluation schedule; the transformed arm is
one run to quiescence.

Process calculus (the shape of MORK's process-calculus benchmark, with the
same rule and data shape as persistent rules):

| Operands | Naive unifications | Transformed unifications | Reduction |
| :--- | ---: | ---: | ---: |
| 80 + 80 | 23,002 | 1,371 | 16.8x |
| 160 + 160 | 90,802 | 2,731 | 33.2x |
| 320 + 320 | 360,802 | 5,451 | 66.2x |
| 480 + 480 | 810,002 | 8,171 | 99.1x |

Transitive closure over chain graphs:

| Edges | Naive unifications | Transformed unifications | Reduction |
| ---: | ---: | ---: | ---: |
| 64 | 93,591 | 57,329 | 1.63x |
| 128 | 748,919 | 435,763 | 1.72x |
| 256 | 5,991,735 | 3,392,053 | 1.77x |
| 384 | 24,166,967 | 11,203,319 | 2.16x |

The reduction grows with size on both families because the naive protocol
re-derives every earlier round's results each round. The savings are
shape-dependent: repository programs that reach their fixed point in one
productive round have nothing for semi-naive evaluation to remove, and the
generated controller adds counters instead (`repository_bench.py` labels
twenty-one of the twenty-three accepted programs neutral-short, the small
transitive resource an overhead case, and the step-bounded `lens_aunt` a
bounded-source case). The transform pays on multi-round recursive workloads.

### Four-quadrant timing

Engine milliseconds are the minimum of three interleaved repeats, secondary to
the counters above. Naive cells sum one external process per round, so their
protocol wall also carries process spawn and file round-tripping; transformed
cells are one process. Measured on one shared machine:

| Instance | Naive PZ | Naive LF | Transformed PZ | Transformed LF |
| :--- | ---: | ---: | ---: | ---: |
| PC 80+80 | 1,432 | 538 | 380 | 68 |
| PC 160+160 | 11,262 | 4,224 | 2,667 | 221 |
| PC 320+320 | 88,800 | 32,601 | 19,590 | 836 |
| PC 480+480 | 303,952 | 109,279 | 66,132 | 1,872 |
| Transitive 64 | 60 | 30 | 46 | 27 |
| Transitive 128 | 499 | 240 | 347 | 180 |
| Transitive 256 | 3,721 | 1,726 | 2,432 | 1,260 |
| Transitive 384 | 15,136 | 7,355 | 8,129 | 4,332 |

The two optimizations act on separate costs and compose: semi-naive evaluation
removes cross-round re-derivation, and the leapfrog join removes per-candidate
byte re-walks inside each round's phase joins. At 320 + 320 the composed path
(naive ProductZipper to transformed leapfrog) is 88.8 s to 0.84 s on engine
timers; the transform alone on ProductZipper is 4.5x, and the transform alone
on leapfrog is 39.0x. At 480 + 480 the composed path is 304.0 s to 1.87 s.

Over the full 80-to-480 matrix, transformed leapfrog transitions fit a log-log
exponent of 1.985 (R^2 0.999997) against a projection-byte exponent of 1.985:
the combined evaluator's work grows at the same rate as the serialized output
it must produce, which has an n^2 floor because the result holds order-n facts
whose Peano terms are order-n bytes. Transformed ProductZipper transitions fit
exponent 2.914 on the same runs. On the transitive family the leapfrog
exponent is 2.023 against a byte exponent of 1.993. `analyze.py` recomputes
these fits from the benchmark JSON artifacts and revalidates every projection
before fitting.

## Notes for the engine

Two engine-side observations from building this, recorded here because the
transform deliberately changes no engine code:

- An insertion sink that reports whether it added a new fact would delete the
  entire difference phase: newness is the only thing the `(c fact)` round-trip
  computes.
- `transform_multi_multi_o` reserves a `1 << 32` byte buffer for each `O`
  firing (`kernel/src/space.rs`), which bounds how cheap a bookkeeping-only
  firing can be.
