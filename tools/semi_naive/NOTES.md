# MM2 semi-naive encoding notes

Every semantic decision in the transform is pinned by an executable probe in
`corpus/i0/` and `corpus/i4/`, run against the release binary built from this
tree with `cargo +nightly build --release -p mork --bin mork`. `./target/release/mork test`
exited 0 before the probes ran. Each command below used `--instrumentation 0` and wrote
the final space under `target/semi_naive/`. The checked result for each probe is stored
under `expected/i0/` and `expected/i4/`.

## Removal and addition sinks

Command:

```text
./target/release/mork run tools/semi_naive/corpus/i0/remove_sink.mm2 --instrumentation 0 target/semi_naive/i0/remove_sink.space
```

Exact stdout:

```text
loaded "tools/semi_naive/corpus/i0/remove_sink.mm2" ; running and outputing to Some("target/semi_naive/i0/remove_sink.space")
executing 1 steps took 0 ms (unifications 1, writes 2, transitions 4, max unify 2)
```

Exact final space:

```text
(removed a)
(survivor b)
```

Decision: inside an `O` template, `(- pattern)` removes the instantiated pattern and `(+ pattern)` adds it. The transform uses these sinks for destructive bookkeeping transitions.

## Bare whole-fact match

Command:

```text
./target/release/mork run tools/semi_naive/corpus/i0/bare_whole_fact.mm2 --instrumentation 0 target/semi_naive/i0/bare_whole_fact.space
```

Exact stdout:

```text
loaded "tools/semi_naive/corpus/i0/bare_whole_fact.mm2" ; running and outputing to Some("target/semi_naive/i0/bare_whole_fact.space")
executing 1 steps took 0 ms (unifications 1, writes 2, transitions 14, max unify 3)
```

Exact final space:

```text
(cand (fact absent))
(fact present)
(bare-hit (fact present))
```

The bound bare conjunct `$x` matched the complete `(fact present)` value and did not match the absent value.

## Wrapped whole-fact match

Command:

```text
./target/release/mork run tools/semi_naive/corpus/i0/wrapped_whole_fact.mm2 --instrumentation 0 target/semi_naive/i0/wrapped_whole_fact.space
```

Exact stdout:

```text
loaded "tools/semi_naive/corpus/i0/wrapped_whole_fact.mm2" ; running and outputing to Some("target/semi_naive/i0/wrapped_whole_fact.space")
executing 1 steps took 0 ms (unifications 1, writes 2, transitions 18, max unify 4)
```

Exact final space:

```text
(f (fact present))
(cand (fact absent))
(wrapped-hit (fact present))
```

Decision: both tested forms work, but the transform uses `(f fact)` for every source fact and `(f $x)` for existence checks. The fixed outer relation gives every whole-fact query a non-variable prefix and makes projection explicit.

## Priority order

Command:

```text
./target/release/mork run tools/semi_naive/corpus/i0/priority_order.mm2 --instrumentation 0 target/semi_naive/i0/priority_order.space
```

Exact stdout:

```text
loaded "tools/semi_naive/corpus/i0/priority_order.mm2" ; running and outputing to Some("target/semi_naive/i0/priority_order.space")
executing 2 steps took 0 ms (unifications 1, writes 2, transitions 4, max unify 1)
```

Exact final space:

```text
(fired priority-0)
```

Decision: priority `0` fires before priority `1`. Priority 0 removed the shared token, so priority 1 observed no match. The phase encoding uses a common structured prefix followed by ordered numeric phase fields.

## Conditional respawn and quiescence

Command:

```text
./target/release/mork run tools/semi_naive/corpus/i0/conditional_respawn.mm2 --instrumentation 0 target/semi_naive/i0/conditional_respawn.space
```

Exact stdout:

```text
loaded "tools/semi_naive/corpus/i0/conditional_respawn.mm2" ; running and outputing to Some("target/semi_naive/i0/conditional_respawn.space")
executing 3 steps took 0 ms (unifications 2, writes 4, transitions 56, max unify 8)
```

Exact final space:

```text
(cleared item)
(worker (, (dc $a)) (O (- (dc $a)) (+ (cleared $a))))
(controller (, (dc $a) (worker $b $c) (controller $d $e)) (, (exec 0 $b $c) (exec 1 $d $e)))
```

The initial controller emitted a priority-0 worker and a priority-1 copy of itself. The worker removed the only `dc` fact. The copied controller was then consumed, found no `dc`, emitted nothing, and execution stopped after three steps.

Decision: controller and worker definitions remain ordinary facts. A controller matches the current delta before it emits the next phase execs and its own replacement. An empty current delta therefore consumes the last controller without respawning it.

## Direct phase emission

The transform embeds every phase `exec` directly in the controller template instead of storing phase definitions as facts. Stored `(phase ...)` definition facts would make the controller match once per phase in every round. The probe deliberately reuses `$x` across two embedded phase statements. Command:

```text
./target/release/mork run tools/semi_naive/corpus/i4/direct_controller.mm2 --instrumentation 0 target/semi_naive/i4/direct_controller.space
```

Exact stdout:

```text
loaded "tools/semi_naive/corpus/i4/direct_controller.mm2" ; running and outputing to Some("target/semi_naive/i4/direct_controller.space")
executing 5 steps took 0 ms (unifications 4, writes 7, transitions 73, max unify 4)
```

Exact final space:

```text
(left a)
(seed a)
(right a)
```

Decision: embed phase statements directly. The probe shows that the two emitted statements remain independently matchable even when their schematic variables originated under one controller template. MORK normalizes each emitted `exec` as an independent fact. The transform canonicalizes each embedded phase into one reusable variable namespace, leaving four variables for the controller's parity, body, and template bindings. A source rule needing more than 60 variables therefore hard-errors as `CONTROLLER_VARIABLE_LIMIT` before the complete controller could exceed MORK's 64-variable form limit.

## Alternating delta buffers

Datalog engines implement the semi-naive table update as merge `new` into the full relation, swap `delta` and `new`, and clear `new`; the relevant Soufflé sequence is in [`UnitTranslator.cpp`](https://github.com/souffle-lang/souffle/blob/a1303be3c0166400dee3d1f36f0d96abe03e6901/src/ast2ram/seminaive/UnitTranslator.cpp#L514-L532). MM2 has no constant-time relation swap, so the transform alternates the roles of two delta relations instead.

The transform wraps full facts as `(f fact)`, seeds `(d0 fact)`, and starts with `(t d0 d1)`. The controller binds the current and next delta relation names from `t`. Each derive variant reads one factor from the bound current relation and its remaining factors from `f`. Difference removes `(c fact)` values already present in `f`. The clear phase removes the current delta and `t`. Promotion writes each surviving candidate directly to `f` and the bound next relation, emits `(t NEXT CURRENT)`, and removes the candidate. A round without a promoted candidate leaves no `t`, so the replacement controller quiesces.

The tags are `f`, `d0`, `d1`, `c`, `t`, and priority prefix `s`. An earlier encoding kept fixed `dc`/`dn` relations and an advance phase that removed every `dn` fact and reinserted it as `dc`; the role swap deletes that phase, one executed step per round, and two writes per promoted delta fact. Under the fixed-role encoding the transformed 320 + 320 process-calculus run took 8,659 steps, 6,732 unifications, and 19,872 writes; the alternating encoding takes 7,697 steps, 5,451 unifications, and 16,348 writes on identical projections. No counter increased on any measured workload.

Source priorities remain the second field in derive priorities, so source rule order is preserved inside the derive phase, and a monotonically assigned variant number breaks ties across rules. MORK's set insertion makes duplicate candidates idempotent, while the explicit difference phase determines newness before promotion.

## Oracle source model

`driver.py` treats the source `exec` statements as persistent Datalog rules. A pilot reinserts the original rules until two consecutive sorted spaces match. The measured source arm then materializes that many rounds with ordered `(naive round source-priority rule-index)` priorities and runs the materialized program once. Pilot counters are discarded. The reported source counters therefore come from one native `mork run`, as do the transformed counters.

An exactly self-respawning source rule (one body `exec` handle matching the live rule, one identical emitted handle) instead runs naturally for the step bound recorded in its manifest row, and its comparison projection drops only the remaining live `exec`. A changed self handle refuses as `SELF_MODIFYING_RULE`; a distinct emitted rule refuses as `FOREIGN_EXEC_TEMPLATE`.

The driver refuses a transformed program containing a bare top-level variable fact with `BARE_TOP_LEVEL_VARIABLE_FACT`, and a unit test regenerates every checked transform and requires exact byte equality with the checked artifact plus the absence of that divergence-class form.

## Combined ProductZipper and leapfrog oracle

`driver.py` accepts one or two `--binary` options under `--all`. One option runs the complete oracle through the selected executable. Two options run every case through both executables, compare each source and transformed projection across engines, and require equal steps, unifications, writes, and source rounds. Transitions and engine milliseconds are reported but are not compared, and the leapfrog output's trailing `max unify` counter is accepted without changing the five canonical metrics. ProductZipper source transitions are nonzero while leapfrog source transitions are zero, which confirms that transitions describe the selected engine rather than a cross-engine semantic invariant.

The one repository case with an engine-specific unification counter is `programs/lens_aunt`: its nine-factor join routes to the leapfrog join under the `leapfrog` feature, so the number of unification attempts is a property of the engine, not the program. Steps, writes, and projections still agree across engines, and each engine's counters are deterministic across repeats.

## Four-quadrant benchmark runner

`bench.py` measures the Cartesian product of the naive repeated-evaluation protocol and the transformed single run with ProductZipper and leapfrog. Its default cases are process-calculus 80+80, 160+160, 320+320, and 480+480, plus transitive chains 64, 128, 256, and 384.

For every repeat, the naive cell starts from the source program, runs one external `mork` process per round, appends the original persistent rules to the preceding output space, and stops when two consecutive sorted projections match. Its engine milliseconds and counters are sums over those processes. Its wall timer includes spawning, loading, dumping, projecting, and re-appending. The transformed cell is one `mork run` to quiescence.

The four cells rotate their starting position across three interleaved repeats. Steps, unifications, writes, transitions, and rounds must match exactly across repeats. Source/transformed and ProductZipper/leapfrog projections must be byte-identical. Steps, unifications, writes, and rounds must also match across engines; transitions remain engine-specific. The table reports the minimum engine milliseconds and minimum end-to-end protocol wall independently, while the JSON retains every raw repeat and records which repeat supplied each minimum.

A naive repeat has a 900-second deadline covering the complete external protocol. If it expires, the runner prints `SKIP` with the workload, cell, repeat, deadline, and reason, then records that cell as skipped. Other failures hard-error with a named reason and do not publish a JSON artifact. Each completed JSON records the exact commit, binary paths and SHA-256 hashes, host facts, method, raw samples, selected minima, exact counters, rounds, and projection hashes.
