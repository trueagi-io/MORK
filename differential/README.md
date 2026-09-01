# Differential tests

The MORK kernel has two query engines. The ProductZipper (`Space::query_multi`) is
the reference; the worst-case-optimal leapfrog join (`leapfrog::query_multi_leapfrog`)
is a compile-time alternative selected by the `leapfrog` cargo feature and only used
for bodies it can handle, everything else falling back to the ProductZipper.

The two must be indistinguishable. This directory is the harness that proves it:
it runs a corpus of `.mm2` programs through both builds and compares the space each
one dumps byte for byte, plus the number of steps each one reports executing.

Programs may additionally pin a checked-in expected space, so the same corpus is a
plain regression suite that does not need two engines at all.

## Running it

```sh
# build both binaries and run everything
python3 differential/run.py --build

# or point it at binaries you already have
cargo build --release -p mork                     && cp target/release/mork /tmp/mork-pz
cargo build --release -p mork --features leapfrog && cp target/release/mork /tmp/mork-lf
python3 differential/run.py --pz /tmp/mork-pz --lf /tmp/mork-lf
```

Note that both builds write `target/release/mork`, so one must be copied aside
before the other is built. `--build` does that for you.

Useful flags:

| flag | meaning |
| --- | --- |
| `--slow` | also run programs tagged `slow` (the default tier is a few seconds) |
| `--generated` | run `generators/*.py` and include what they emit |
| `--single pz` / `--single lf` | one engine only; checks expected files, not equivalence |
| `--update-expected` | rewrite every declared expected file from the reference engine |
| `--list` | show the corpus with its declared steps/tags and exit |
| `-j N`, `-v`, `--timeout S` | parallelism, per-program lines, per-run timeout |
| `NAME...` | positional substring filters, e.g. `run.py unify/ bc0` |

Exit status is non-zero if anything failed, so this can be wired into CI as-is.
Python 3 standard library only; there is nothing to install.

## The corpus

Roots scanned by default:

- `differential/corpus/` — programs lifted out of `kernel/src/main.rs`, where the
  Rust test was already "build a space from a literal, run `metta_calculus`, assert
  on the dump".
  - `unify/` — the unification and join semantics: ground vs. variable on either
    side, repeated variables, wildcards in the *data*, bare top-level conjuncts.
  - `programs/` — whole programs: CTL model checking, backward chaining, an
    anamorphism, a pi-calculus reduction, proof search.
  - `wiki/` — every runnable example from the MORK wiki, one file per code block,
    named `<page>_<block>.mm2` and carrying the page it came from in its `@desc`.
    The tutorials build a program up over many blocks, so the intermediate versions
    are here too: each is a program the wiki asks a reader to run, so each is a
    program that has to keep working. The final version of each tutorial pins an
    expected space.
- `kernel/resources/` — the `.mm2` programs that already lived in the repo.

Anything a program needs beyond the two binaries is declared in its own leading
comment block, so a corpus entry stays an ordinary runnable `.mm2` file:

```
;; @desc   one line of prose (repeatable)
;; @steps  50            how many steps to run; default is the CLI's "run to fixpoint"
;; @expect-steps 50      pin the reported "executing N steps"
;; @expect               pin the whole space against differential/expected/<name>.expected
;; @expect  other.space  ... or against a path relative to the program
;; @aux     lib.mm2      extra --aux-path input (repeatable)
;; @tags    slow         opt-in tier
;; @skip    reason       do not run this program
```

Only programs that ask for one get an expected file. That is deliberate: the
`exponential` benchmarks dump 13 MB and 48 MB respectively, which is worth
comparing between engines but not worth checking in. Empty `.mm2` files are
skipped automatically.

`--update-expected` regenerates every declared expected file from the ProductZipper
arm, and rewrites an existing `@expect-steps` line in place. Review the resulting
diff before committing it: that is the whole value of the file.

## Generated programs

Some benchmarks build their data in Rust with a seeded RNG over tens of thousands
of facts. Those cannot be checked in as text, and the Rust `StdRng` stream cannot
be reproduced from Python anyway, so `generators/` emits the same *shapes* at sizes
that finish in seconds, from its own seeded PRNG so the files are byte-stable:

| generator | stands in for |
| --- | --- |
| `gen_transitive.py` | `bench_transitive_no_unify(50000, 1000000)` |
| `gen_clique.py` | `bench_clique_no_unify(200, 3600, 5)` |
| `gen_process_calculus.py` | `process_calculus_bench(1000, 200, 200)` |

They are skipped unless `--generated` is passed, and each writes `.mm2` files into
`target/differential/generated/`. Nothing generated is checked in.

## What is *not* here

Tests that assert on something a space dump cannot express — instruction counters,
`touched` counts, timings — and tests that need sinks, sources, ACT or Z3 stay as
Rust functions in `kernel/src/main.rs`. `mork test` remains the way to run those.
