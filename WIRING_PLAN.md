# Wiring plan: route COUNT/SUM through the factorized aggregation

Goal: make MORK's existing COUNT/SUM **sinks** compute their answer with the factorized
sum-product engine (O(N^fhtw)) instead of enumerate-then-count (O(output)), byte-identical.
This ACCELERATES an existing operation asymptotically — exactly what Adam's upstream policy
protects ("closed to constant-time speed-ups until the asymptotic runtime has no known
deficiencies") — it is not a new feature and not a constant factor.

## Status
- **Slices 1-3 LANDED and proven** (commits `caa1ff2` connected-components, `42fc718` routing,
  `8a346f5` benchmark). The count sink routes through the factorized aggregate, gated behind
  `MORK_FACTORIZED_COUNT` / a per-thread test override, **default OFF**. Three differential oracles
  assert byte-identical whole-space dumps (sound Cartesian + connected star route; grouped +
  projected decline and fall back). Full lib suite 35/0. Measured through the exec:
  `factorized_count_sink_win_scales` grows 16.3x -> 399.9x (k=50..800), byte-identical each k -- the
  growing (not flat) speedup proves the fast path is actually taken.
- **Alloy fac18** (`alloy-mork`, online) proves the exact gate: distinct-output == match count iff
  the projection keeps every variable.
- **Slice 4 LANDED** (commit `ee476e4`): the SumSink routes SUM(DISTINCT col) through a Yannakakis
  semi-join reduction -- sum the column's surviving domain, computed by keeping it free and
  eliminating the rest over the EXISTS semiring. Key fix: `elimination_order_free` re-roots the order
  at the summed column's bag, or a chain join tree eliminates a shared variable before a leaf and
  materializes a quadratic intermediate (ghd_sum_distinct was O(k^2), 324918us -> O(k), 971us at
  k=800). Through the exec the SUM sink grows 13.3x -> 340.5x, byte-identical. Alloy `fac19` proves
  the semi-join domain equals the join's column projection. Full lib suite 37/0.
- **MIN/MAX also WIRED** (commit `985700b`): `FloatReductionSink<Min>/<Max>` route through the same
  semi-join surviving domain (MIN/MAX are idempotent + exact, so distinct==all and the f64 to_string
  is byte-identical). Float SUM/PROD deliberately NOT routed -- their reduction is order-sensitive
  (non-associative rounding), so a different domain order could differ in the last bit. The aggregate
  family is now COUNT, SUM, MIN, MAX.
- **Perfected:** a 600-program property-based fuzz differential (six join shapes incl. cyclic,
  4-cycle, self-join; COUNT/SUM/MIN/MAX; grouped/partial declines) is byte-identical both ways;
  Alloy `fac16`-`fac21` cover every gate decision; gate knob renamed `MORK_FACTORIZED_AGGREGATE`;
  jscpd 0, full lib suite 39/0.
- **Slice 5 (fusion) is a NON-GOAL as an automatic pass** -- and not for value reasons: removing
  `res0`'s materialization changes the OBSERVABLE space (dumps, other execs, external queries can
  read `res0`), and `res0` cannot be proven dead in MORK's open, externally-queryable model. It is
  sound only as a user-directed rewrite where the user asserts `res0` is intermediate -- a separate
  feature, not part of the aggregate routing. The natural single-exec `(exec (, join) (O (agg ..)))`
  form is already fully optimized by what landed.

## Prior art (researched, tavily)
The wiring is a combination of battle-tested work, not an invention:
- **Engine (C1):** FAQ / `InsideOut` (Abo Khamis-Ngo-Rudra, PODS'16) -- aggregation as semiring
  variable elimination over worst-case-optimal joins. Same as the generalized distributive law
  (Aji-McEliece) and factorized-DB aggregation (Bakibayev-Kocisky-Olteanu-Zavodny, PVLDB'13).
- **Pushdown soundness (C2):** Yan-Larson eager aggregation (VLDB'95, now in PostgreSQL; conditions
  by Chaudhuri-Shim). The gate (full projection, no grouping) is their "double eager" COUNT:
  push COUNT to all relations and multiply, `Sum_y Prod |R_y|`.
- **Distinct (C3):** the CountSink counts distinct OUTPUTS; the full-projection gate makes
  distinct == matches (fac18), sidestepping hard COUNT-DISTINCT-over-join.
- **Disconnected (C4):** GYO's isolated-edge-is-an-ear (Ullman, Fagin) -> a disconnected CQ is a
  Cartesian product -> connected-components split, `Prod` of per-component aggregates.
- **Semiring contract (C5):** FAQ + fac10 + the MORK devnotes all require a commutative semiring;
  COUNT (naturals) qualifies, so MORK's own regroup-freedom already licenses the factorization.

## Pick-up context (read first after compaction)
- Repo/branch: `/home/user/Dev/mork-124-validate`, branch `wco-ghd-upstream`, off #124
  (`e491c44`, upstream PR trueagi-io/MORK#124 = fork/wco-leapfrog-join).
- Author EVERY commit `MesTTo <a.mesto@student.unsw.edu.au>` (author AND committer). This is the
  corrected email (Dev/CLAUDE.md was fixed; old commits were re-authored via filter-branch).
- Build/test: `RUSTFLAGS="-C target-cpu=native -Awarnings" cargo +nightly test -p mork --lib ghd`.
- Alloy models backing this: `/home/user/Dev/alloy-mork` — `fac14_ghd` (decomposition sound),
  `fac16_pushdown` (projection pushdown sound only for a variable local to one relation),
  `fac17_count` (|R⋈S| = Σ_y |R_y|·|S_y|, factorized == enumerate).
- Commits so far on this branch (leaf order):
  `b71bc6a` planner · `1a04c22` evaluation · `718a97f` factorized COUNT · `6ac0bbe` semiring ·
  `fe45c19` elimination order · `639440c` flybase star benchmark.

## What is already built (REUSE, do not rebuild)
`kernel/src/ghd.rs`:
- `hypergraph(&[Factor]) -> Vec<BTreeSet<usize>>`, `gyo_join_tree`, `decompose(edges, k_max) -> Option<Ghd>`.
- `Bag`, `Ghd { bags, parent, width }`, `elimination_order(&Ghd) -> Vec<usize>`.
- `Semiring` trait (impls: `u64` = COUNT, `bool` = EXISTS), `FactorTable<S>`, `materialize_factor_table`,
  `multiply`, `sum_out`.
- `ghd_aggregate::<S>(map, factors, nvars, elim_order, weight) -> S` — the sum-product engine.
- **`ghd_aggregate_auto::<S>(map, factors, nvars, weight) -> Option<S>`** — decompose + derive order +
  aggregate. THIS is the entry point to call from the sink path. `None` = does not decompose.
- `ghd_count` = `ghd_aggregate::<u64>(.., |_| 1)`.

`kernel/src/zipper_join.rs`:
- `parse_body_factors(body: &[u8]) -> Option<(Vec<Factor>, usize)>` — a `(, ...)` body's bytes to factors.
- `pub fn run_unify_join_stream(map, factors, var_order, nvars, on_tuple)` — the WCO join (enumerate baseline).
- `query_multi_ghd` — byte-identical GHD drop-in for ENUMERATION (not the count path).
- Oracles/benches: `ghd_full_tuples_match_global_join_on_cycles`, `ghd_count_matches_enumerate_count`,
  `ghd_aggregate_over_semirings`, `ghd_aggregate_auto_derives_order_on_a_chain`,
  `ghd_count_win_scales` (#[ignore]), `ghd_count_flybase_star_shape` (#[ignore], 216.9x measured).

## The wiring target (existing enumerate-based sink)
- `kernel/src/sinks.rs` ~line 547: `pub struct CountSink { e: Expr, unique: PathMap<()> }`.
  - `sink()` inserts each match's output path into `unique` (dedup).
  - `finalize()` counts `unique.val_count()` GROUPED BY a context and emits `(count of $k is <n>)` by
    `substitute_one_de_bruijn` of the count into the sink template. Enumerate-based, O(output).
  - Semantics comment (~line 543): `(count (count of $k is $i) $i (proj))` = GROUP BY `$k`, count
    DISTINCT `proj`, emit per group. `SumSink` is the weighted analogue.
- `kernel/src/space.rs` ~line 1498: `transform_multi_multi_o(pat_expr, tpl_expr, add)` drives the O-sink
  path: `query_multi(&read_copy, pat_expr, |bindings, loc| { ... sinks[i].sink(..) })` per match, then
  `sinks[i].finalize(..)`. Templates parsed to `ASink` (enum, ~line 1225: CountSink, SumSink, ...).
- Exec grammar: `(exec loc (, pattern) (O (COUNT ...)))`; `interpret` (space.rs ~1671) routes `(',','O')`
  to `transform_multi_multi_o`. COUNT/SUM are sinks (wiki `Sources-and-Sinks.md`, both TODO there).

## Soundness condition (WHEN factorizing is correct)
`ghd_aggregate` counts MATCHES (multiplicity). `CountSink` counts DISTINCT `proj`. Routing is sound
iff DISTINCT `proj` == match count. That holds when:
1. `proj` = ALL body variables (nothing projected away collapses distinct below matches), AND
2. no grouping key changes semantics (single group), AND
3. each output tuple arises once (true when all vars are in the output).
Local-variable projection (dropping a variable that occurs in ONE relation only) is also sound
(Alloy `fac16`); a projected-out JOIN variable is NOT (distinct < matches) → always fall back.
The enumerate `CountSink` is ALWAYS correct; the fast-path is an optional, proven acceleration.

## Slices (build, differential-oracle byte-identical vs enumerate, NO default flip until proven)
1. **[DONE] CountSink precomputed fast-path.** Add `precomputed: Option<u64>` to `CountSink`. In `finalize`,
   if `Some(n)`, emit `n` for the single group via the SAME `substitute_one_de_bruijn` emit path (so it
   is byte-identical to the enumerate path that reached `unique.val_count() == n`); skip the `unique`
   scan. Default `None` = unchanged. Differential: set `precomputed` to the true count and assert the
   emitted space == the enumerate sink's (`dump_all_sexpr`).
2. **[DONE] Detect + route in `transform_multi_multi_o`.** Before the query loop, gate on: exactly one sink,
   it is a `CountSink`, `pat_expr` is a multi-factor `(, ..)` (`parse_body_factors` Some, len ≥ 2),
   `decompose(hypergraph(&factors), 3)` Some, no nonground compound columns, count is
   projection-free-full-vars (sink proj == body vars, no grouping). If so:
   `let n = ghd::ghd_aggregate_auto::<u64>(&read_copy, &factors, nvars, |_| 1)?;` set
   `count_sink.precomputed = Some(n)`, SKIP the `query_multi` loop, go to `finalize`. Else unchanged.
   Feature-gate (env `MORK_FACTORIZED_COUNT` or cargo feature), default OFF.
3. **[DONE] Differential corpus.** Test the transform BOTH ways (fast-path on/off) over: star, chain,
   projection-free multi-join (route + win); AND adversarial (projected join var, grouped, cyclic,
   nonground compound, single-factor) which MUST fall back — assert byte-identical `dump_all_sexpr` and
   identical `(count "..." n)`. Flip default only after clean.
4. **[DONE] SUM sink via Yannakakis semi-join.** `SumSink` is `SUM(DISTINCT col)` (FAQ SumSum), NOT a
   COUNT weight-swap. Landed as `ghd_surviving_domain` (keep the column free, EXISTS-eliminate the
   rest = the full reducer) + `ghd_sum_distinct` (parse + sum, wrapping u32 to match) +
   `elimination_order_free` (root at the free column's bag -- without this it is O(N^2)). Gate:
   ungrouped, single-column projection, connected, >= 2 factors. `SumSink::set_precomputed` in both
   emit guards. Differentials + a scaling proof; Alloy `fac19`.
5. **[NON-GOAL as an automatic pass] P1+P1'' fusion.** Fusing `(exec P1 join (,) res0)` +
   `(exec P1'' (res0 ..) (O (COUNT ..)))` to skip materializing `res0` is UNSOUND automatically:
   `res0` is written into the space and is observable (dumps, other execs, external queries), and it
   cannot be proven dead in MORK's open model. Sound only as a user-directed rewrite where the user
   asserts `res0` is intermediate -- a separate feature. The natural single-exec count/sum/min/max
   form is already fully optimized (Slices 1-4), so there is no automatic win to chase here.

## Measurement
- `ghd_count_flybase_star_shape` already shows 216.9x on the P1 star (k inputs, k^2 output). After
  slice 2, add `mork bench count_join` running a COUNT exec both ways. Real flybase data
  (`/dev/shm/combined_ni.paths.gz`, ~978M atoms) is not present here; the synthetic star is the proxy.

## Never-wrong gates (fall back to enumerate CountSink)
Grouping keys · projected-out join variables · nonground compound columns · non-decomposable bodies ·
single-factor patterns (already O(N)). Correctness is paramount (>$1M): the differential oracle is the
gate; default stays enumerate until the adversarial corpus is byte-identical.
