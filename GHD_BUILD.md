# GHD for upstream MORK — build plan (branch wco-ghd-upstream, off #124)

Goal: worst-case-optimal evaluation BEYOND the WCO join, for cyclic bodies where
fhtw < rho* (the 4-cycle: rho*=2 O(N^2) -> width-2 decomposition O(N^{3/2})).
Drop-in for `query_multi_dispatch`: produce the SAME `effect(bindings, loc)` stream,
computed via decomposition. Byte-identical is the law (differential oracle).

Design contract (from transform_multi_multi_ @ space.rs:1382):
  query_multi_dispatch(btm, pat_expr, effect) streams (Err(bindings), loc) per match.
  query_multi_leapfrog's `on_tuple(tuple: &[Vec<u8>])` (one matched fact per factor)
  does `unify(pairs) -> bindings`, `loc = tuple[0]`, `effect(Err(bindings), loc)`.
  => GHD enumerates the SAME full tuples (matched fact per factor) via bag joins,
     then calls the identical unify+effect. Same tuples => byte-identical.

## Slices (correctness first, then the asymptotic join)
- [x] A. Planner (ghd.rs): hypergraph, GYO, min-width decomposition. TESTED. (356b56b)
- [ ] B. Bag materialization: run the WCO join on a bag's factors; per match collect
       (the matched facts for the bag's factors) keyed by the bag's shared-variable
       VALUES (top-level FactorColumn::Var columns; nested-var bodies fall back).
       Test: the bag relation = the WCO join output projected to the bag.
- [ ] C. Bag join (Yannakakis): the bags form an acyclic bag-query; semijoin-reduce
       along the GYO join tree, then join on shared variables -> full tuples (a fact
       per original factor). Reuse on_tuple(full_tuple) for unify+effect.
- [ ] D. query_multi_ghd drop-in + gate (only cyclic + top-level-var bodies route;
       else global WCO join). Differential oracle vs query_multi_dispatch: identical
       answer set on triangle + 4-cycle over random spaces, ground AND schematic.
- [ ] E. Benchmark: a 4-cycle bench showing the O(N^{3/2}) vs O(N^2) separation.

## Fallbacks (never wrong, only slower)
- Nested-var shared variables, disconnected bodies, no low-width decomposition,
  or any parse the planner declines -> return None -> caller keeps the WCO join.
- Model 14 cover is the soundness invariant; the differential oracle is the gate.
