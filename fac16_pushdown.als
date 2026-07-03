// Model 16 — Projection pushdown: how the GHD actually BEATS the WCO join.
//
// The WCO join is output-optimal for FULL enumeration, so the GHD only wins when the query
// PROJECTS (the template uses a subset of the variables). The lever: project out a LOCAL
// variable (one appearing in a single relation, not in the output) BEFORE joining. If that is
// sound, a projecting cyclic query costs O(N + OUT_proj), not O(full join): the 4-cycle counted
// or projected is O(N^{3/2}) even though its full enumeration is O(N^2).
module fac16_pushdown

sig Val {}
sig R { x: one Val, v: one Val }   // R(x, v): v is LOCAL (projected out); x is shared / output.
sig Q { x: one Val }               // Q(x): stands for the rest of the acyclic query, on x.

// join R and Q on x, THEN project out v: the surviving output (x) values.
fun proj_after: set Val { { a: Val | (some r: R | r.x = a) and (some q: Q | q.x = a) } }
// project v out of R FIRST (R -> its x-values), then join with Q.
fun proj_before: set Val { { a: R.x | some q: Q | q.x = a } }

// SOUND: pushing the projection before the join gives the same output. Expect UNSAT.
assert PushdownSound { proj_after = proj_before }
check PushdownSound for 6 Val, 6 R, 6 Q

// WIN: the surviving full-join rows (x, v) can strictly outnumber the projected output (x), so
// projecting early does strictly less work. Expect SAT (a witness where projection shrinks).
pred ProjectionShrinks {
  #proj_before < #{ r: R | some q: Q | q.x = r.x }
}
run ProjectionShrinks for 6 Val, 6 R, 6 Q
