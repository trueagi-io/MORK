// Model 17 — Factorized aggregation: the win the WCO join cannot match.
//
// WCO is output-optimal for ENUMERATION, so it cannot be beaten there. But a COUNT/SUM does not
// need the tuples, only the aggregate. Factorizing it collapses the join variable into a
// sum-of-products: |R(x,y) join S(y,z)| = SUM_y |R_y| * |S_y|, touching each relation ONCE
// (O(N)), where enumerate-and-count materializes all O(N^2) tuples. That is a genuine asymptotic
// win over WCO, and it is exactly what the GHD/Yannakakis machinery computes.
module fac17_count

sig Val {}
sig R { x: one Val, y: one Val }   // R(x, y)
sig S { y: one Val, z: one Val }   // S(y, z), joined on y

// enumerate-and-count: the number of join tuples (x, y, z) = matching (r, s) pairs.
fun enumCount: Int { #{ r: R, s: S | r.y = s.y } }

// factorized count: group by the join variable y, multiply per-group sizes, sum. Touches each
// relation once.
fun ry[v: Val]: Int { #{ r: R | r.y = v } }
fun sy[v: Val]: Int { #{ s: S | s.y = v } }
fun factCount: Int { sum v: Val | mul[ry[v], sy[v]] }

// SOUND: the factorized aggregate equals the enumerated one. Expect UNSAT.
assert CountFactorizes { enumCount = factCount }
check CountFactorizes for 4 Val, 5 R, 5 S, 7 int

// WIN: the enumerated tuple count can strictly exceed the number of input rows touched by the
// factorized pass (|R| + |S|), so factorizing does asymptotically less work. Expect SAT.
pred FactorizedTouchesFewer { enumCount > add[#R, #S] }
run FactorizedTouchesFewer for 4 Val, 5 R, 5 S, 7 int
