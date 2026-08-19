#!/usr/bin/env python3
"""Generate the measured programs for the two source-level transforms.

  chain_{naive,staged}.mm2   a chain query R-S-T, joined directly vs Yannakakis-staged
  proj_{keyfirst,keylast}.mm2  the same projection under both column orders
  tc_{naive,delta}.mm2       transitive closure, re-joined in full vs semi-naive

Run:  generate.py OUTDIR   then  mork run OUTDIR/<prog>.mm2 --steps 300 /tmp/out.space
"""
import os, random, sys

def main(outdir):
    os.makedirs(outdir, exist_ok=True)
    w = lambda n, s: open(os.path.join(outdir, n), "w").write(s)
    random.seed(9)

    # ---- chain query: T is narrow, so most S and R tuples dangle
    ny = nz = 600
    R = [(f"x{i}", f"y{random.randrange(ny)}") for i in range(60000)]
    S = [(f"y{random.randrange(ny)}", f"z{random.randrange(nz)}") for i in range(60000)]
    T = [(f"z{i}", f"w{j}") for i in range(8) for j in range(3)]
    data = ([f"(R {a} {b})" for a, b in R] + [f"(S {a} {b})" for a, b in S]
            + [f"(T {a} {b})" for a, b in T])
    w("chain_naive.mm2", "\n".join(data) + "\n"
      "(exec 9 (, (R $x $y) (S $y $z) (T $z $w)) (, (out $x $w)))\n")
    w("chain_staged.mm2", "\n".join(data) + """
;; Yannakakis: project, semi-join bottom-up, semi-join top-down, join the reduced relations.
;; Every projection is `(, (Rel $key $_))` -- the shape the projection cut answers with one
;; witness per key -- which is why the reduced relations are emitted KEY-FIRST.
(exec (1 0) (, (T $z $_))            (, (Tz $z)))
(exec (1 1) (, (S $y $z) (Tz $z))    (, (S1 $y $z)))
(exec (1 2) (, (S1 $y $_))           (, (S1y $y)))
(exec (1 3) (, (R $x $y) (S1y $y))   (, (R1 $y $x)))
(exec (1 4) (, (R1 $y $_))           (, (R1y $y)))
(exec (1 5) (, (S1 $y $z) (R1y $y))  (, (S2 $z $y)))
(exec (1 6) (, (S2 $z $_))           (, (S2z $z)))
(exec (1 7) (, (T $z $w) (S2z $z))   (, (T1 $z $w)))
(exec (2 0) (, (R1 $y $x) (S2 $z $y) (T1 $z $w)) (, (out $x $w)))
""")

    # ---- the projection alone, under both column orders
    P = [(f"y{random.randrange(600)}", f"z{random.randrange(600)}") for _ in range(80000)]
    pd = "\n".join(f"(S {a} {b})" for a, b in P)
    w("proj_keyfirst.mm2", pd + "\n(exec 0 (, (S $y $_)) (, (Sy $y)))\n")
    w("proj_keylast.mm2", pd + "\n(exec 0 (, (S $_ $z)) (, (Sz $z)))\n")

    # ---- transitive closure over a chain: |path| is quadratic, each frontier is linear
    n = 220
    edges = "\n".join(f"(edge n{i} n{i+1})" for i in range(n - 1))
    w("tc_naive.mm2", edges + """
(exec (0 0) (, (edge $x $y)) (, (path $x $y)))
(exec (1 Z) (, (exec (1 $l) $p $t) (path $x $y) (edge $y $z))
            (, (exec (1 (S $l)) $p $t) (path $x $z)))
""")
    w("tc_delta.mm2", edges + """
(exec (0 0) (, (edge $x $y)) (, (front Z $x $y) (path $x $y)))
(exec (1 Z) (, (exec (1 $l) $p $t) (front $l $x $y) (edge $y $z))
            (, (exec (1 (S $l)) $p $t) (front (S $l) $x $z) (path $x $z)))
""")
    print("wrote 6 programs to " + outdir)

if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else ".")
