#!/usr/bin/env python3
"""Generate the measured programs for the two source-level transforms.

  chain_{naive,staged}.mm2   a chain query R-S-T, joined directly vs Yannakakis-staged
  proj_{keyfirst,keylast}.mm2  the same projection under both column orders
  tc_{naive,delta}.mm2       transitive closure, re-joined in full vs semi-naive

Run:  generate.py OUTDIR   then  mork run OUTDIR/<prog>.mm2 --steps 300 /tmp/out.space
"""
import os, random, sys

RULES = {'cyc_naive': '(exec 9 (, (e $a $b) (e $b $c) (e $c $d) (e $d $f) (e $f $g) (e $g $a)) (, (cyc6 $a)))', 'cyc_staged': '(exec (1 0) (, (e $a $b) (e $b $c) (e $c $d)) (, (p3 $a $d)))\n(exec (1 1) (, (p3 $a $d) (e $d $f) (e $f $g) (e $g $a)) (, (cyc6 $a)))', 'clq_naive': '(exec 9 (, (edge $x0 $x1) (edge $x0 $x2) (edge $x0 $x3) (edge $x1 $x2) (edge $x1 $x3) (edge $x2 $x3))\n        (, (c4 $x0 $x1 $x2 $x3)))', 'clq_staged': '(exec (1 0) (, (edge $x0 $x1) (edge $x0 $x2) (edge $x1 $x2)) (, (tri $x0 $x1 $x2)))\n(exec (1 1) (, (tri $x0 $x1 $x2) (edge $x0 $x3) (edge $x1 $x3) (edge $x2 $x3))\n            (, (c4 $x0 $x1 $x2 $x3)))', 'craft_naive': '(exec 9 (, (recipe $p (numIngredients 2)) (recipe $p (result (id $n)))\n           (recipe $p (pattern 0 $x)) (recipe $p (key ($x $xi)))\n           (recipe $p (pattern 1 $y)) (recipe $p (key ($y $yi)))\n           (inventory $xi) (inventory $yi))\n        (, (craftable $n)))', 'craft_staged': '(exec (1 0) (, (recipe $p (pattern 0 $x)) (recipe $p (key ($x $xi))) (inventory $xi)) (, (ok0 $p)))\n(exec (1 1) (, (recipe $p (pattern 1 $y)) (recipe $p (key ($y $yi))) (inventory $yi)) (, (ok1 $p)))\n(exec (1 2) (, (recipe $p (numIngredients 2)) (ok0 $p) (ok1 $p) (recipe $p (result (id $n))))\n            (, (craftable $n)))', 'lts_naive': '(exec (1 Z) (, (exec (1 $l) $p $t) (fuelN (S $k)) (state $s) (trans $s $u))\n            (O (+ (exec (1 (S $l)) $p $t)) (+ (state $u)) (+ (fuelN $k)) (- (fuelN (S $k)))))', 'lts_delta': ';; One exec: take the worklist, publish successors into both the state set and the worklist,\n;; retire what was taken. A separate promotion exec would be starved -- this family re-adds\n;; itself and sorts first, so it consumes all the fuel before the promoter ever runs.\n(exec (1 Z) (, (exec (1 $l) $p $t) (fuelD (S $k)) (dstate $s) (trans $s $u))\n            (O (+ (exec (1 (S $l)) $p $t)) (+ (state $u)) (+ (dstate $u))\n               (- (dstate $s)) (+ (fuelD $k)) (- (fuelD (S $k)))))', 'pc3_naive': '(exec (1 Z) (, (exec (1 $l) $p $t) (fuel (S $k))\n               (petri (? $c $pl $b)) (petri (! $c $pl)))\n            (O (+ (exec (1 (S $l)) $p $t)) (+ (petri $b)) (+ (fuel $k)) (- (fuel (S $k)))))', 'pc3_delta': '(exec (1 Z) (, (exec (1 $l) $p $t) (fuel (S $k))\n               (petri (? $c $pl $b)) (dmsg (! $c $pl)))\n            (O (+ (exec (1 (S $l)) $p $t)) (+ (petri $b)) (+ (dmsg $b))\n               (- (dmsg (! $c $pl))) (+ (fuel $k)) (- (fuel (S $k)))))', 'pc3_consume': '(exec (1 Z) (, (exec (1 $l) $p $t) (fuel (S $k))\n               (petri (? $c $pl $b)) (petri (! $c $pl)))\n            (O (+ (exec (1 (S $l)) $p $t)) (+ (petri $b))\n               (- (petri (? $c $pl $b))) (- (petri (! $c $pl)))\n               (+ (fuel $k)) (- (fuel (S $k)))))'}

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

    E = set()
    while len(E) < 900:
        a, b = random.randrange(70), random.randrange(70)
        if a != b: E.add((a, b))
    edges = "\n".join("(e n%d n%d)" % (a, b) for a, b in sorted(E)) + "\n"
    w("cyc_naive.mm2", edges + RULES["cyc_naive"] + "\n")
    w("cyc_staged.mm2", edges + RULES["cyc_staged"] + "\n")

    C = set()
    while len(C) < 3600:
        a, b = random.randrange(200), random.randrange(200)
        if a < b: C.add((a, b))
    cedges = "\n".join("(edge n%d n%d)" % (a, b) for a, b in sorted(C)) + "\n"
    w("clq_naive.mm2", cedges + RULES["clq_naive"] + "\n")
    w("clq_staged.mm2", cedges + RULES["clq_staged"] + "\n")

    L = []
    for pi in range(400):
        L += ["(recipe r%d (numIngredients 2))" % pi, "(recipe r%d (result (id item%d)))" % (pi, pi),
              "(recipe r%d (pattern 0 sx%d))" % (pi, pi), "(recipe r%d (pattern 1 sy%d))" % (pi, pi)]
        for k in range(12):
            L.append("(recipe r%d (key (sx%d ing%d)))" % (pi, pi, (pi * 3 + k) % 600))
            L.append("(recipe r%d (key (sy%d ing%d)))" % (pi, pi, (pi * 5 + k) % 600))
    L += ["(inventory ing%d)" % i for i in range(600)]
    craft = "\n".join(L) + "\n"
    w("craft_naive.mm2", craft + RULES["craft_naive"] + "\n")
    w("craft_staged.mm2", craft + RULES["craft_staged"] + "\n")

    tr = "\n".join("(trans s%d s%d)" % (i, (i * 7 + j * 13 + 1) % 6000)
                    for i in range(6000) for j in range(3)) + "\n(state s0)\n"
    w("lts_naive.mm2", tr + RULES["lts_naive"] + "\n")
    w("lts_delta.mm2", tr + "(dstate s0)\n" + RULES["lts_delta"] + "\n")

    for n in (200, 400, 800):
        soup = "\n".join("(petri (? c%d p%d (! c%d p%d)))" % (i, i, i + 1, i + 1) for i in range(n))
        fuel = "Z"
        for _ in range(n + 5): fuel = "(S %s)" % fuel
        head = soup + "\n(petri (! c0 p0))\n(fuel %s)\n" % fuel
        w("pc%d_naive.mm2" % n, head + RULES["pc3_naive"] + "\n")
        w("pc%d_delta.mm2" % n, soup + "\n(petri (! c0 p0))\n(dmsg (! c0 p0))\n(fuel %s)\n" % fuel
                                + RULES["pc3_delta"] + "\n")
        w("pc%d_consume.mm2" % n, head + RULES["pc3_consume"] + "\n")
    print("wrote all programs to " + outdir)

if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else ".")
