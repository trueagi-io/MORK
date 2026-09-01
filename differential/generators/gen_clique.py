#!/usr/bin/env python3
"""Emit scaled-down instances of the `clique` benchmark.

`bench_clique_no_unify(200, 3600, 5)` searches for 3-, 4- and 5-cliques in a
random degeneracy-ordered graph; the 5-clique pass alone takes ~25 s in the
reference engine, so only the k=3 and k=4 queries are emitted by default and
the graph is smaller.  Same shape, seconds instead of minutes.

usage: gen_clique.py OUTDIR
"""
import os
import random
import sys

INSTANCES = [
    (40, 300, 3, ""),
    (40, 300, 4, ""),
    (200, 3600, 3, "slow"),
    (200, 3600, 4, "slow"),
]


def clique_query(k):
    conjuncts = "".join(" (edge $x%d $x%d)" % (i, j)
                        for i in range(k) for j in range(i + 1, k))
    head = "".join(" $x%d" % i for i in range(k))
    return "(exec 0 (,%s) (, (%d-clique%s)))\n" % (conjuncts, k, head)


def main(outdir):
    os.makedirs(outdir, exist_ok=True)
    for nnodes, nedges, k, tags in INSTANCES:
        rng = random.Random(0)
        edges = set()
        while len(edges) < nedges:
            i = rng.randrange(nnodes)
            j = rng.randrange(nnodes)
            if i == j:
                continue
            edges.add((min(i, j), max(i, j)))  # irreflexive, degeneracy ordered
        name = "clique%d_%dx%d" % (k, nnodes, nedges)
        path = os.path.join(outdir, name + ".mm2")
        with open(path, "w") as f:
            f.write(";; @desc generated: %d-clique enumeration over a random graph, "
                    "%d nodes / %d edges\n" % (k, nnodes, nedges))
            f.write(";; @desc shape of main.rs bench_clique_no_unify, scaled down\n")
            f.write(";; @steps 1\n;; @expect-steps 1\n")
            if tags:
                f.write(";; @tags %s\n" % tags)
            f.write("\n")
            for i, j in sorted(edges):
                f.write("(edge %d %d)\n" % (i, j))
            f.write(clique_query(k))
        print(path)


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else ".")
