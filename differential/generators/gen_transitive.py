#!/usr/bin/env python3
"""Emit scaled-down instances of the `transitive` benchmark.

`bench_transitive_no_unify(50000, 1000000)` builds a random graph in Rust and
runs two joins over it.  A million edges is not something to check in, and the
Rust `StdRng` stream cannot be reproduced here anyway, so this emits the same
*shape* at sizes that finish in seconds, from a seeded PRNG of its own so the
files are byte-stable.

usage: gen_transitive.py OUTDIR
"""
import os
import random
import sys

# (nodes, edges, tags) -- keep the default instance quick; the big one is opt-in.
INSTANCES = [
    (60, 300, ""),
    (400, 6000, "slow"),
]

BODY = """
(exec 0 (, (edge $x $y) (edge $y $z)) (, (trans $x $z)))
(exec 1 (, (edge $x $y) (edge $y $z) (edge $x $z)) (, (dtrans $x $y $z)))
"""


def main(outdir):
    os.makedirs(outdir, exist_ok=True)
    for nnodes, nedges, tags in INSTANCES:
        rng = random.Random(0)
        edges = sorted({(rng.randrange(nnodes), rng.randrange(nnodes))
                        for _ in range(nedges)})
        name = "transitive_%dx%d" % (nnodes, nedges)
        path = os.path.join(outdir, name + ".mm2")
        with open(path, "w") as f:
            f.write(";; @desc generated: transitive closure over a random graph, "
                    "%d nodes / %d distinct edges\n" % (nnodes, len(edges)))
            f.write(";; @desc shape of main.rs bench_transitive_no_unify, scaled down\n")
            f.write(";; @steps 2\n")
            if tags:
                f.write(";; @tags %s\n" % tags)
            f.write("\n")
            for i, j in edges:
                f.write("(edge %d %d)\n" % (i, j))
            f.write(BODY)
        print(path)


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else ".")
