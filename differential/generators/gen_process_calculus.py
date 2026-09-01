#!/usr/bin/env python3
"""Emit scaled-down instances of the `process_calculus` benchmark.

`process_calculus_bench(1000, 200, 200)` adds two Peano numerals of 200 in a
pi-calculus encoding; the numerals alone are 200-deep s-expressions and the run
takes ~40 s.  The program text is a `format!` template in Rust, so it is
regenerated here at small operand sizes.

Unlike the Rust bench this checks the whole final space, not just the result
channel, which is what makes it a differential case.

usage: gen_process_calculus.py OUTDIR
"""
import os
import sys

INSTANCES = [(20, 3, 4), (60, 8, 9), (400, 60, 60)]  # (inference budget, x, y)

TEMPLATE = """
(exec (IC 0 1 %(budget)s)
               (, (exec (IC $x $y (S $c)) $sp $st)
                  ((exec $x) $p $t))
               (, (exec (IC $y $x $c) $sp $st)
                  (exec (R $x) $p $t)))

((exec 0)
      (, (petri (? $channel $payload $body))
         (petri (! $channel $payload)) )
      (, (petri $body)))
((exec 1)
      (, (petri (| $lprocess $rprocess)))
      (, (petri $lprocess)
         (petri $rprocess)))

(petri (? (add $ret) ((S $x) $y) (| (! (add (PN $x $y)) ($x $y))
                                    (? (PN $x $y) $z (! $ret (S $z)))  )  ))
(petri (? (add $ret) (Z $y) (! $ret $y)))
(petri (! (add result) (%(x)s %(y)s)))
"""


def peano(n):
    return "(S " * n + "Z" + ")" * n


def main(outdir):
    os.makedirs(outdir, exist_ok=True)
    for budget, x, y in INSTANCES:
        name = "process_calculus_%dp%d" % (x, y)
        path = os.path.join(outdir, name + ".mm2")
        tags = "slow" if x > 10 else ""
        with open(path, "w") as f:
            f.write(";; @desc generated: pi-calculus addition %d+%d under an inference\n"
                    ";; @desc budget of %d (shape of main.rs process_calculus_bench)\n"
                    % (x, y, budget))
            if tags:
                f.write(";; @tags %s\n" % tags)
            f.write(TEMPLATE % {"budget": peano(budget),
                                "x": peano(x), "y": peano(y)})
        print(path)


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else ".")
