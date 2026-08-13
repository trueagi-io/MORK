#!/usr/bin/env python3
"""Emit persistent-rule instances of MORK's process-calculus benchmark."""

import argparse
import os


DEFAULT_INSTANCES = ((32, 32), (64, 64), (128, 128), (200, 200), (320, 320))

TEMPLATE = """\
; Process-calculus addition from `process_calculus_bench`.
; The benchmark's idle rules and IC controller are represented as persistent rules.

(exec 0
  (, (petri (? $channel $payload $body))
     (petri (! $channel $payload)))
  (, (petri $body)))

(exec 1
  (, (petri (| $left $right)))
  (, (petri $left)
     (petri $right)))

(petri (? (add $ret) ((S $x) $y)
          (| (! (add (PN $x $y)) ($x $y))
             (? (PN $x $y) $z (! $ret (S $z))))))
(petri (? (add $ret) (Z $y) (! $ret $y)))
(petri (! (add result) (%(x)s %(y)s)))
"""


def peano(value):
    return "(S " * value + "Z" + ")" * value


def parse_instance(value):
    try:
        left, right = (int(part) for part in value.split(":", 1))
    except ValueError as error:
        raise argparse.ArgumentTypeError("expected LEFT:RIGHT") from error
    if left < 0 or right < 0:
        raise argparse.ArgumentTypeError("operands must be nonnegative")
    return left, right


def generate(output_directory, instances):
    os.makedirs(output_directory, exist_ok=True)
    paths = []
    for left, right in instances:
        path = os.path.join(
            output_directory,
            "process_calculus_%03d_%03d.source.mm2" % (left, right),
        )
        with open(path, "w", encoding="utf-8", newline="\n") as stream:
            stream.write(TEMPLATE % {"x": peano(left), "y": peano(right)})
        required_path = path[: -len(".source.mm2")] + ".required"
        with open(required_path, "w", encoding="utf-8", newline="\n") as stream:
            stream.write("(petri (! result %s))\n" % peano(left + right))
        paths.append(path)
    return paths


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output_directory")
    parser.add_argument(
        "--instance",
        action="append",
        type=parse_instance,
        dest="instances",
        help="operand pair LEFT:RIGHT; repeat for multiple programs",
    )
    args = parser.parse_args()
    for path in generate(args.output_directory, args.instances or DEFAULT_INSTANCES):
        print(path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
