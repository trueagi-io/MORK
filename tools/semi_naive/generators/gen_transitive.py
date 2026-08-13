#!/usr/bin/env python3
"""Emit chain transitive-closure programs at deterministic sizes."""

import argparse
import os


DEFAULT_LENGTHS = (64, 128, 256, 384)

RULE = """\

(exec 0
  (, (edge $x $y) (edge $y $z))
  (, (edge $x $z)))
"""


def positive_integer(value):
    parsed = int(value)
    if parsed <= 0:
        raise argparse.ArgumentTypeError("length must be positive")
    return parsed


def generate(output_directory, lengths):
    os.makedirs(output_directory, exist_ok=True)
    paths = []
    for length in lengths:
        path = os.path.join(
            output_directory, "transitive_chain_%03d.source.mm2" % length
        )
        with open(path, "w", encoding="utf-8", newline="\n") as stream:
            stream.write("; %d-edge transitive-closure chain.\n\n" % length)
            for index in range(length):
                stream.write("(edge n%03d n%03d)\n" % (index, index + 1))
            stream.write(RULE)
        paths.append(path)
    return paths


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output_directory")
    parser.add_argument(
        "--length",
        action="append",
        type=positive_integer,
        dest="lengths",
        help="chain edge count; repeat for multiple programs",
    )
    args = parser.parse_args()
    for path in generate(args.output_directory, args.lengths or DEFAULT_LENGTHS):
        print(path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
