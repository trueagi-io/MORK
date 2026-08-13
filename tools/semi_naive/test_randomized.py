#!/usr/bin/env python3
"""Run deterministic generated add-only programs through the projection oracle."""

import argparse
import contextlib
import io
import os
import random
import sys
import tempfile


HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
import driver
import sexpr
import transform


VALUES = ("a", "b", "c", "d")


def generate(seed):
    rng = random.Random(seed)
    lines = ["; deterministic generated case %d" % seed, ""]
    relation_count = rng.randint(2, 5)
    for relation_index in range(relation_count):
        selected = [value for value in VALUES if rng.randrange(2)]
        if not selected:
            selected = [VALUES[rng.randrange(len(VALUES))]]
        for value in selected:
            lines.append("(r%d %s)" % (relation_index, value))

    lines.append("")
    rule_count = rng.randint(1, 4)
    for rule_index in range(rule_count):
        factor_count = rng.randint(1, 4)
        factors = [
            "(r%d $x)" % rng.randrange(relation_count)
            for _ in range(factor_count)
        ]
        heads = ["(out%d $x)" % rule_index]
        if rng.randrange(2):
            heads.append("(mirror%d $x)" % rule_index)
        source_priority = (
            str(rng.randrange(10))
            if rng.randrange(2)
            else "(source %d)" % rng.randrange(10)
        )
        lines.extend(
            [
                "(exec %s" % source_priority,
                "  (, %s)" % " ".join(factors),
                "  (, %s))" % " ".join(heads),
                "",
            ]
        )
    return "\n".join(lines)


def run(seed_count, binary):
    temp_root = os.path.join(REPO, "target", "semi_naive")
    os.makedirs(temp_root, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="semi-naive-random-", dir=temp_root) as root:
        for seed in range(seed_count):
            source_path = os.path.join(root, "%04d.source.mm2" % seed)
            transformed_path = os.path.join(root, "%04d.transformed.mm2" % seed)
            source = generate(seed)
            with open(source_path, "w", encoding="utf-8", newline="\n") as stream:
                stream.write(source)
            with open(
                transformed_path, "w", encoding="utf-8", newline="\n"
            ) as stream:
                stream.write(sexpr.dumps(transform.transform(sexpr.parse(source))))
            output = io.StringIO()
            with contextlib.redirect_stdout(output):
                result = driver.compare(
                    binary,
                    source_path,
                    transformed_path,
                    None,
                    driver.DEFAULT_STEPS,
                    64,
                )
            if result:
                sys.stdout.write(output.getvalue())
                print("FAIL generated seed %d" % seed)
                return 1
    print("OK %d deterministic generated programs" % seed_count)
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seeds", type=int, default=64)
    parser.add_argument("--binary", default=driver.DEFAULT_BINARY)
    args = parser.parse_args()
    if args.seeds <= 0:
        parser.error("--seeds must be positive")
    binary = os.path.abspath(args.binary)
    if not os.access(binary, os.X_OK):
        parser.error("binary is not executable: %s" % binary)
    return run(args.seeds, binary)


if __name__ == "__main__":
    sys.exit(main())
