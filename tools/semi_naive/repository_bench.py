#!/usr/bin/env python3
"""Measure repository-corpus source and transformed counters under both engines."""

import argparse
import contextlib
import io
import os
import sys
import tempfile


HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
import bench
import driver


DEFAULT_REPEATS = 3
COUNTER_FIELDS = ("steps", "unifications", "writes", "transitions")


def counter_record(result):
    record = {field: result[field] for field in COUNTER_FIELDS}
    if "rounds" in result:
        record["rounds"] = result["rounds"]
    return record


def verify_repeat(reference, actual, context):
    for arm in ("source", "transformed"):
        expected = counter_record(reference[arm])
        observed = counter_record(actual[arm])
        if observed != expected:
            raise RuntimeError(
                "NONDETERMINISTIC_COUNTERS: %s %s: %r != %r"
                % (context, arm, expected, observed)
            )
        projection_key = arm + "_projection"
        if actual[projection_key] != reference[projection_key]:
            raise RuntimeError(
                "NONDETERMINISTIC_PROJECTION: %s %s" % (context, arm)
            )


def verdict(source, transformed, source_mode="persistent"):
    if source_mode == "natural":
        return "BOUNDED_SOURCE"
    if source.get("rounds", 0) <= 2:
        return "NEUTRAL_SHORT"
    if transformed["unifications"] < source["unifications"]:
        return "FEWER_UNIFICATIONS"
    if transformed["unifications"] == source["unifications"]:
        return "NEUTRAL_COUNTER"
    return "OVERHEAD"


def run_case(case, binaries, repeats, max_source_rounds):
    samples = {engine: [] for engine in bench.ENGINE_ORDER}
    for repeat in range(1, repeats + 1):
        for engine in bench.ENGINE_ORDER:
            captured = io.StringIO()
            with contextlib.redirect_stdout(captured):
                failed, result = driver.evaluate_case(
                    binaries[engine],
                    case.source,
                    case.transformed,
                    case.expected,
                    driver.DEFAULT_STEPS,
                    max_source_rounds,
                    case.required,
                    engine,
                    case.source_mode,
                    case.source_steps,
                )
            if failed:
                raise RuntimeError(
                    "ORACLE_FAILURE: %s %s repeat %d\n%s"
                    % (case.label, engine, repeat, captured.getvalue())
                )
            if samples[engine]:
                verify_repeat(
                    samples[engine][0],
                    result,
                    "%s %s repeat %d" % (case.label, engine, repeat),
                )
            samples[engine].append(result)

    first = {engine: samples[engine][0] for engine in bench.ENGINE_ORDER}
    captured = io.StringIO()
    with contextlib.redirect_stdout(captured):
        failed = driver.compare_cross_engine(
            "pz",
            first["pz"],
            "lf",
            first["lf"],
            case.engine_specific_fields,
        )
    if failed:
        raise RuntimeError(
            "CROSS_ENGINE_FAILURE: %s\n%s" % (case.label, captured.getvalue())
        )

    return {
        "case": case.label,
        "source_mode": case.source_mode,
        "source_steps": case.source_steps,
        "engine_specific_fields": list(case.engine_specific_fields),
        "verdict": verdict(
            first["pz"]["source"],
            first["pz"]["transformed"],
            case.source_mode,
        ),
        "engines": {
            engine: {
                "source": counter_record(first[engine]["source"]),
                "transformed": counter_record(first[engine]["transformed"]),
            }
            for engine in bench.ENGINE_ORDER
        },
    }


def render_table(rows):
    lines = [
        "| Case | Engine | Source rounds | Source steps | Source unifications | "
        "Source writes | Source transitions | Transformed steps | "
        "Transformed unifications | Transformed writes | Transformed transitions | "
        "Verdict |",
        "| :--- | :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | :--- |",
    ]
    for row in rows:
        for engine in bench.ENGINE_ORDER:
            source = row["engines"][engine]["source"]
            transformed = row["engines"][engine]["transformed"]
            lines.append(
                "| %s | %s | %s | %d | %d | %d | %d | %d | %d | %d | %d | %s |"
                % (
                    row["case"],
                    engine.upper(),
                    source.get("rounds", "-"),
                    source["steps"],
                    source["unifications"],
                    source["writes"],
                    source["transitions"],
                    transformed["steps"],
                    transformed["unifications"],
                    transformed["writes"],
                    transformed["transitions"],
                    row["verdict"],
                )
            )
    return "\n".join(lines) + "\n"


def artifact(rows, binaries, repeats):
    return {
        "schema": 1,
        "git_head": bench.git_head(),
        "repeats": repeats,
        "binary_sha256": {
            engine: bench.sha256_file(binary)
            for engine, binary in binaries.items()
        },
        "results": rows,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pz-binary", default=bench.DEFAULT_PZ_BINARY)
    parser.add_argument("--lf-binary", default=bench.DEFAULT_LF_BINARY)
    parser.add_argument("--repeats", type=bench.positive_integer, default=DEFAULT_REPEATS)
    parser.add_argument(
        "--max-source-rounds",
        type=bench.positive_integer,
        default=bench.DEFAULT_MAX_SOURCE_ROUNDS,
    )
    parser.add_argument("--json")
    args = parser.parse_args()

    try:
        binaries = bench.validate_binaries(
            {"pz": args.pz_binary, "lf": args.lf_binary},
            bench.ENGINE_ORDER,
        )
        temp_root = os.path.join(REPO, "target", "semi_naive")
        os.makedirs(temp_root, exist_ok=True)
        with tempfile.TemporaryDirectory(
            prefix="semi-naive-repository-bench-", dir=temp_root
        ) as workdir:
            cases = driver.discover_repository_cases(
                os.path.join(workdir, "transforms")
            )
            rows = [
                run_case(case, binaries, args.repeats, args.max_source_rounds)
                for case in cases
            ]
        if args.json:
            bench.atomic_write_json(
                os.path.abspath(args.json), artifact(rows, binaries, args.repeats)
            )
        sys.stdout.write(render_table(rows))
        print(
            "BENCHMARKED %d cases x 2 engines x %d repeats; "
            "projections and counters deterministic"
            % (len(rows), args.repeats)
        )
        return 0
    except (bench.BenchmarkRefusal, OSError, RuntimeError, ValueError) as error:
        print("ERROR: %s" % error, file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
