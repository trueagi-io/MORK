#!/usr/bin/env python3
"""Validate and analyze the complete semi-naive four-quadrant benchmark."""

import argparse
import json
import math
import os
import statistics
import sys
import tempfile

import bench


EXPECTED_CASES = {
    (workload, size)
    for workload, sizes in bench.WORKLOAD_SIZES.items()
    for size in sizes
}
EXPECTED_CELLS = {
    (workload, size, protocol, engine)
    for workload, size in EXPECTED_CASES
    for protocol in bench.PROTOCOL_ORDER
    for engine in bench.ENGINE_ORDER
}
ROW_COUNTER_FIELDS = bench.COUNTER_FIELDS + ("rounds",)


class AnalysisRefusal(ValueError):
    pass


def refuse(reason, detail=None):
    if detail is None:
        raise AnalysisRefusal(reason)
    raise AnalysisRefusal("%s: %s" % (reason, detail))


def read_artifact(path):
    try:
        with open(path, "r", encoding="utf-8") as stream:
            value = json.load(stream)
    except (OSError, json.JSONDecodeError) as error:
        refuse("ARTIFACT_READ_FAILED", "%s: %s" % (path, error))
    if not isinstance(value, dict):
        refuse("ARTIFACT_NOT_OBJECT", path)
    return value


def binary_hashes(artifact, path):
    binaries = artifact.get("binaries")
    if not isinstance(binaries, dict) or set(binaries) != set(bench.ENGINE_ORDER):
        refuse("ARTIFACT_REQUIRES_BOTH_ENGINES", path)
    hashes = {}
    for engine in bench.ENGINE_ORDER:
        metadata = binaries.get(engine)
        digest = metadata.get("sha256") if isinstance(metadata, dict) else None
        if not isinstance(digest, str) or len(digest) != 64:
            refuse("INVALID_BINARY_SHA256", "%s %s" % (path, engine))
        hashes[engine] = digest
    if hashes["pz"] == hashes["lf"]:
        refuse("ENGINE_BINARIES_IDENTICAL", path)
    return hashes


def validate_sample(row, sample, expected_repeat, context):
    if not isinstance(sample, dict):
        refuse("INVALID_SAMPLE", context)
    if sample.get("repeat") != expected_repeat:
        refuse("INVALID_REPEAT_INDEX", context)
    for field in ROW_COUNTER_FIELDS:
        if sample.get(field) != row.get(field):
            refuse(
                "NONDETERMINISTIC_COUNTERS",
                "%s %s sample=%r row=%r"
                % (context, field, sample.get(field), row.get(field)),
            )
    for field in ("engine_ms", "wall_ns"):
        value = sample.get(field)
        if not isinstance(value, int) or value < 0:
            refuse("INVALID_SAMPLE_TIMER", "%s %s" % (context, field))


def validate_row(row, repeats, context):
    if not isinstance(row, dict):
        refuse("INVALID_RESULT_ROW", context)
    if row.get("status") != "measured":
        refuse(
            "UNMEASURED_CELL",
            "%s: %s" % (context, row.get("reason", row.get("status"))),
        )
    key = tuple(row.get(field) for field in ("workload", "size", "protocol", "engine"))
    if key not in EXPECTED_CELLS:
        refuse("UNEXPECTED_CELL", "%s: %r" % (context, key))
    if row.get("protocol_label") != bench.protocol_label(row["protocol"]):
        refuse("INVALID_PROTOCOL_LABEL", context)
    for field in ROW_COUNTER_FIELDS:
        value = row.get(field)
        if not isinstance(value, int) or value < 0:
            refuse("INVALID_COUNTER", "%s %s" % (context, field))
    for field in ("projection_bytes", "projection_lines"):
        value = row.get(field)
        if not isinstance(value, int) or value <= 0:
            refuse("INVALID_PROJECTION_SIZE", "%s %s" % (context, field))
    projection_hash = row.get("projection_sha256")
    if not isinstance(projection_hash, str) or len(projection_hash) != 64:
        refuse("INVALID_PROJECTION_SHA256", context)

    samples = row.get("samples")
    if not isinstance(samples, list) or len(samples) != repeats:
        refuse(
            "INCOMPLETE_REPEATS",
            "%s: %r != %d"
            % (context, len(samples) if isinstance(samples, list) else None, repeats),
        )
    for repeat, sample in enumerate(samples, 1):
        validate_sample(row, sample, repeat, context)
    if row.get("engine_ms") != min(sample["engine_ms"] for sample in samples):
        refuse("ENGINE_MS_NOT_MINIMUM", context)
    if row.get("wall_ns") != min(sample["wall_ns"] for sample in samples):
        refuse("WALL_NOT_MINIMUM", context)
    if not math.isclose(
        row.get("wall_ms", math.nan),
        row["wall_ns"] / 1_000_000,
        rel_tol=0,
        abs_tol=1e-9,
    ):
        refuse("WALL_MS_MISMATCH", context)
    return key


def load_and_validate(paths):
    if not paths:
        refuse("NO_ARTIFACTS")
    rows = {}
    expected_hashes = None
    sources = []
    for path in paths:
        absolute = os.path.abspath(path)
        artifact = read_artifact(absolute)
        if artifact.get("schema") != 1:
            refuse("UNSUPPORTED_BENCHMARK_SCHEMA", absolute)
        if artifact.get("resolved") is not True:
            refuse("UNRESOLVED_BENCHMARK", absolute)
        if artifact.get("all_measured") is not True:
            refuse("BENCHMARK_HAS_SKIPS", absolute)
        methodology = artifact.get("methodology")
        if not isinstance(methodology, dict) or methodology.get("repeats") != 3:
            refuse("BENCHMARK_REQUIRES_MIN_OF_3", absolute)
        hashes = binary_hashes(artifact, absolute)
        if expected_hashes is None:
            expected_hashes = hashes
        elif hashes != expected_hashes:
            refuse("MIXED_BINARY_HASHES", absolute)
        artifact_rows = artifact.get("results")
        if not isinstance(artifact_rows, list):
            refuse("INVALID_RESULTS", absolute)
        for index, row in enumerate(artifact_rows):
            context = "%s result %d" % (absolute, index + 1)
            key = validate_row(row, 3, context)
            if key in rows:
                refuse("DUPLICATE_CELL", "%r" % (key,))
            rows[key] = row
        sources.append(
            {
                "path": absolute,
                "sha256": bench.sha256_file(absolute),
                "git_head": artifact.get("git_head"),
            }
        )

    observed = set(rows)
    if observed != EXPECTED_CELLS:
        missing = sorted(EXPECTED_CELLS - observed)
        extra = sorted(observed - EXPECTED_CELLS)
        refuse("INCOMPLETE_MATRIX", "missing=%r extra=%r" % (missing, extra))
    validate_case_agreement(rows)
    return rows, expected_hashes, sources


def validate_case_agreement(rows):
    for workload, size in sorted(EXPECTED_CASES):
        case_rows = [
            rows[(workload, size, protocol, engine)]
            for protocol in bench.PROTOCOL_ORDER
            for engine in bench.ENGINE_ORDER
        ]
        projection = {
            (row["projection_sha256"], row["projection_bytes"], row["projection_lines"])
            for row in case_rows
        }
        if len(projection) != 1:
            refuse("CROSS_CELL_PROJECTION_MISMATCH", "%s %d" % (workload, size))
        for protocol in bench.PROTOCOL_ORDER:
            left = rows[(workload, size, protocol, "pz")]
            right = rows[(workload, size, protocol, "lf")]
            for field in bench.CROSS_ENGINE_FIELDS:
                if left[field] != right[field]:
                    refuse(
                        "CROSS_ENGINE_COUNTER_MISMATCH",
                        "%s %d %s %s" % (workload, size, protocol, field),
                    )


def power_fit(points):
    if len(points) < 2 or any(x <= 0 or y <= 0 for x, y in points):
        refuse("POWER_FIT_REQUIRES_POSITIVE_POINTS", repr(points))
    xs = [math.log(x) for x, _ in points]
    ys = [math.log(y) for _, y in points]
    fit = statistics.linear_regression(xs, ys)
    correlation = statistics.correlation(xs, ys)
    return {
        "exponent": fit.slope,
        "coefficient": math.exp(fit.intercept),
        "r_squared": correlation * correlation,
    }


def adjacent_growth(points):
    growth = []
    for (left_size, left_value), (right_size, right_value) in zip(points, points[1:]):
        raw = right_value / left_value
        size_ratio = right_size / left_size
        growth.append(
            {
                "from_size": left_size,
                "to_size": right_size,
                "size_ratio": size_ratio,
                "raw_ratio": raw,
                "per_doubling": raw ** (math.log(2) / math.log(size_ratio)),
            }
        )
    return growth


def ratio(numerator, denominator, label):
    if denominator <= 0:
        refuse("NONPOSITIVE_RATIO_DENOMINATOR", label)
    return numerator / denominator


def analyze(rows, binary_hashes, sources):
    scaling = {}
    projection_scaling = {}
    for workload in bench.WORKLOAD_ORDER:
        sizes = bench.WORKLOAD_SIZES[workload]
        scaling[workload] = {}
        for engine in bench.ENGINE_ORDER:
            points = [
                (
                    size,
                    rows[(workload, size, "transformed", engine)]["transitions"],
                )
                for size in sizes
            ]
            scaling[workload][engine] = {
                "points": [
                    {"size": size, "transitions": transitions}
                    for size, transitions in points
                ],
                "fit": power_fit(points),
                "adjacent_growth": adjacent_growth(points),
            }
        projection_points = [
            (
                size,
                rows[(workload, size, "transformed", "pz")]["projection_bytes"],
            )
            for size in sizes
        ]
        projection_scaling[workload] = {
            "points": [
                {"size": size, "bytes": projection_bytes}
                for size, projection_bytes in projection_points
            ],
            "fit": power_fit(projection_points),
        }

    case = "process_calculus", 320
    naive_pz = rows[case + ("naive", "pz")]["engine_ms"]
    naive_lf = rows[case + ("naive", "lf")]["engine_ms"]
    transformed_pz = rows[case + ("transformed", "pz")]["engine_ms"]
    transformed_lf = rows[case + ("transformed", "lf")]["engine_ms"]
    composition = {
        "workload": case[0],
        "size": case[1],
        "engine_ms": {
            "naive_pz": naive_pz,
            "naive_lf": naive_lf,
            "transformed_pz": transformed_pz,
            "transformed_lf": transformed_lf,
        },
        "ratios": {
            "stock_to_combined": ratio(naive_pz, transformed_lf, "stock_to_combined"),
            "same_lf_naive_to_transformed": ratio(
                naive_lf, transformed_lf, "same_lf_naive_to_transformed"
            ),
            "same_pz_naive_to_transformed": ratio(
                naive_pz, transformed_pz, "same_pz_naive_to_transformed"
            ),
            "transformed_pz_to_lf": ratio(
                transformed_pz, transformed_lf, "transformed_pz_to_lf"
            ),
        },
    }
    return {
        "schema": 1,
        "benchmark_sources": sources,
        "binary_sha256": binary_hashes,
        "validation": {
            "cells": len(rows),
            "cases": len(EXPECTED_CASES),
            "all_measured": True,
            "cross_cell_projection_agreement": True,
            "cross_engine_counter_agreement": [
                "steps",
                "unifications",
                "writes",
                "rounds",
            ],
        },
        "scaling": scaling,
        "projection_scaling": projection_scaling,
        "composition_at_process_calculus_320": composition,
    }


def render_analysis(analysis):
    lines = [
        "VALIDATED %d cells across %d cases; all projections agree"
        % (
            analysis["validation"]["cells"],
            analysis["validation"]["cases"],
        )
    ]
    for workload in bench.WORKLOAD_ORDER:
        for engine in bench.ENGINE_ORDER:
            data = analysis["scaling"][workload][engine]
            growth = ", ".join(
                "%d->%d %.6fx"
                % (item["from_size"], item["to_size"], item["per_doubling"])
                for item in data["adjacent_growth"]
            )
            lines.append(
                "%s transformed %s transitions: exponent=%.6f R^2=%.9f; "
                "per-doubling=%s"
                % (
                    workload,
                    engine.upper(),
                    data["fit"]["exponent"],
                    data["fit"]["r_squared"],
                    growth,
                )
            )
        projection = analysis["projection_scaling"][workload]["fit"]
        lines.append(
            "%s projection bytes: exponent=%.6f R^2=%.9f"
            % (workload, projection["exponent"], projection["r_squared"])
        )
    composition = analysis["composition_at_process_calculus_320"]
    lines.append(
        "process_calculus 320+320 engine-ms ratios: stock-to-combined=%.6fx; "
        "same-LF-naive-to-transformed=%.6fx; same-PZ-naive-to-transformed=%.6fx; "
        "transformed-PZ-to-LF=%.6fx"
        % (
            composition["ratios"]["stock_to_combined"],
            composition["ratios"]["same_lf_naive_to_transformed"],
            composition["ratios"]["same_pz_naive_to_transformed"],
            composition["ratios"]["transformed_pz_to_lf"],
        )
    )
    return "\n".join(lines) + "\n"


def atomic_write_text(path, content):
    directory = os.path.dirname(os.path.abspath(path))
    os.makedirs(directory, exist_ok=True)
    descriptor, temporary = tempfile.mkstemp(
        prefix=".semi-naive-analysis-", suffix=".txt", dir=directory
    )
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8", newline="\n") as stream:
            stream.write(content)
        os.replace(temporary, path)
    except BaseException:
        try:
            os.unlink(temporary)
        except FileNotFoundError:
            pass
        raise


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("artifacts", nargs="+")
    parser.add_argument("--json", dest="json_path")
    parser.add_argument("--text", dest="text_path")
    args = parser.parse_args()

    try:
        rows, hashes, sources = load_and_validate(args.artifacts)
        analysis = analyze(rows, hashes, sources)
        rendered = render_analysis(analysis)
        if args.json_path:
            bench.atomic_write_json(args.json_path, analysis)
        if args.text_path:
            atomic_write_text(args.text_path, rendered)
        sys.stdout.write(rendered)
    except (AnalysisRefusal, RuntimeError) as error:
        print("ERROR: %s" % error, file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
