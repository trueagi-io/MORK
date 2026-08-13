#!/usr/bin/env python3
"""Benchmark naive and transformed MM2 under ProductZipper and leapfrog."""

import argparse
import datetime
import hashlib
import json
import math
import os
import platform
import subprocess
import sys
import tempfile
import time


HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
import driver  # noqa: E402

gen_process_calculus = driver.gen_process_calculus
gen_transitive = driver.gen_transitive


DEFAULT_PZ_BINARY = os.path.join(REPO, "target", "semi_naive", "bin-pz")
DEFAULT_LF_BINARY = os.path.join(REPO, "target", "semi_naive", "bin-lf")
DEFAULT_JSON = os.path.join(REPO, "target", "semi_naive", "semi-naive-four-quadrant.json")
DEFAULT_REPEATS = 3
DEFAULT_NAIVE_TIMEOUT_SECONDS = 15 * 60
DEFAULT_MAX_SOURCE_ROUNDS = 2048

WORKLOAD_SIZES = {
    "process_calculus": (80, 160, 320, 480),
    "transitive": (64, 128, 256, 384),
}
WORKLOAD_ORDER = tuple(WORKLOAD_SIZES)
PROTOCOL_ORDER = ("naive", "transformed")
ENGINE_ORDER = ("pz", "lf")
COUNTER_FIELDS = ("steps", "unifications", "writes", "transitions")
CROSS_ENGINE_FIELDS = ("steps", "unifications", "writes", "rounds")


class BenchmarkRefusal(ValueError):
    pass


def positive_integer(value):
    parsed = int(value)
    if parsed <= 0:
        raise argparse.ArgumentTypeError("value must be positive")
    return parsed


def positive_float(value):
    parsed = float(value)
    if not math.isfinite(parsed) or parsed <= 0:
        raise argparse.ArgumentTypeError("value must be positive")
    return parsed


def unique(values, reason):
    if len(values) != len(set(values)):
        raise BenchmarkRefusal(reason)
    return values


def case_specs(workloads, sizes):
    workloads = unique(list(workloads or WORKLOAD_ORDER), "DUPLICATE_WORKLOAD")
    if sizes is not None:
        sizes = unique(list(sizes), "DUPLICATE_SIZE")
        if len(workloads) != 1:
            raise BenchmarkRefusal("SIZES_REQUIRE_ONE_WORKLOAD")
        return [(workloads[0], size) for size in sizes]
    return [
        (workload, size)
        for workload in workloads
        for size in WORKLOAD_SIZES[workload]
    ]


def cell_specs(protocols, engines):
    protocols = unique(list(protocols or PROTOCOL_ORDER), "DUPLICATE_PROTOCOL")
    engines = unique(list(engines or ENGINE_ORDER), "DUPLICATE_ENGINE")
    return [
        (protocol, engine)
        for protocol in PROTOCOL_ORDER
        if protocol in protocols
        for engine in ENGINE_ORDER
        if engine in engines
    ]


def interleaved_schedule(cells, repeats):
    if not cells:
        raise BenchmarkRefusal("NO_BENCHMARK_CELLS")
    for repeat in range(repeats):
        offset = repeat % len(cells)
        for index in range(len(cells)):
            yield repeat, cells[(offset + index) % len(cells)]


def sha256_file(path):
    digest = hashlib.sha256()
    with open(path, "rb") as stream:
        while True:
            chunk = stream.read(1024 * 1024)
            if not chunk:
                return digest.hexdigest()
            digest.update(chunk)


def validate_binaries(binaries, engines):
    selected = {engine: os.path.abspath(binaries[engine]) for engine in engines}
    for engine, binary in selected.items():
        if not os.access(binary, os.X_OK):
            raise BenchmarkRefusal(
                "BINARY_NOT_EXECUTABLE: %s=%s" % (engine, binary)
            )
    if set(selected) == set(ENGINE_ORDER):
        if os.path.samefile(selected["pz"], selected["lf"]):
            raise BenchmarkRefusal("ENGINE_BINARIES_SAME_FILE")
        if sha256_file(selected["pz"]) == sha256_file(selected["lf"]):
            raise BenchmarkRefusal("ENGINE_BINARIES_IDENTICAL")
    return selected


def generate_case(root, workload, size):
    source_root = os.path.join(root, "source")
    if workload == "process_calculus":
        source = gen_process_calculus.generate(source_root, ((size, size),))[0]
        instance = "%d+%d" % (size, size)
        required = source[: -len(".source.mm2")] + ".required"
    elif workload == "transitive":
        source = gen_transitive.generate(source_root, (size,))[0]
        instance = str(size)
        required = None
    else:
        raise BenchmarkRefusal("UNSUPPORTED_WORKLOAD: %s" % workload)

    transformed = os.path.join(root, "transformed.mm2")
    driver.transform_program(source, transformed)
    driver.assert_no_bare_top_level_variable_facts(transformed)
    return {
        "workload": workload,
        "size": size,
        "instance": instance,
        "source": source,
        "transformed": transformed,
        "required": required,
    }


def sample_from_result(result, projection, wall_ns, rounds):
    sample = {field: result[field] for field in COUNTER_FIELDS}
    sample.update(
        {
            "engine_ms": result["milliseconds"],
            "wall_ns": wall_ns,
            "rounds": rounds,
            "projection": projection,
        }
    )
    return sample


def run_naive_once(binary, case, workdir, steps, max_rounds, timeout_seconds):
    started = time.perf_counter_ns()
    deadline_ns = started + int(timeout_seconds * 1_000_000_000)
    result = driver.run_source_protocol(
        binary,
        case["source"],
        workdir,
        steps,
        max_rounds,
        deadline_ns=deadline_ns,
    )
    wall_ns = time.perf_counter_ns() - started
    if wall_ns > int(timeout_seconds * 1_000_000_000):
        raise subprocess.TimeoutExpired("repeated-evaluation protocol", timeout_seconds)
    return sample_from_result(
        result,
        result["projection"],
        wall_ns,
        result["rounds"],
    )


def run_transformed_once(binary, case, workdir, steps):
    started = time.perf_counter_ns()
    result = driver.run_program(
        binary,
        case["transformed"],
        os.path.join(workdir, "transformed.space"),
        steps,
    )
    wall_ns = time.perf_counter_ns() - started
    projection = driver.sorted_projection(result["dump"], transformed=True)
    return sample_from_result(result, projection, wall_ns, 1)


def run_cell_once(
    protocol,
    binary,
    case,
    workdir,
    steps,
    max_rounds,
    naive_timeout_seconds,
):
    if protocol == "naive":
        return run_naive_once(
            binary,
            case,
            workdir,
            steps,
            max_rounds,
            naive_timeout_seconds,
        )
    if protocol == "transformed":
        return run_transformed_once(binary, case, workdir, steps)
    raise BenchmarkRefusal("UNSUPPORTED_PROTOCOL: %s" % protocol)


def counter_bytes(sample):
    fields = COUNTER_FIELDS + ("rounds",)
    return "\n".join(
        "%s=%d" % (field, sample[field]) for field in fields
    ).encode("ascii")


def verify_projection(case, reference, sample, context):
    projection = sample["projection"]
    if case["required"] is not None:
        with open(case["required"], "rb") as stream:
            required = set(stream.read().splitlines())
        missing = sorted(required - set(projection.splitlines()))
        if missing:
            raise RuntimeError(
                "REQUIRED_PROJECTION_MISSING: %s: %r" % (context, missing[0])
            )
    if reference is None:
        return projection
    if projection != reference:
        line, expected, actual = driver.first_difference(reference, projection)
        raise RuntimeError(
            "CROSS_CELL_PROJECTION_MISMATCH: %s line %d: %r != %r"
            % (context, line, expected, actual)
        )
    return reference


def verify_counter_repeat(samples, sample, context):
    if samples and counter_bytes(samples[0]) != counter_bytes(sample):
        raise RuntimeError(
            "NONDETERMINISTIC_COUNTERS: %s: %r != %r"
            % (context, counter_bytes(samples[0]), counter_bytes(sample))
        )


def public_sample(sample, repeat):
    return {
        "repeat": repeat + 1,
        **{field: sample[field] for field in COUNTER_FIELDS},
        "rounds": sample["rounds"],
        "engine_ms": sample["engine_ms"],
        "wall_ns": sample["wall_ns"],
        "wall_ms": sample["wall_ns"] / 1_000_000,
    }


def completed_row(case, protocol, engine, samples, repeats):
    if len(samples) != repeats:
        raise RuntimeError(
            "INCOMPLETE_REPEATS: %s %s %s: %d != %d"
            % (case["workload"], case["instance"], protocol, len(samples), repeats)
        )
    first = samples[0]
    wall_index = min(
        range(len(samples)), key=lambda index: samples[index]["wall_ns"]
    )
    engine_index = min(
        range(len(samples)), key=lambda index: samples[index]["engine_ms"]
    )
    return {
        "workload": case["workload"],
        "size": case["size"],
        "instance": case["instance"],
        "protocol": protocol,
        "protocol_label": protocol_label(protocol),
        "engine": engine,
        "status": "measured",
        **{field: first[field] for field in COUNTER_FIELDS},
        "rounds": first["rounds"],
        "engine_ms": samples[engine_index]["engine_ms"],
        "wall_ns": samples[wall_index]["wall_ns"],
        "wall_ms": samples[wall_index]["wall_ns"] / 1_000_000,
        "selected_engine_repeat": engine_index + 1,
        "selected_wall_repeat": wall_index + 1,
        "projection_bytes": len(first["projection"]),
        "projection_lines": first["projection"].count(b"\n"),
        "projection_sha256": hashlib.sha256(first["projection"]).hexdigest(),
        "samples": [
            public_sample(sample, repeat)
            for repeat, sample in enumerate(samples)
        ],
    }


def skipped_row(case, protocol, engine, reason):
    return {
        "workload": case["workload"],
        "size": case["size"],
        "instance": case["instance"],
        "protocol": protocol,
        "protocol_label": protocol_label(protocol),
        "engine": engine,
        "status": "skipped",
        "reason": reason,
        "samples": [],
    }


def verify_cross_engine_counters(rows):
    by_cell = {(row["protocol"], row["engine"]): row for row in rows}
    for protocol in PROTOCOL_ORDER:
        left = by_cell.get((protocol, "pz"))
        right = by_cell.get((protocol, "lf"))
        if left is None or right is None:
            continue
        if left["status"] != "measured" or right["status"] != "measured":
            continue
        for field in CROSS_ENGINE_FIELDS:
            if left[field] != right[field]:
                raise RuntimeError(
                    "CROSS_ENGINE_COUNTER_MISMATCH: %s %s: pz %s=%d, lf %s=%d"
                    % (
                        left["workload"],
                        left["instance"],
                        field,
                        left[field],
                        field,
                        right[field],
                    )
                )


def benchmark_case(
    case,
    cells,
    binaries,
    repeats,
    steps,
    max_rounds,
    naive_timeout_seconds,
    work_root,
):
    samples = {cell: [] for cell in cells}
    skipped = {}
    projection = None
    for repeat, (protocol, engine) in interleaved_schedule(cells, repeats):
        cell = (protocol, engine)
        if cell in skipped:
            continue
        context = "%s %s %s %s repeat %d" % (
            case["workload"],
            case["instance"],
            protocol_label(protocol),
            engine.upper(),
            repeat + 1,
        )
        print("RUN %s" % context, flush=True)
        with tempfile.TemporaryDirectory(
            prefix="%s-%s-%02d-" % (protocol, engine, repeat + 1),
            dir=work_root,
        ) as workdir:
            try:
                sample = run_cell_once(
                    protocol,
                    binaries[engine],
                    case,
                    workdir,
                    steps,
                    max_rounds,
                    naive_timeout_seconds,
                )
            except subprocess.TimeoutExpired:
                if protocol != "naive":
                    raise
                reason = (
                    "repeated-evaluation protocol exceeded %g seconds in repeat %d"
                    % (naive_timeout_seconds, repeat + 1)
                )
                samples[cell] = []
                skipped[cell] = reason
                print("SKIP %s: %s" % (context, reason), flush=True)
                continue

        projection = verify_projection(case, projection, sample, context)
        verify_counter_repeat(samples[cell], sample, context)
        samples[cell].append(sample)
        print(
            "OK %s steps=%d unifications=%d writes=%d transitions=%d "
            "engine_ms=%d wall_ms=%.3f rounds=%d"
            % (
                context,
                sample["steps"],
                sample["unifications"],
                sample["writes"],
                sample["transitions"],
                sample["engine_ms"],
                sample["wall_ns"] / 1_000_000,
                sample["rounds"],
            ),
            flush=True,
        )

    rows = []
    for protocol, engine in cells:
        cell = (protocol, engine)
        if cell in skipped:
            rows.append(skipped_row(case, protocol, engine, skipped[cell]))
        else:
            rows.append(
                completed_row(case, protocol, engine, samples[cell], repeats)
            )
    verify_cross_engine_counters(rows)
    return rows


def protocol_label(protocol):
    if protocol == "naive":
        return "naive repeated-evaluation protocol"
    if protocol == "transformed":
        return "transformed single run"
    raise BenchmarkRefusal("UNSUPPORTED_PROTOCOL: %s" % protocol)


def format_integer(value):
    return "-" if value is None else format(value, ",d")


def render_table(rows, repeats):
    lines = [
        "| Workload | Instance | Protocol | Engine | Rounds | Steps | "
        "Unifications | Writes | Transitions | Engine ms min-of-%d | "
        "Protocol wall ms min-of-%d |" % (repeats, repeats),
        "| :--- | :--- | :--- | :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |",
    ]
    for row in rows:
        if row["status"] == "skipped":
            values = ["-"] * 7
            protocol = "%s; SKIPPED: %s" % (
                row["protocol_label"],
                row["reason"],
            )
        else:
            values = [
                format_integer(row["rounds"]),
                format_integer(row["steps"]),
                format_integer(row["unifications"]),
                format_integer(row["writes"]),
                format_integer(row["transitions"]),
                format_integer(row["engine_ms"]),
                "%.3f" % row["wall_ms"],
            ]
            protocol = row["protocol_label"]
        lines.append(
            "| %s | %s | %s | %s | %s |"
            % (
                row["workload"],
                row["instance"],
                protocol,
                row["engine"].upper(),
                " | ".join(values),
            )
        )
    return "\n".join(lines) + "\n"


def atomic_write_json(path, value):
    directory = os.path.dirname(os.path.abspath(path))
    os.makedirs(directory, exist_ok=True)
    descriptor, temporary = tempfile.mkstemp(
        prefix=".semi-naive-bench-", suffix=".json", dir=directory
    )
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8", newline="\n") as stream:
            json.dump(value, stream, indent=2, sort_keys=True)
            stream.write("\n")
        os.replace(temporary, path)
    except BaseException:
        try:
            os.unlink(temporary)
        except FileNotFoundError:
            pass
        raise


def git_head():
    completed = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=REPO,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
        text=True,
    )
    if completed.returncode != 0:
        raise RuntimeError(
            "GIT_HEAD_UNAVAILABLE: %s" % completed.stderr.strip()
        )
    return completed.stdout.strip()


def artifact(rows, binaries, repeats, timeout_seconds, max_rounds, steps):
    all_measured = all(row["status"] == "measured" for row in rows)
    return {
        "schema": 1,
        "resolved": True,
        "all_measured": all_measured,
        "generated_at_utc": datetime.datetime.now(
            datetime.timezone.utc
        ).isoformat(),
        "git_head": git_head(),
        "host": {
            "platform": platform.platform(),
            "machine": platform.machine(),
            "python": platform.python_version(),
            "logical_cpus": os.cpu_count(),
            "load_average_at_write": os.getloadavg(),
        },
        "binaries": {
            engine: {
                "path": binary,
                "sha256": sha256_file(binary),
            }
            for engine, binary in binaries.items()
        },
        "methodology": {
            "repeats": repeats,
            "schedule": "rotated interleaving by repeat within each case",
            "wall_estimator": "minimum end-to-end wall across repeats",
            "engine_ms": "minimum engine timer across repeats",
            "counters": "steps, unifications, writes, and transitions must be byte-stable across repeats",
            "naive": "external repeated-evaluation fixed-point protocol; engine_ms is summed across rounds",
            "transformed": "one mork run to quiescence per repeat",
            "naive_timeout_seconds_per_repeat": timeout_seconds,
            "max_source_rounds": max_rounds,
            "step_limit_per_mork_run": steps,
            "binary_build": "RUSTFLAGS='-C target-cpu=native -Awarnings -C link-arg=-fuse-ld=mold' cargo +nightly build --release -p mork --bin mork",
        },
        "results": rows,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pz-binary", default=DEFAULT_PZ_BINARY)
    parser.add_argument("--lf-binary", default=DEFAULT_LF_BINARY)
    parser.add_argument(
        "--workload", action="append", choices=WORKLOAD_ORDER, dest="workloads"
    )
    parser.add_argument("--size", action="append", type=positive_integer, dest="sizes")
    parser.add_argument(
        "--protocol", action="append", choices=PROTOCOL_ORDER, dest="protocols"
    )
    parser.add_argument(
        "--engine", action="append", choices=ENGINE_ORDER, dest="engines"
    )
    parser.add_argument("--repeats", type=positive_integer, default=DEFAULT_REPEATS)
    parser.add_argument(
        "--naive-timeout-seconds",
        type=positive_float,
        default=DEFAULT_NAIVE_TIMEOUT_SECONDS,
    )
    parser.add_argument(
        "--max-source-rounds",
        type=positive_integer,
        default=DEFAULT_MAX_SOURCE_ROUNDS,
    )
    parser.add_argument("--steps", type=positive_integer, default=driver.DEFAULT_STEPS)
    parser.add_argument("--json", default=DEFAULT_JSON)
    args = parser.parse_args()

    try:
        specs = case_specs(args.workloads, args.sizes)
        cells = cell_specs(args.protocols, args.engines)
        selected_engines = unique(
            [engine for engine in ENGINE_ORDER if any(cell[1] == engine for cell in cells)],
            "DUPLICATE_ENGINE",
        )
        binaries = validate_binaries(
            {"pz": args.pz_binary, "lf": args.lf_binary}, selected_engines
        )

        temp_root = os.path.join(REPO, "target", "semi_naive")
        os.makedirs(temp_root, exist_ok=True)
        rows = []
        with tempfile.TemporaryDirectory(
            prefix="semi-naive-bench-", dir=temp_root
        ) as benchmark_root:
            for workload, size in specs:
                case_root = os.path.join(
                    benchmark_root, "%s-%d" % (workload, size)
                )
                os.makedirs(case_root)
                case = generate_case(case_root, workload, size)
                rows.extend(
                    benchmark_case(
                        case,
                        cells,
                        binaries,
                        args.repeats,
                        args.steps,
                        args.max_source_rounds,
                        args.naive_timeout_seconds,
                        case_root,
                    )
                )

        result = artifact(
            rows,
            binaries,
            args.repeats,
            args.naive_timeout_seconds,
            args.max_source_rounds,
            args.steps,
        )
        atomic_write_json(args.json, result)
        print(render_table(rows, args.repeats), end="")
        print("WROTE %s" % os.path.relpath(args.json, REPO))
        return 0
    except (BenchmarkRefusal, OSError, RuntimeError, subprocess.SubprocessError) as error:
        print("ERROR: %s" % error, file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
