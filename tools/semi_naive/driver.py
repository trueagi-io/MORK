#!/usr/bin/env python3
"""Compare an MM2 program with a semi-naive transformed program."""

import argparse
from dataclasses import dataclass
import os
import re
import subprocess
import sys
import tempfile
import time


HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
import sexpr

GENERATORS = os.path.join(HERE, "generators")
sys.path.insert(0, GENERATORS)
import gen_process_calculus
import gen_transitive


DEFAULT_BINARY = os.path.join(REPO, "target", "release", "mork")
DEFAULT_STEPS = 1_000_000_000_000_000
REPOSITORY_MANIFEST = os.path.join(HERE, "corpus", "repository", "manifest.tsv")
METRIC_FIELDS = ("steps", "milliseconds", "unifications", "writes", "transitions")
ENGINE_SPECIFIC_COUNTER_FIELDS = ("unifications",)

METRICS_RE = re.compile(
    rb"executing (\d+) steps took (\d+) ms "
    rb"\(unifications (\d+), writes (\d+), transitions (\d+)"
    rb"(?:, max unify \d+)?\)"
)
EXPECTED_SOURCE_STEPS_RE = re.compile(r"^;+\s*@source-steps\s+([0-9]+)\s*$")
BOOKKEEPING_PREFIXES = (
    b"(d0 ",
    b"(d1 ",
    b"(c ",
    b"(t ",
    b"(dc ",
    b"(dn ",
    b"(cand ",
    b"(phase ",
    b"(controller ",
    b"(active)",
)


@dataclass(frozen=True)
class OracleCase:
    label: str
    source: str
    transformed: str
    expected: str | None = None
    required: str | None = None
    source_mode: str = "persistent"
    source_steps: int | None = None
    engine_specific_fields: tuple[str, ...] = ()


@dataclass(frozen=True)
class RepositorySpec:
    label: str
    source: str
    expected: str
    source_mode: str
    source_steps: int | None
    engine_specific_fields: tuple[str, ...]


def capture(command, timeout=None):
    return subprocess.run(
        command,
        cwd=REPO,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
        timeout=timeout,
    )


def parse_metrics(output):
    match = METRICS_RE.search(output)
    if match is None:
        raise ValueError("EXECUTION_METRICS_MISSING")
    steps_run, milliseconds, unifications, writes, transitions = (
        int(value) for value in match.groups()
    )
    return {
        "steps": steps_run,
        "milliseconds": milliseconds,
        "unifications": unifications,
        "writes": writes,
        "transitions": transitions,
    }


def run_program(binary, program, dump_path, steps, timeout=None):
    command = [
        binary,
        "run",
        program,
        "--steps",
        str(steps),
        "--instrumentation",
        "0",
        dump_path,
    ]
    completed = capture(command, timeout=timeout)
    if completed.returncode != 0:
        sys.stderr.buffer.write(completed.stdout)
        raise RuntimeError(
            "%s exited %d" % (os.path.relpath(program, REPO), completed.returncode)
        )

    try:
        result = parse_metrics(completed.stdout)
    except ValueError:
        sys.stderr.buffer.write(completed.stdout)
        raise RuntimeError(
            "%s produced no execution metrics" % os.path.relpath(program, REPO)
        ) from None
    with open(dump_path, "rb") as stream:
        result["dump"] = stream.read()
    return result


def materialize_naive_program(text, rounds):
    forms = sexpr.parse(text)
    facts = [
        form
        for form in forms
        if not (isinstance(form, sexpr.ListExpr) and form and form[0] == "exec")
    ]
    rules = [
        form
        for form in forms
        if isinstance(form, sexpr.ListExpr) and form and form[0] == "exec"
    ]
    materialized = [sexpr.dump(fact) for fact in facts]
    for round_number in range(rounds):
        for rule_number, rule in enumerate(rules):
            if len(rule) != 4:
                raise ValueError("exec must have priority, pattern, and template")
            priority = "(naive r%06d %s q%06d)" % (
                round_number,
                sexpr.dump(rule[1]),
                rule_number,
            )
            materialized.append(
                "(exec %s\n  %s\n  %s)"
                % (priority, sexpr.dump(rule[2]), sexpr.dump(rule[3]))
            )
    return "\n\n".join(materialized) + "\n"


def source_rules(text):
    return [
        sexpr.dump(form)
        for form in sexpr.parse(text)
        if isinstance(form, sexpr.ListExpr) and form and form[0] == "exec"
    ]


def timeout_until(deadline_ns):
    if deadline_ns is None:
        return None
    remaining_ns = deadline_ns - time.perf_counter_ns()
    if remaining_ns <= 0:
        raise subprocess.TimeoutExpired("repeated-evaluation protocol", 0)
    return remaining_ns / 1_000_000_000


def run_source_protocol(
    binary,
    program,
    workdir,
    steps,
    max_rounds,
    deadline_ns=None,
):
    with open(program, "r", encoding="utf-8") as stream:
        rules = source_rules(stream.read())

    totals = {field: 0 for field in METRIC_FIELDS}
    if not rules:
        result = run_program(
            binary,
            program,
            os.path.join(workdir, "source.space"),
            steps,
            timeout=timeout_until(deadline_ns),
        )
        for field in METRIC_FIELDS:
            totals[field] += result[field]
        totals.update(
            {
                "rounds": 1,
                "dump": result["dump"],
                "projection": sorted_projection(result["dump"], transformed=False),
            }
        )
        return totals

    round_program = program
    previous = None
    for round_number in range(1, max_rounds + 1):
        result = run_program(
            binary,
            round_program,
            os.path.join(workdir, "source-%04d.space" % round_number),
            steps,
            timeout=timeout_until(deadline_ns),
        )
        for field in METRIC_FIELDS:
            totals[field] += result[field]
        projection = sorted_projection(result["dump"], transformed=False)
        if projection == previous:
            totals.update(
                {
                    "rounds": round_number,
                    "dump": result["dump"],
                    "projection": projection,
                }
            )
            return totals
        previous = projection

        round_program = os.path.join(workdir, "source-%04d.mm2" % (round_number + 1))
        with open(round_program, "wb") as stream:
            stream.write(result["dump"])
            stream.write(b"\n")
            stream.write("\n\n".join(rules).encode("utf-8"))
            stream.write(b"\n")
    raise RuntimeError(
        "%s did not reach a fixed point in %d source rounds"
        % (os.path.relpath(program, REPO), max_rounds)
    )


def run_source_to_fixpoint(binary, program, workdir, steps, max_rounds):
    with open(program, "r", encoding="utf-8") as stream:
        text = stream.read()
    if not source_rules(text):
        return run_source_protocol(binary, program, workdir, steps, max_rounds)

    pilot = run_source_protocol(binary, program, workdir, steps, max_rounds)

    measured_program = os.path.join(workdir, "source-materialized.mm2")
    with open(measured_program, "w", encoding="utf-8") as stream:
        stream.write(materialize_naive_program(text, pilot["rounds"]))
    measured = run_program(
        binary, measured_program, os.path.join(workdir, "source-measured.space"), steps
    )
    measured_projection = sorted_projection(measured["dump"], transformed=False)
    if measured_projection != pilot["projection"]:
        line, expected, actual = first_difference(
            pilot["projection"], measured_projection
        )
        raise RuntimeError(
            "materialized source diverged from fixed-point pilot at line %d: %r != %r"
            % (line, expected, actual)
        )
    measured["rounds"] = pilot["rounds"]
    return measured


def run_source_natural(binary, program, workdir, steps, source_steps):
    effective_steps = source_steps if source_steps is not None else steps
    result = run_program(
        binary,
        program,
        os.path.join(workdir, "source-natural.space"),
        effective_steps,
    )
    result["projection"] = sorted_projection(
        result["dump"], transformed=False, strip_exec=True
    )
    result["source_mode"] = "natural"
    if source_steps is not None:
        result["step_bound"] = source_steps
    return result


def read_repository_path(relative, field, line_number):
    if os.path.isabs(relative):
        raise ValueError(
            "REPOSITORY_MANIFEST_ABSOLUTE_%s: line %d" % (field, line_number)
        )
    normalized = os.path.normpath(relative)
    if normalized == ".." or normalized.startswith(".." + os.sep):
        raise ValueError(
            "REPOSITORY_MANIFEST_ESCAPES_REPO_%s: line %d"
            % (field, line_number)
        )
    path = os.path.join(REPO, normalized)
    if not os.path.isfile(path):
        raise ValueError(
            "REPOSITORY_MANIFEST_MISSING_%s: line %d: %s"
            % (field, line_number, relative)
        )
    return path


def read_expected_source_steps(path):
    found = None
    with open(path, "r", encoding="utf-8") as stream:
        for line_number, line in enumerate(stream, 1):
            if not line.startswith(";"):
                break
            match = EXPECTED_SOURCE_STEPS_RE.match(line.rstrip("\n"))
            if match is None:
                continue
            if found is not None:
                raise ValueError(
                    "EXPECTED_DUPLICATE_SOURCE_STEPS: %s line %d"
                    % (os.path.relpath(path, REPO), line_number)
                )
            found = int(match.group(1))
    return found


def load_repository_manifest(path=REPOSITORY_MANIFEST):
    specs = []
    labels = set()
    sources = set()
    with open(path, "r", encoding="utf-8") as stream:
        for line_number, raw_line in enumerate(stream, 1):
            line = raw_line.rstrip("\n")
            if not line or line.startswith("#"):
                continue
            fields = line.split("|")
            if len(fields) != 6:
                raise ValueError(
                    "REPOSITORY_MANIFEST_FIELDS: line %d" % line_number
                )
            (
                label,
                source_relative,
                expected_relative,
                source_mode,
                steps_text,
                engine_specific_text,
            ) = fields
            if not label or os.path.normpath(label) != label or label.startswith("."):
                raise ValueError(
                    "REPOSITORY_MANIFEST_LABEL: line %d" % line_number
                )
            if label in labels:
                raise ValueError(
                    "REPOSITORY_MANIFEST_DUPLICATE_LABEL: line %d: %s"
                    % (line_number, label)
                )
            if source_mode not in ("persistent", "natural"):
                raise ValueError(
                    "REPOSITORY_MANIFEST_SOURCE_MODE: line %d: %s"
                    % (line_number, source_mode)
                )
            if steps_text == "-":
                source_steps = None
            else:
                try:
                    source_steps = int(steps_text)
                except ValueError:
                    raise ValueError(
                        "REPOSITORY_MANIFEST_SOURCE_STEPS: line %d: %s"
                        % (line_number, steps_text)
                    ) from None
                if source_steps <= 0:
                    raise ValueError(
                        "REPOSITORY_MANIFEST_SOURCE_STEPS: line %d: %s"
                        % (line_number, steps_text)
                    )
            if source_mode == "persistent" and source_steps is not None:
                raise ValueError(
                    "REPOSITORY_MANIFEST_PERSISTENT_STEPS: line %d" % line_number
                )
            if engine_specific_text == "-":
                engine_specific_fields = ()
            else:
                engine_specific_fields = tuple(engine_specific_text.split(","))
                if (
                    len(engine_specific_fields) != len(set(engine_specific_fields))
                    or not set(engine_specific_fields)
                    <= set(ENGINE_SPECIFIC_COUNTER_FIELDS)
                ):
                    raise ValueError(
                        "REPOSITORY_MANIFEST_ENGINE_SPECIFIC_FIELDS: line %d: %s"
                        % (line_number, engine_specific_text)
                    )
            source = read_repository_path(source_relative, "SOURCE", line_number)
            expected = read_repository_path(
                expected_relative, "EXPECTED", line_number
            )
            recorded_steps = read_expected_source_steps(expected)
            if source_mode == "natural" and source_steps != recorded_steps:
                raise ValueError(
                    "REPOSITORY_MANIFEST_EXPECTED_SOURCE_STEPS: line %d: %r != %r"
                    % (line_number, source_steps, recorded_steps)
                )
            if source_mode == "persistent" and recorded_steps is not None:
                raise ValueError(
                    "REPOSITORY_MANIFEST_PERSISTENT_EXPECTED_STEPS: line %d"
                    % line_number
                )
            if source in sources:
                raise ValueError(
                    "REPOSITORY_MANIFEST_DUPLICATE_SOURCE: line %d: %s"
                    % (line_number, source_relative)
                )
            labels.add(label)
            sources.add(source)
            specs.append(
                RepositorySpec(
                    label,
                    source,
                    expected,
                    source_mode,
                    source_steps,
                    engine_specific_fields,
                )
            )
    if not specs:
        raise ValueError("REPOSITORY_MANIFEST_EMPTY")
    return specs


def sorted_projection(dump, transformed, strip_exec=False):
    projected = []
    for line in dump.splitlines():
        if not line or line.startswith(b";"):
            continue
        if strip_exec and line.startswith(b"(exec "):
            continue
        if transformed and line.startswith(BOOKKEEPING_PREFIXES):
            continue
        if transformed and line.startswith(b"(f ") and line.endswith(b")"):
            line = line[3:-1]
        projected.append(line)
    projected.sort()
    if not projected:
        return b""
    return b"\n".join(projected) + b"\n"


def first_difference(expected, actual):
    expected_lines = expected.splitlines()
    actual_lines = actual.splitlines()
    limit = max(len(expected_lines), len(actual_lines))
    for index in range(limit):
        left = expected_lines[index] if index < len(expected_lines) else b"<missing>"
        right = actual_lines[index] if index < len(actual_lines) else b"<missing>"
        if left != right:
            return index + 1, left, right
    raise AssertionError("different byte strings have no differing line")


def assert_no_bare_top_level_variable_facts(program):
    with open(program, "r", encoding="utf-8") as stream:
        expressions = sexpr.parse(stream.read())
    for form_number, expression in enumerate(expressions, 1):
        if isinstance(expression, sexpr.Atom) and expression.startswith("$"):
            raise ValueError(
                "BARE_TOP_LEVEL_VARIABLE_FACT: %s form %d"
                % (os.path.relpath(program, REPO), form_number)
            )


def display_metrics(label, result):
    details = []
    if "rounds" in result:
        details.append("rounds=%d" % result["rounds"])
    if "step_bound" in result:
        details.append("step-bound=%d" % result["step_bound"])
    suffix = " " + " ".join(details) if details else ""
    print(
        "%s:%s steps=%d unifications=%d writes=%d transitions=%d"
        % (
            label,
            suffix,
            result["steps"],
            result["unifications"],
            result["writes"],
            result["transitions"],
        )
    )


def report_difference(label, expected, actual):
    line, expected_line, actual_line = first_difference(expected, actual)
    print("FAIL %s differs at sorted line %d" % (label, line))
    print("expected: %s" % expected_line.decode("utf-8", errors="replace"))
    print("actual:   %s" % actual_line.decode("utf-8", errors="replace"))


def evaluate_case(
    binary,
    source,
    transformed,
    expected,
    steps,
    max_source_rounds,
    required=None,
    engine_label=None,
    source_mode="persistent",
    source_steps=None,
):
    assert_no_bare_top_level_variable_facts(transformed)
    if source_mode == "persistent" and source_steps is not None:
        raise ValueError("PERSISTENT_SOURCE_STEPS")
    if source_mode not in ("persistent", "natural"):
        raise ValueError("UNSUPPORTED_SOURCE_MODE: %s" % source_mode)
    temp_root = os.path.join(REPO, "target", "semi_naive")
    os.makedirs(temp_root, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="semi-naive-", dir=temp_root) as workdir:
        if source_mode == "persistent":
            source_result = run_source_to_fixpoint(
                binary, source, workdir, steps, max_source_rounds
            )
        else:
            source_result = run_source_natural(
                binary, source, workdir, steps, source_steps
            )
        transformed_result = run_program(
            binary,
            transformed,
            os.path.join(workdir, "transformed.space"),
            steps,
        )

    source_projection = source_result.get("projection")
    if source_projection is None:
        source_projection = sorted_projection(
            source_result["dump"], transformed=False
        )
    transformed_projection = sorted_projection(
        transformed_result["dump"], transformed=True
    )

    label_prefix = "%s/" % engine_label if engine_label else ""
    display_metrics(label_prefix + "source", source_result)
    display_metrics(label_prefix + "transformed", transformed_result)
    if transformed_result["unifications"]:
        print(
            "%sunification-ratio=%.6fx"
            % (
                label_prefix,
                source_result["unifications"]
                / transformed_result["unifications"],
            )
        )

    failed = False
    if source_projection != transformed_projection:
        report_difference(
            label_prefix + "projection", source_projection, transformed_projection
        )
        failed = True
    else:
        print(
            "OK %sprojection identical: %d bytes, %d lines"
            % (
                label_prefix,
                len(source_projection),
                source_projection.count(b"\n"),
            )
        )
    if expected is not None:
        with open(expected, "rb") as stream:
            expected_projection = sorted_projection(stream.read(), transformed=False)
        if source_projection != expected_projection:
            report_difference(
                label_prefix + "expected projection",
                expected_projection,
                source_projection,
            )
            failed = True
        else:
            print(
                "OK %sexpected projection: %s"
                % (label_prefix, os.path.relpath(expected, REPO))
            )
    if required is not None:
        with open(required, "rb") as stream:
            required_lines = set(stream.read().splitlines())
        if not required_lines or b"" in required_lines:
            raise ValueError("required projection must contain nonempty lines")
        projected_lines = set(source_projection.splitlines())
        missing = sorted(required_lines - projected_lines)
        if missing:
            print("FAIL %srequired projection line is absent" % label_prefix)
            print("missing: %s" % missing[0].decode("utf-8", errors="replace"))
            failed = True
        else:
            print(
                "OK %srequired projection: %s"
                % (label_prefix, os.path.basename(required))
            )
    return int(failed), {
        "source": source_result,
        "transformed": transformed_result,
        "source_projection": source_projection,
        "transformed_projection": transformed_projection,
    }


def compare_cross_engine(
    left_label,
    left,
    right_label,
    right,
    engine_specific_fields=(),
):
    failed = False
    for arm in ("source", "transformed"):
        projection_key = arm + "_projection"
        if left[projection_key] != right[projection_key]:
            report_difference(
                "cross-engine %s %s != %s" % (arm, left_label, right_label),
                left[projection_key],
                right[projection_key],
            )
            failed = True
        else:
            print(
                "OK cross-engine %s projection %s=%s: %d bytes, %d lines"
                % (
                    arm,
                    left_label,
                    right_label,
                    len(left[projection_key]),
                    left[projection_key].count(b"\n"),
                )
            )

        invariant_fields = [
            field
            for field in ("steps", "unifications", "writes")
            if field not in engine_specific_fields
        ]
        if "rounds" in left[arm] or "rounds" in right[arm]:
            invariant_fields.append("rounds")
        if "step_bound" in left[arm] or "step_bound" in right[arm]:
            invariant_fields.append("step_bound")
        mismatches = [
            field
            for field in invariant_fields
            if left[arm].get(field) != right[arm].get(field)
        ]
        if mismatches:
            field = mismatches[0]
            print(
                "FAIL cross-engine %s counter %s differs: %s=%r, %s=%r"
                % (
                    arm,
                    field,
                    left_label,
                    left[arm].get(field),
                    right_label,
                    right[arm].get(field),
                )
            )
            failed = True
        else:
            counters = " ".join(
                "%s=%d" % (field, left[arm][field]) for field in invariant_fields
            )
            specific_fields = ("transitions",) + tuple(engine_specific_fields)
            specific = " ".join(
                "%s %s=%d %s=%d"
                % (
                    field,
                    left_label,
                    left[arm][field],
                    right_label,
                    right[arm][field],
                )
                for field in specific_fields
            )
            print(
                "OK cross-engine %s counters %s=%s: %s; %s (engine-specific)"
                % (
                    arm,
                    left_label,
                    right_label,
                    counters,
                    specific,
                )
            )
    return int(failed)


def compare(
    binary,
    source,
    transformed,
    expected,
    steps,
    max_source_rounds,
    required=None,
):
    failed, _ = evaluate_case(
        binary,
        source,
        transformed,
        expected,
        steps,
        max_source_rounds,
        required,
    )
    return failed


def transform_program(source, output):
    command = [sys.executable, os.path.join(HERE, "transform.py"), source, output]
    completed = capture(command)
    if completed.returncode != 0:
        sys.stderr.buffer.write(completed.stdout)
        raise RuntimeError(
            "transform failed for %s" % os.path.relpath(source, REPO)
        )


def generate_benchmark_corpus(output_root):
    gen_process_calculus.generate(
        os.path.join(output_root, "process_calculus"),
        gen_process_calculus.DEFAULT_INSTANCES,
    )
    gen_transitive.generate(
        os.path.join(output_root, "transitive"),
        gen_transitive.DEFAULT_LENGTHS,
    )


def discover_cases(transformed_root, generate_all=False, benchmark_root=None):
    corpus = os.path.join(HERE, "corpus")
    cases = []
    roots = [(corpus, "", True)]
    if benchmark_root is not None:
        roots.extend(
            [
                (
                    os.path.join(benchmark_root, "process_calculus"),
                    "generated/process_calculus",
                    False,
                ),
                (
                    os.path.join(benchmark_root, "transitive"),
                    "generated/transitive",
                    False,
                ),
            ]
        )
    for source_root, label_prefix, checked in roots:
        for directory, dirnames, filenames in os.walk(source_root):
            dirnames.sort()
            for filename in sorted(filenames):
                if not filename.endswith(".source.mm2"):
                    continue
                source = os.path.join(directory, filename)
                stem = filename[: -len(".source.mm2")]
                relative_directory = os.path.relpath(directory, source_root)
                label = os.path.normpath(
                    os.path.join(label_prefix, relative_directory, filename)
                )
                checked_transform = os.path.join(
                    directory, stem + ".transformed.mm2"
                )
                if checked and not generate_all and os.path.isfile(checked_transform):
                    transformed = checked_transform
                else:
                    output_group = label_prefix or "corpus"
                    transformed = os.path.join(
                        transformed_root,
                        output_group,
                        relative_directory,
                        stem + ".transformed.mm2",
                    )
                    os.makedirs(os.path.dirname(transformed), exist_ok=True)
                    transform_program(source, transformed)
                expected = None
                if checked:
                    expected = os.path.join(
                        HERE, "expected", relative_directory, stem + ".expected"
                    )
                    if not os.path.isfile(expected):
                        expected = None
                required = os.path.join(directory, stem + ".required")
                if not os.path.isfile(required):
                    required = None
                cases.append(
                    OracleCase(label, source, transformed, expected, required)
                )
    if not cases:
        raise RuntimeError("no .source.mm2 corpus cases found")
    return cases


def discover_repository_cases(transformed_root, manifest=REPOSITORY_MANIFEST):
    cases = []
    for spec in load_repository_manifest(manifest):
        transformed = os.path.join(
            transformed_root, "repository", spec.label + ".transformed.mm2"
        )
        os.makedirs(os.path.dirname(transformed), exist_ok=True)
        transform_program(spec.source, transformed)
        cases.append(
            OracleCase(
                "repository/" + spec.label,
                spec.source,
                transformed,
                spec.expected,
                source_mode=spec.source_mode,
                source_steps=spec.source_steps,
                engine_specific_fields=spec.engine_specific_fields,
            )
        )
    return cases


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", nargs="?")
    parser.add_argument("transformed", nargs="?")
    parser.add_argument("--all", action="store_true")
    parser.add_argument("--generate", action="store_true")
    parser.add_argument(
        "--suite",
        action="append",
        choices=("existing", "repository"),
        dest="suites",
        help="oracle suite; repeat to select both (default: both)",
    )
    parser.add_argument("--expected")
    parser.add_argument(
        "--binary",
        action="append",
        dest="binaries",
        help="mork binary; repeat exactly twice under --all for cross-engine checks",
    )
    parser.add_argument("--steps", type=int, default=DEFAULT_STEPS)
    parser.add_argument("--max-source-rounds", type=int, default=1024)
    args = parser.parse_args()

    binaries = [os.path.abspath(path) for path in (args.binaries or [DEFAULT_BINARY])]
    for binary in binaries:
        if not os.access(binary, os.X_OK):
            parser.error("binary is not executable: %s" % binary)
    if len(binaries) > 2:
        parser.error("at most two --binary values are supported")
    if len(binaries) == 2:
        if os.path.samefile(binaries[0], binaries[1]):
            parser.error("cross-engine binaries resolve to the same file")
        labels = [os.path.basename(binary) for binary in binaries]
        if labels[0] == labels[1]:
            parser.error("cross-engine binary basenames must be distinct")
    else:
        labels = [os.path.basename(binaries[0])]
    if args.generate and not args.all:
        parser.error("--generate requires --all")
    if args.suites and not args.all:
        parser.error("--suite requires --all")
    suites = args.suites or ["existing", "repository"]
    if len(suites) != len(set(suites)):
        parser.error("duplicate --suite value")
    if args.generate and "existing" not in suites:
        parser.error("--generate requires the existing suite")

    try:
        if args.all:
            if args.source is not None or args.transformed is not None or args.expected:
                parser.error("--all does not accept source, transformed, or --expected")
            failed = 0
            temp_root = os.path.join(REPO, "target", "semi_naive")
            os.makedirs(temp_root, exist_ok=True)
            with tempfile.TemporaryDirectory(
                prefix="semi-naive-generated-", dir=temp_root
            ) as generated_root:
                transformed_root = os.path.join(generated_root, "transforms")
                cases = []
                if "existing" in suites:
                    benchmark_root = os.path.join(generated_root, "sources")
                    generate_benchmark_corpus(benchmark_root)
                    cases.extend(
                        discover_cases(
                            transformed_root,
                            generate_all=args.generate,
                            benchmark_root=benchmark_root,
                        )
                    )
                if "repository" in suites:
                    cases.extend(discover_repository_cases(transformed_root))
                for case in cases:
                    print("== %s ==" % case.label)
                    case_failed = False
                    engine_results = []
                    for engine_label, binary in zip(labels, binaries):
                        if len(binaries) == 2:
                            print("-- %s --" % engine_label)
                        engine_failed, engine_result = evaluate_case(
                            binary,
                            case.source,
                            case.transformed,
                            case.expected,
                            args.steps,
                            args.max_source_rounds,
                            case.required,
                            engine_label if len(binaries) == 2 else None,
                            case.source_mode,
                            case.source_steps,
                        )
                        case_failed |= bool(engine_failed)
                        engine_results.append(engine_result)
                    if len(binaries) == 2:
                        case_failed |= bool(
                            compare_cross_engine(
                                labels[0],
                                engine_results[0],
                                labels[1],
                                engine_results[1],
                                case.engine_specific_fields,
                            )
                        )
                    failed += int(case_failed)
            print("%d cases, %d failed" % (len(cases), failed))
            return 1 if failed else 0

        if args.source is None or args.transformed is None:
            parser.error("source and transformed are required unless --all is used")
        if len(binaries) != 1:
            parser.error("two --binary values require --all")
        source = os.path.abspath(args.source)
        transformed = os.path.abspath(args.transformed)
        expected = os.path.abspath(args.expected) if args.expected else None
        for program in (source, transformed, expected):
            if program is not None and not os.path.isfile(program):
                parser.error("file does not exist: %s" % program)
        return compare(
            binaries[0],
            source,
            transformed,
            expected,
            args.steps,
            args.max_source_rounds,
        )
    except (OSError, RuntimeError, ValueError) as error:
        print("ERROR: %s" % error, file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
