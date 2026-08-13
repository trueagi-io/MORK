#!/usr/bin/env python3

import copy
import hashlib
import json
import os
import sys
import tempfile
import unittest


sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import analyze
import bench


def projection_hash(workload, size):
    return hashlib.sha256(("%s:%d" % (workload, size)).encode()).hexdigest()


def result_row(workload, size, protocol, engine):
    scale = 2 if protocol == "transformed" else 1
    transitions = size ** (3 if engine == "pz" else 2)
    if protocol == "naive" and engine == "lf":
        transitions = 0
    engine_ms = {
        ("naive", "pz"): size * 100,
        ("naive", "lf"): size * 50,
        ("transformed", "pz"): size * 10,
        ("transformed", "lf"): size,
    }[(protocol, engine)]
    counters = {
        "steps": size * scale,
        "unifications": size * 3 * scale,
        "writes": size * 4 * scale,
        "transitions": transitions,
        "rounds": size if protocol == "naive" else 1,
    }
    samples = [
        {
            "repeat": repeat,
            **counters,
            "engine_ms": engine_ms + repeat - 1,
            "wall_ns": (engine_ms + repeat) * 1_000_000,
            "wall_ms": engine_ms + repeat,
        }
        for repeat in (1, 2, 3)
    ]
    return {
        "workload": workload,
        "size": size,
        "instance": "%d+%d" % (size, size)
        if workload == "process_calculus"
        else str(size),
        "protocol": protocol,
        "protocol_label": bench.protocol_label(protocol),
        "engine": engine,
        "status": "measured",
        **counters,
        "engine_ms": engine_ms,
        "wall_ns": (engine_ms + 1) * 1_000_000,
        "wall_ms": engine_ms + 1,
        "selected_engine_repeat": 1,
        "selected_wall_repeat": 1,
        "projection_bytes": size * size,
        "projection_lines": size,
        "projection_sha256": projection_hash(workload, size),
        "samples": samples,
    }


def complete_artifact():
    rows = [
        result_row(workload, size, protocol, engine)
        for workload, sizes in bench.WORKLOAD_SIZES.items()
        for size in sizes
        for protocol in bench.PROTOCOL_ORDER
        for engine in bench.ENGINE_ORDER
    ]
    return {
        "schema": 1,
        "resolved": True,
        "all_measured": True,
        "git_head": "a" * 40,
        "binaries": {
            "pz": {"sha256": "1" * 64},
            "lf": {"sha256": "2" * 64},
        },
        "methodology": {"repeats": 3},
        "results": rows,
    }


def write_artifact(root, name, artifact):
    path = os.path.join(root, name)
    with open(path, "w", encoding="utf-8") as stream:
        json.dump(artifact, stream)
    return path


class AnalyzeTest(unittest.TestCase):
    def load(self, artifact):
        with tempfile.TemporaryDirectory() as root:
            path = write_artifact(root, "bench.json", artifact)
            return analyze.load_and_validate([path])

    def test_complete_matrix_has_expected_power_fits_and_ratios(self):
        rows, hashes, sources = self.load(complete_artifact())
        result = analyze.analyze(rows, hashes, sources)
        self.assertEqual(result["validation"]["cells"], 32)
        self.assertAlmostEqual(
            result["scaling"]["process_calculus"]["pz"]["fit"]["exponent"],
            3,
        )
        self.assertAlmostEqual(
            result["scaling"]["process_calculus"]["lf"]["fit"]["exponent"],
            2,
        )
        self.assertAlmostEqual(
            result["projection_scaling"]["process_calculus"]["fit"]["exponent"],
            2,
        )
        growth = result["scaling"]["process_calculus"]["pz"]["adjacent_growth"]
        self.assertTrue(all(abs(item["per_doubling"] - 8) < 1e-12 for item in growth))
        ratios = result["composition_at_process_calculus_320"]["ratios"]
        self.assertEqual(ratios["stock_to_combined"], 100)
        self.assertEqual(ratios["same_lf_naive_to_transformed"], 50)

    def test_fragments_must_use_the_same_binary_hashes(self):
        artifact = complete_artifact()
        left = copy.deepcopy(artifact)
        right = copy.deepcopy(artifact)
        left["results"] = artifact["results"][:16]
        right["results"] = artifact["results"][16:]
        right["binaries"]["lf"]["sha256"] = "3" * 64
        with tempfile.TemporaryDirectory() as root:
            paths = [
                write_artifact(root, "left.json", left),
                write_artifact(root, "right.json", right),
            ]
            with self.assertRaisesRegex(
                analyze.AnalysisRefusal, "^MIXED_BINARY_HASHES"
            ):
                analyze.load_and_validate(paths)

    def test_duplicate_cell_is_refused(self):
        artifact = complete_artifact()
        artifact["results"].append(copy.deepcopy(artifact["results"][0]))
        with self.assertRaisesRegex(analyze.AnalysisRefusal, "^DUPLICATE_CELL"):
            self.load(artifact)

    def test_missing_cell_is_refused(self):
        artifact = complete_artifact()
        artifact["results"].pop()
        with self.assertRaisesRegex(analyze.AnalysisRefusal, "^INCOMPLETE_MATRIX"):
            self.load(artifact)

    def test_skipped_cell_is_refused(self):
        artifact = complete_artifact()
        artifact["all_measured"] = False
        artifact["results"][0] = {
            **artifact["results"][0],
            "status": "skipped",
            "reason": "timeout",
        }
        with self.assertRaisesRegex(analyze.AnalysisRefusal, "^BENCHMARK_HAS_SKIPS"):
            self.load(artifact)

    def test_counter_change_between_repeats_is_refused(self):
        artifact = complete_artifact()
        artifact["results"][0]["samples"][1]["writes"] += 1
        with self.assertRaisesRegex(
            analyze.AnalysisRefusal, "^NONDETERMINISTIC_COUNTERS"
        ):
            self.load(artifact)

    def test_nonminimum_timer_is_refused(self):
        artifact = complete_artifact()
        artifact["results"][0]["engine_ms"] += 1
        with self.assertRaisesRegex(analyze.AnalysisRefusal, "^ENGINE_MS_NOT_MINIMUM"):
            self.load(artifact)

    def test_projection_disagreement_is_refused(self):
        artifact = complete_artifact()
        artifact["results"][1]["projection_sha256"] = "f" * 64
        with self.assertRaisesRegex(
            analyze.AnalysisRefusal, "^CROSS_CELL_PROJECTION_MISMATCH"
        ):
            self.load(artifact)


if __name__ == "__main__":
    unittest.main()
