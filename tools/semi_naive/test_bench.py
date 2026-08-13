#!/usr/bin/env python3

import argparse
import contextlib
import io
import os
import subprocess
import sys
import tempfile
import unittest
from unittest import mock


sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import bench


def sample(wall_ns=10, transitions=5, unifications=3):
    return {
        "steps": 2,
        "unifications": unifications,
        "writes": 4,
        "transitions": transitions,
        "engine_ms": 1,
        "wall_ns": wall_ns,
        "rounds": 1,
        "projection": b"(fact a)\n",
    }


class BenchTest(unittest.TestCase):
    def test_timeout_parser_rejects_nonfinite_values(self):
        for value in ("nan", "inf", "-inf", "0"):
            with self.subTest(value=value), self.assertRaises(
                argparse.ArgumentTypeError
            ):
                bench.positive_float(value)

    def test_case_specs_require_one_workload_for_custom_sizes(self):
        with self.assertRaisesRegex(
            bench.BenchmarkRefusal, "^SIZES_REQUIRE_ONE_WORKLOAD$"
        ):
            bench.case_specs(["process_calculus", "transitive"], [8])

    def test_interleaved_schedule_rotates_each_repeat(self):
        cells = [("naive", "pz"), ("naive", "lf"), ("transformed", "pz")]
        self.assertEqual(
            list(bench.interleaved_schedule(cells, 2)),
            [
                (0, cells[0]),
                (0, cells[1]),
                (0, cells[2]),
                (1, cells[1]),
                (1, cells[2]),
                (1, cells[0]),
            ],
        )

    def test_interleaved_schedule_is_a_permutation_for_many_shapes(self):
        for cell_count in range(1, 9):
            cells = [("cell", index) for index in range(cell_count)]
            schedule = list(bench.interleaved_schedule(cells, 11))
            for repeat in range(11):
                observed = [cell for row, cell in schedule if row == repeat]
                self.assertEqual(len(observed), cell_count)
                self.assertEqual(set(observed), set(cells))

    def test_counter_signature_excludes_time_but_includes_transitions(self):
        left = sample(wall_ns=10, transitions=5)
        right = dict(left, wall_ns=20, engine_ms=9)
        self.assertEqual(bench.counter_bytes(left), bench.counter_bytes(right))
        different = dict(right, transitions=6)
        self.assertNotEqual(bench.counter_bytes(left), bench.counter_bytes(different))

    def test_changed_counter_repeat_hard_errors(self):
        with self.assertRaisesRegex(RuntimeError, "^NONDETERMINISTIC_COUNTERS"):
            bench.verify_counter_repeat(
                [sample(unifications=3)], sample(unifications=4), "case"
            )

    def test_engine_and_wall_minima_are_selected_independently(self):
        case = {
            "workload": "transitive",
            "size": 4,
            "instance": "4",
        }
        slow = sample(wall_ns=20)
        slow["engine_ms"] = 2
        fast = sample(wall_ns=10)
        fast["engine_ms"] = 7
        row = bench.completed_row(case, "transformed", "pz", [slow, fast], 2)
        self.assertEqual(row["selected_wall_repeat"], 2)
        self.assertEqual(row["selected_engine_repeat"], 1)
        self.assertEqual(row["wall_ns"], 10)
        self.assertEqual(row["engine_ms"], 2)

    def test_cross_engine_invariants_ignore_transitions(self):
        case = {
            "workload": "transitive",
            "size": 4,
            "instance": "4",
        }
        pz = bench.completed_row(
            case, "transformed", "pz", [sample(transitions=99)], 1
        )
        lf = bench.completed_row(
            case, "transformed", "lf", [sample(transitions=1)], 1
        )
        bench.verify_cross_engine_counters([pz, lf])
        lf["unifications"] = 100
        with self.assertRaisesRegex(
            RuntimeError, "^CROSS_ENGINE_COUNTER_MISMATCH"
        ):
            bench.verify_cross_engine_counters([pz, lf])

    def test_cross_cell_projection_mismatch_hard_errors(self):
        case = {"required": None}
        with self.assertRaisesRegex(
            RuntimeError, "^CROSS_CELL_PROJECTION_MISMATCH"
        ):
            bench.verify_projection(
                case,
                b"(fact a)\n",
                dict(sample(), projection=b"(fact b)\n"),
                "case",
            )

    def test_binary_validation_rejects_identical_copies(self):
        with tempfile.TemporaryDirectory() as workdir:
            pz = os.path.join(workdir, "pz")
            lf = os.path.join(workdir, "lf")
            for path in (pz, lf):
                with open(path, "wb") as stream:
                    stream.write(b"binary")
                os.chmod(path, 0o755)
            with self.assertRaisesRegex(
                bench.BenchmarkRefusal, "^ENGINE_BINARIES_IDENTICAL$"
            ):
                bench.validate_binaries({"pz": pz, "lf": lf}, ["pz", "lf"])

    @mock.patch.object(bench, "run_cell_once")
    def test_naive_timeout_prints_skip_and_keeps_transformed_cell(self, run_cell):
        def side_effect(protocol, *args, **kwargs):
            if protocol == "naive":
                raise subprocess.TimeoutExpired("mork", 1)
            return sample()

        run_cell.side_effect = side_effect
        with tempfile.TemporaryDirectory() as workdir:
            transformed = os.path.join(workdir, "transformed.mm2")
            with open(transformed, "w", encoding="utf-8") as stream:
                stream.write("(f (fact a))\n")
            case = {
                "workload": "transitive",
                "size": 4,
                "instance": "4",
                "source": os.path.join(workdir, "source.mm2"),
                "transformed": transformed,
                "required": None,
            }
            output = io.StringIO()
            with contextlib.redirect_stdout(output):
                rows = bench.benchmark_case(
                    case,
                    [("naive", "pz"), ("transformed", "pz")],
                    {"pz": "/mork"},
                    1,
                    100,
                    8,
                    1,
                    workdir,
                )
        self.assertEqual(rows[0]["status"], "skipped")
        self.assertEqual(rows[1]["status"], "measured")
        self.assertIn(
            "SKIP transitive 4 naive repeated-evaluation protocol PZ repeat 1: "
            "repeated-evaluation protocol exceeded 1 seconds in repeat 1",
            output.getvalue(),
        )

    @mock.patch.object(bench.driver, "run_source_protocol")
    @mock.patch.object(bench.time, "perf_counter_ns", side_effect=[0, 2_000_000_000])
    def test_naive_protocol_checks_total_wall_after_final_round(self, _, protocol):
        protocol.return_value = {
            "steps": 1,
            "milliseconds": 1,
            "unifications": 1,
            "writes": 1,
            "transitions": 1,
            "rounds": 1,
            "projection": b"(fact a)\n",
        }
        case = {"source": "/source.mm2"}
        with self.assertRaises(subprocess.TimeoutExpired):
            bench.run_naive_once("/mork", case, "/work", 10, 2, 1)

    def test_table_never_labels_naive_as_one_shot(self):
        case = {
            "workload": "transitive",
            "size": 4,
            "instance": "4",
        }
        row = bench.completed_row(case, "naive", "pz", [sample()], 1)
        table = bench.render_table([row], 1)
        self.assertIn("naive repeated-evaluation protocol", table)
        self.assertNotIn("one-shot", table)

    def test_artifact_distinguishes_resolved_skips_from_all_measured(self):
        case = {
            "workload": "transitive",
            "size": 4,
            "instance": "4",
        }
        rows = [bench.skipped_row(case, "naive", "pz", "timeout")]
        with mock.patch.object(bench, "git_head", return_value="abc"), mock.patch.object(
            bench, "sha256_file", return_value="def"
        ):
            artifact = bench.artifact(rows, {"pz": "/pz"}, 3, 900, 8, 10)
        self.assertTrue(artifact["resolved"])
        self.assertFalse(artifact["all_measured"])


if __name__ == "__main__":
    unittest.main()
