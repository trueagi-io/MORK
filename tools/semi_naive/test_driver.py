#!/usr/bin/env python3

import contextlib
import io
import os
import subprocess
import sys
import tempfile
import unittest
from unittest import mock


sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import driver


def cross_engine_fixture():
    projection = b"(fact a)\n"
    return {
        "source_projection": projection,
        "transformed_projection": projection,
        "source": {
            "steps": 1,
            "milliseconds": 1,
            "unifications": 2,
            "writes": 3,
            "transitions": 4,
            "rounds": 1,
        },
        "transformed": {
            "steps": 1,
            "milliseconds": 1,
            "unifications": 2,
            "writes": 3,
            "transitions": 4,
        },
    }


class DriverTest(unittest.TestCase):
    def test_metrics_accept_product_zipper_and_leapfrog_formats(self):
        expected = {
            "steps": 8659,
            "milliseconds": 1123,
            "unifications": 6732,
            "writes": 19872,
            "transitions": 12798481,
        }
        product_zipper = (
            b"executing 8659 steps took 1123 ms "
            b"(unifications 6732, writes 19872, transitions 12798481)\n"
        )
        leapfrog = (
            b"executing 8659 steps took 1123 ms "
            b"(unifications 6732, writes 19872, transitions 12798481, max unify 9)\n"
        )
        self.assertEqual(driver.parse_metrics(product_zipper), expected)
        self.assertEqual(driver.parse_metrics(leapfrog), expected)

    def test_missing_metrics_has_a_named_error(self):
        with self.assertRaisesRegex(ValueError, "^EXECUTION_METRICS_MISSING$"):
            driver.parse_metrics(b"no counters here")

    def test_materializer_handles_comments_strings_and_semicolons_in_atoms(self):
        program = '''
            ; (ignored)
            (fact foo;bar "text; ) still text") ; trailing comment
            (exec (priority 0) (, (fact $x $y)) (, (seen $x $y)))
        '''
        materialized = driver.materialize_naive_program(program, rounds=1)
        self.assertIn('(fact foo;bar "text; ) still text")', materialized)
        self.assertIn("(naive r000000 (priority 0) q000000)", materialized)

    def test_materializer_rejects_unbalanced_input(self):
        with self.assertRaisesRegex(ValueError, "unterminated expression"):
            driver.materialize_naive_program("(fact", rounds=1)
        with self.assertRaisesRegex(ValueError, "unexpected"):
            driver.materialize_naive_program("fact)", rounds=1)

    def test_materialized_rounds_have_ordered_unique_priorities(self):
        program = """
            (seed)
            (exec (source 2) (, (seed)) (, (two)))
            (exec (source 1) (, (seed)) (, (one)))
        """
        materialized = driver.materialize_naive_program(program, rounds=2)
        self.assertEqual(materialized.count("(exec "), 4)
        self.assertIn("(naive r000000 (source 2) q000000)", materialized)
        self.assertIn("(naive r000001 (source 1) q000001)", materialized)

    @mock.patch.object(driver, "run_program")
    def test_source_protocol_sums_external_rounds(self, run_program):
        run_program.side_effect = [
            {
                "steps": 2,
                "milliseconds": 3,
                "unifications": 5,
                "writes": 7,
                "transitions": 11,
                "dump": b"(out a)\n(seed a)\n",
            },
            {
                "steps": 2,
                "milliseconds": 4,
                "unifications": 5,
                "writes": 7,
                "transitions": 13,
                "dump": b"(seed a)\n(out a)\n",
            },
        ]
        with tempfile.TemporaryDirectory() as workdir:
            program = os.path.join(workdir, "source.mm2")
            with open(program, "w", encoding="utf-8") as stream:
                stream.write(
                    "(seed a)\n(exec 0 (, (seed $x)) (, (out $x)))\n"
                )
            result = driver.run_source_protocol(
                "/mork", program, workdir, driver.DEFAULT_STEPS, 8
            )
        self.assertEqual(result["rounds"], 2)
        self.assertEqual(result["steps"], 4)
        self.assertEqual(result["milliseconds"], 7)
        self.assertEqual(result["unifications"], 10)
        self.assertEqual(result["writes"], 14)
        self.assertEqual(result["transitions"], 24)
        self.assertEqual(result["projection"], b"(out a)\n(seed a)\n")

    @mock.patch.object(driver, "run_program")
    def test_natural_source_uses_bound_and_strips_live_exec(self, run_program):
        run_program.return_value = {
            "steps": 1,
            "milliseconds": 2,
            "unifications": 3,
            "writes": 4,
            "transitions": 5,
            "dump": b"(fact a)\n(exec loop (, (fact $x)) (, (fact $x)))\n",
        }
        with tempfile.TemporaryDirectory() as workdir:
            result = driver.run_source_natural(
                "/mork", "/source.mm2", workdir, driver.DEFAULT_STEPS, 7
            )
        self.assertEqual(run_program.call_args.args[3], 7)
        self.assertEqual(result["projection"], b"(fact a)\n")
        self.assertEqual(result["step_bound"], 7)
        self.assertEqual(result["source_mode"], "natural")

    @mock.patch.object(driver.time, "perf_counter_ns", return_value=101)
    def test_expired_protocol_deadline_is_named(self, _):
        with self.assertRaises(subprocess.TimeoutExpired) as raised:
            driver.timeout_until(100)
        self.assertEqual(raised.exception.cmd, "repeated-evaluation protocol")

    def test_projection_unwraps_and_drops_bookkeeping(self):
        dump = b"""\
(phase p q r)
(f (edge b c))
(cand (edge a c))
(d0 (edge b c))
(d1 (edge a c))
(c d0 d1 (edge a c))
(t d0 d1)
(f (edge a b))
(controller p q)
(active)
"""
        self.assertEqual(
            driver.sorted_projection(dump, transformed=True),
            b"(edge a b)\n(edge b c)\n",
        )

    def test_expected_projection_comments_and_source_exec_are_optional_metadata(self):
        dump = b"; @source-steps 1\n(fact a)\n(exec loop (, (fact $x)) (, (fact $x)))\n"
        self.assertEqual(
            driver.sorted_projection(dump, transformed=False, strip_exec=True),
            b"(fact a)\n",
        )
        with tempfile.NamedTemporaryFile("w", encoding="utf-8") as stream:
            stream.write(";; @source-steps 7\n(fact a)\n")
            stream.flush()
            self.assertEqual(driver.read_expected_source_steps(stream.name), 7)

    def test_first_difference_reports_missing_lines(self):
        self.assertEqual(
            driver.first_difference(b"a\nb\n", b"a\n"),
            (2, b"b", b"<missing>"),
        )

    def test_bare_top_level_variable_fact_is_a_named_error(self):
        with tempfile.TemporaryDirectory() as workdir:
            program = os.path.join(workdir, "bare.mm2")
            with open(program, "w", encoding="utf-8") as stream:
                stream.write("(fixed $x)\n$bare\n")
            with self.assertRaisesRegex(
                ValueError, "^BARE_TOP_LEVEL_VARIABLE_FACT: .* form 2$"
            ):
                driver.assert_no_bare_top_level_variable_facts(program)

    def test_all_generated_transforms_have_no_bare_top_level_variable_facts(self):
        temp_root = os.path.join(driver.REPO, "target", "semi_naive")
        os.makedirs(temp_root, exist_ok=True)
        with tempfile.TemporaryDirectory(
            prefix="semi-naive-bare-variable-test-", dir=temp_root
        ) as root:
            benchmark_root = os.path.join(root, "sources")
            driver.generate_benchmark_corpus(benchmark_root)
            cases = driver.discover_cases(
                os.path.join(root, "transforms"),
                generate_all=True,
                benchmark_root=benchmark_root,
            )
            self.assertEqual(len(cases), 17)
            for case in cases:
                with self.subTest(label=case.label):
                    driver.assert_no_bare_top_level_variable_facts(
                        case.transformed
                    )

    def test_repository_manifest_pins_persistent_and_self_respawn_cases(self):
        specs = driver.load_repository_manifest()
        self.assertEqual(len(specs), 11)
        self.assertEqual(
            [spec.label for spec in specs],
            [
                "kernel/string_convert",
                "kernel/transitive",
                "programs/cross_join_dict",
                "programs/cross_join_tuple",
                "programs/lens_aunt",
                "programs/lens_composition",
                "programs/pattern_mining",
                "programs/stv_roman",
                "unify/coref_absorbed_by_data_varref",
                "unify/func_type_unification",
                "unify/two_bipolar_equal_crossed",
            ],
        )
        persistent = [spec for spec in specs if spec.source_mode == "persistent"]
        natural = [spec for spec in specs if spec.source_mode == "natural"]
        self.assertEqual(len(persistent), 10)
        self.assertTrue(all(spec.source_steps is None for spec in persistent))
        self.assertEqual(
            [(spec.label, spec.source_steps) for spec in natural],
            [("programs/lens_aunt", 1)],
        )
        self.assertEqual(natural[0].engine_specific_fields, ("unifications",))

    def test_repository_manifest_rejects_escape_and_duplicate_rows(self):
        with tempfile.TemporaryDirectory() as workdir:
            manifest = os.path.join(workdir, "manifest.tsv")
            with open(manifest, "w", encoding="utf-8") as stream:
                stream.write("bad|../source.mm2|../expected|persistent|-|-\n")
            with self.assertRaisesRegex(
                ValueError, "^REPOSITORY_MANIFEST_ESCAPES_REPO_SOURCE"
            ):
                driver.load_repository_manifest(manifest)

            source = os.path.relpath(__file__, driver.REPO)
            with open(manifest, "w", encoding="utf-8") as stream:
                stream.write("one|%s|%s|persistent|-|-\n" % (source, source))
                stream.write("one|%s|%s|persistent|-|-\n" % (source, source))
            with self.assertRaisesRegex(
                ValueError, "^REPOSITORY_MANIFEST_DUPLICATE_LABEL"
            ):
                driver.load_repository_manifest(manifest)

    def test_cross_engine_agreement_ignores_transitions_and_time(self):
        projection = b"(fact a)\n"
        left = {
            "source_projection": projection,
            "transformed_projection": projection,
            "source": {
                "steps": 3,
                "milliseconds": 20,
                "unifications": 4,
                "writes": 5,
                "transitions": 100,
                "rounds": 2,
            },
            "transformed": {
                "steps": 7,
                "milliseconds": 10,
                "unifications": 8,
                "writes": 9,
                "transitions": 200,
            },
        }
        right = {
            "source_projection": projection,
            "transformed_projection": projection,
            "source": dict(left["source"], milliseconds=12, transitions=0),
            "transformed": dict(
                left["transformed"], milliseconds=1, transitions=30
            ),
        }
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(
                driver.compare_cross_engine("bin-pz", left, "bin-lf", right),
                0,
            )

    def test_cross_engine_counter_mismatch_fails(self):
        result = cross_engine_fixture()
        different = dict(result)
        different["transformed"] = dict(result["transformed"], unifications=99)
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(
                driver.compare_cross_engine(
                    "bin-pz", result, "bin-lf", different
                ),
                1,
            )

    def test_declared_engine_specific_unifications_are_reported_not_failed(self):
        result = cross_engine_fixture()
        different = dict(result)
        different["source"] = dict(result["source"], unifications=99)
        different["transformed"] = dict(
            result["transformed"], unifications=101
        )
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(
                driver.compare_cross_engine(
                    "bin-pz",
                    result,
                    "bin-lf",
                    different,
                    ("unifications",),
                ),
                0,
            )

    def test_cross_engine_projection_mismatch_fails(self):
        result = cross_engine_fixture()
        different = dict(result, transformed_projection=b"(fact b)\n")
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(
                driver.compare_cross_engine(
                    "bin-pz", result, "bin-lf", different
                ),
                1,
            )


if __name__ == "__main__":
    unittest.main()
