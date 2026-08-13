#!/usr/bin/env python3

import os
import sys
import unittest


HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import repository_bench


def result(rounds=3, unifications=10, transitions=20):
    return {
        "source": {
            "rounds": rounds,
            "steps": 3,
            "unifications": unifications,
            "writes": 11,
            "transitions": transitions,
        },
        "transformed": {
            "steps": 7,
            "unifications": 8,
            "writes": 12,
            "transitions": transitions + 1,
        },
        "source_projection": b"(fact)\n",
        "transformed_projection": b"(fact)\n",
    }


class RepositoryBenchTest(unittest.TestCase):
    def test_short_programs_are_labeled_neutral(self):
        sample = result(rounds=2, unifications=1)
        self.assertEqual(
            repository_bench.verdict(sample["source"], sample["transformed"]),
            "NEUTRAL_SHORT",
        )

    def test_longer_programs_report_reduction_or_overhead(self):
        reduced = result(rounds=3, unifications=10)
        overhead = result(rounds=3, unifications=4)
        self.assertEqual(
            repository_bench.verdict(
                reduced["source"], reduced["transformed"]
            ),
            "FEWER_UNIFICATIONS",
        )
        self.assertEqual(
            repository_bench.verdict(
                overhead["source"], overhead["transformed"]
            ),
            "OVERHEAD",
        )
        self.assertEqual(
            repository_bench.verdict(
                overhead["source"], overhead["transformed"], "natural"
            ),
            "BOUNDED_SOURCE",
        )

    def test_repeat_counter_or_projection_change_hard_errors(self):
        reference = result()
        changed_counter = result(transitions=21)
        with self.assertRaisesRegex(RuntimeError, "^NONDETERMINISTIC_COUNTERS"):
            repository_bench.verify_repeat(reference, changed_counter, "case")

        changed_projection = result()
        changed_projection["source_projection"] = b"(different)\n"
        with self.assertRaisesRegex(RuntimeError, "^NONDETERMINISTIC_PROJECTION"):
            repository_bench.verify_repeat(reference, changed_projection, "case")


if __name__ == "__main__":
    unittest.main()
