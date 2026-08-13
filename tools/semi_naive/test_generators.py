#!/usr/bin/env python3

import argparse
import os
import sys
import tempfile
import unittest


HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))
GENERATORS = os.path.join(HERE, "generators")
sys.path.insert(0, GENERATORS)
import gen_process_calculus
import gen_transitive


def tree_bytes(root):
    contents = {}
    for directory, dirnames, filenames in os.walk(root):
        dirnames.sort()
        for filename in sorted(filenames):
            path = os.path.join(directory, filename)
            with open(path, "rb") as stream:
                contents[os.path.relpath(path, root)] = stream.read()
    return contents


class GeneratorTest(unittest.TestCase):
    def deterministic_generation(self, generate):
        temp_root = os.path.join(REPO, "target", "semi_naive")
        os.makedirs(temp_root, exist_ok=True)
        with tempfile.TemporaryDirectory(
            prefix="semi-naive-generator-a-", dir=temp_root
        ) as first, tempfile.TemporaryDirectory(
            prefix="semi-naive-generator-b-", dir=temp_root
        ) as second:
            generate(first)
            generate(second)
            self.assertEqual(tree_bytes(first), tree_bytes(second))
            return tree_bytes(first)

    def test_process_calculus_is_deterministic_and_checks_the_sum(self):
        contents = self.deterministic_generation(
            lambda root: gen_process_calculus.generate(root, ((3, 4), (0, 0)))
        )
        self.assertEqual(
            contents["process_calculus_003_004.required"],
            b"(petri (! result (S (S (S (S (S (S (S Z)))))))))\n",
        )
        source = contents["process_calculus_003_004.source.mm2"]
        self.assertEqual(source.count(b"(exec "), 2)
        self.assertIn(b"(petri (! (add result)", source)

    def test_transitive_is_deterministic_and_has_the_requested_edges(self):
        contents = self.deterministic_generation(
            lambda root: gen_transitive.generate(root, (1, 4))
        )
        self.assertEqual(
            contents["transitive_chain_001.source.mm2"].count(b"(edge "),
            4,
        )
        self.assertEqual(
            contents["transitive_chain_004.source.mm2"].count(b"(edge "),
            7,
        )

    def test_process_instance_parser_rejects_negative_operands(self):
        with self.assertRaises(argparse.ArgumentTypeError):
            gen_process_calculus.parse_instance("-1:2")

    def test_transitive_length_rejects_zero(self):
        with self.assertRaises(argparse.ArgumentTypeError):
            gen_transitive.positive_integer("0")


if __name__ == "__main__":
    unittest.main()
