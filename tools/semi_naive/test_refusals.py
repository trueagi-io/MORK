#!/usr/bin/env python3

import os
import subprocess
import sys
import tempfile
import unittest


HERE = os.path.dirname(os.path.abspath(__file__))
REFUSALS = os.path.join(HERE, "corpus", "refusals")
EXPECTED = os.path.join(HERE, "expected", "i3", "refusals.expected")
TRANSFORM = os.path.join(HERE, "transform.py")


def expected_refusals():
    refusals = []
    with open(EXPECTED, "r", encoding="utf-8") as stream:
        for line in stream:
            filename, reason = line.rstrip("\n").split("|", 1)
            refusals.append((filename, reason))
    return refusals


class RefusalTest(unittest.TestCase):
    def test_refusal_matrix(self):
        expected = expected_refusals()
        self.assertEqual(
            [filename for filename, _ in expected], sorted(os.listdir(REFUSALS))
        )
        with tempfile.TemporaryDirectory() as workdir:
            for filename, reason in expected:
                with self.subTest(filename=filename):
                    output = os.path.join(workdir, filename)
                    completed = subprocess.run(
                        [
                            sys.executable,
                            TRANSFORM,
                            os.path.join(REFUSALS, filename),
                            output,
                        ],
                        stdout=subprocess.PIPE,
                        stderr=subprocess.PIPE,
                        check=False,
                    )
                    self.assertEqual(completed.returncode, 2)
                    self.assertEqual(completed.stdout, b"")
                    self.assertEqual(
                        completed.stderr,
                        ("REFUSE %s\n" % reason).encode("utf-8"),
                    )
                    self.assertFalse(os.path.exists(output))

    def test_parse_error_is_named_and_writes_nothing(self):
        with tempfile.TemporaryDirectory() as workdir:
            source = os.path.join(workdir, "broken.mm2")
            output = os.path.join(workdir, "output.mm2")
            with open(source, "w", encoding="utf-8") as stream:
                stream.write("(broken")
            completed = subprocess.run(
                [sys.executable, TRANSFORM, source, output],
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                check=False,
            )
            self.assertEqual(completed.returncode, 2)
            self.assertEqual(
                completed.stderr,
                b"REFUSE PARSE_ERROR: unterminated expression at end of input\n",
            )
            self.assertFalse(os.path.exists(output))


if __name__ == "__main__":
    unittest.main()
