#!/usr/bin/env python3
"""End-to-end conversion tests (default-feature mork build).

cargo build -p mork --release
python3 kernel/tests/test_conversions.py --mork target/release/mork
"""
import argparse
import os
from pathlib import Path
import struct
import subprocess
import tempfile
import unittest
import zlib


MORK = Path(__file__).resolve().parents[2] / "target/release/mork"


def write_paths(path, records):
    payload = b"".join(struct.pack("<I", len(record)) + record for record in records)
    path.write_bytes(zlib.compress(payload))


def read_paths(path):
    decoder = zlib.decompressobj()
    payload = decoder.decompress(path.read_bytes()) + decoder.flush()
    if not decoder.eof or decoder.unused_data:
        raise ValueError("incomplete paths stream or trailing data")
    records = []
    offset = 0
    while offset < len(payload):
        size, = struct.unpack_from("<I", payload, offset)
        offset += 4
        end = offset + size
        if end > len(payload):
            raise ValueError("truncated path")
        records.append(payload[offset:end])
        offset = end
    return records


class ConversionTests(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory(prefix="mork-conversion-")
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        self.scratch = self.root / "sort runs"
        self.scratch.mkdir()

    def invoke(self, *args, success=True):
        result = subprocess.run(
            [str(MORK), *map(str, args)], cwd=self.root,
            capture_output=True, text=True, timeout=60,
        )
        diagnostic = f"{result.args!r}\nstdout:\n{result.stdout}\nstderr:\n{result.stderr}"
        if success:
            self.assertEqual(result.returncode, 0, diagnostic)
        else:
            self.assertNotEqual(result.returncode, 0, diagnostic)
        return result

    def convert(self, source, target, input_path, output_path=None, *, success=True,
                xmx=1, pattern="$", template="_1"):
        args = ["convert", source, target, pattern, template, input_path]
        if output_path is not None:
            args.append(output_path)
        args += ["--xmx", str(xmx), "--temp-dir", self.scratch]
        return self.invoke(*args, success=success)

    def test_upaths_preserve_order_duplicates_and_destination_on_error(self):
        source = self.root / "input.mm2"
        output = self.root / "output.upaths"
        source.write_text("(z $v $v) (a) (z $v $v)")
        result = self.convert("mm2", "upaths", source, output)
        self.assertIn("wrote 3 paths", result.stdout)
        records = read_paths(output)
        self.assertEqual(len(records), 3)
        self.assertEqual(records[0], records[2])
        self.assertGreater(records[0], records[1])
        before = output.read_bytes()
        for bad in ["(", ")", "(a", "(a ; unfinished", '"escape\\']:
            with self.subTest(input=bad):
                source.write_text(bad)
                self.convert("mm2", "upaths", source, output, success=False)
                self.assertEqual(output.read_bytes(), before)
        self.assertEqual(set(self.root.iterdir()), {source, output, self.scratch})

    def test_mmap_parser_matches_existing_conversion(self):
        source = self.root / "input.mm2"
        output = self.root / "output.upaths"
        expected = self.root / "expected.paths"
        for text in [
            "", "; trailing comment",
            '; comment\n(foo (bar $x) $x $y "multi\nline") () $v $v abc',
            f"(outer (inner {'x' * 200_000}) $x $x) (next $x $x)",
            '(z $x $x) (a (b) "string") (z $x $x) (prefix) ()',
        ]:
            with self.subTest(input_length=len(text)):
                source.write_text(text)
                self.convert("mm2", "upaths", source, output)
                actual = sorted(set(read_paths(output)))
                if not text:
                    self.assertEqual(actual, [])
                else:
                    self.convert("metta", "paths", source, expected)
                    self.assertEqual(actual, read_paths(expected))

    def test_external_sort_and_empty_paths(self):
        source = self.root / "input.upaths"
        output = self.root / "output.paths"
        records = [i.to_bytes(4, "big") + b"x" * 96 for i in range(20_000, -1, -1)]
        records += records[::7] + [b"", b"", b"\0", b"\0\xff", b"\xff"]
        write_paths(source, records)
        self.convert("upaths", "paths", source, output)
        self.assertEqual(read_paths(output), sorted(set(records)))
        self.assertEqual(list(self.scratch.iterdir()), [])
        write_paths(source, [])
        self.convert("upaths", "paths", source, output)
        self.assertEqual(read_paths(output), [])

    def test_sort_read_failure_preserves_output_and_cleans_intermediates(self):
        source = self.root / "input.upaths"
        output = self.root / "output.paths"
        source.mkdir()
        output.write_bytes(b"existing destination")
        self.convert("upaths", "paths", source, output, success=False)
        self.assertEqual(output.read_bytes(), b"existing destination")
        self.assertEqual(list(self.scratch.iterdir()), [])
        self.convert("upaths", "paths", source, output, xmx=0, success=False)
        self.assertEqual(output.read_bytes(), b"existing destination")
        self.assertEqual(set(self.root.iterdir()), {source, output, self.scratch})

    def test_act_empty_prefix_paths_and_invalid_input(self):
        source = self.root / "input.paths"
        output = self.root / "output.act"
        for records in [[], [b""], [b"", b"\0", b"\0\0", b"\0\xff", b"\xff"]]:
            with self.subTest(records=records):
                write_paths(source, records)
                result = self.convert("paths", "act", source, output)
                self.assertIn(f"wrote {len(records)} paths", result.stdout)
                self.assertGreater(output.stat().st_size, 0)
        before = output.read_bytes()
        for records in [[b"\2", b"\1"], [b"\1", b"\1"]]:
            write_paths(source, records)
            self.convert("paths", "act", source, output, success=False)
            self.assertEqual(output.read_bytes(), before)
        self.assertEqual(set(self.root.iterdir()), {source, output, self.scratch})

    def test_direct_act_matches_stages_and_cleans_intermediates(self):
        source = self.root / "input.mm2"
        unordered = self.root / "input.upaths"
        ordered = self.root / "input.paths"
        staged = self.root / "staged.act"
        direct = self.root / "direct.act"
        source.write_text('(z $x $x) (a (b) "string") (z $x $x) (prefix) ()')
        self.convert("mm2", "upaths", source, unordered)
        self.convert("upaths", "paths", unordered, ordered)
        self.convert("paths", "act", ordered, staged)
        result = self.convert("mm2", "act", source, direct)
        self.assertIn("wrote 4 paths", result.stdout)
        self.assertEqual(direct.read_bytes(), staged.read_bytes())
        self.assertEqual(list(self.scratch.iterdir()), [])
        before = direct.read_bytes()
        source.write_text("(bad")
        self.convert("mm2", "act", source, direct, success=False)
        self.assertEqual(direct.read_bytes(), before)
        self.assertEqual(list(self.scratch.iterdir()), [])
        self.convert("mm2", "act", source, direct, xmx=0, success=False)
        self.assertEqual(direct.read_bytes(), before)
        self.assertEqual(list(self.scratch.iterdir()), [])

    def test_missing_shortcuts_match_stages(self):
        source = self.root / "input.mm2"
        unordered = self.root / "input.upaths"
        ordered = self.root / "staged.paths"
        staged_act = self.root / "staged.act"
        direct_paths = self.root / "direct.paths"
        direct_act = self.root / "direct.act"
        for text in ["", "(z $x $x) (a) (z $x $x) ()"]:
            with self.subTest(input=text):
                source.write_text(text)
                self.convert("mm2", "upaths", source, unordered)
                self.convert("upaths", "paths", unordered, ordered)
                self.convert("paths", "act", ordered, staged_act)
                self.convert("mm2", "paths", source, direct_paths)
                self.convert("upaths", "act", unordered, direct_act)
                self.assertEqual(read_paths(direct_paths), read_paths(ordered))
                self.assertEqual(direct_act.read_bytes(), staged_act.read_bytes())
                self.assertEqual(list(self.scratch.iterdir()), [])
                self.assertTrue(unordered.is_file())

    def test_json_shortcuts_match_existing_conversion(self):
        source = self.root / "input.json"
        unordered = self.root / "input.upaths"
        ordered = self.root / "staged.paths"
        staged_act = self.root / "staged.act"
        direct_paths = self.root / "direct.paths"
        direct_act = self.root / "direct.act"
        expected = self.root / "expected.metta"
        actual = self.root / "actual.metta"
        for text in ['{}', '[]', 'null',
                     '{"z":[1,true,null,"text"],"a":{"nested":false,"empty":[]}}',
                     '{"dup":1,"dup":1}']:
            with self.subTest(input=text):
                source.write_text(text)
                self.convert("json", "upaths", source, unordered)
                self.convert("upaths", "paths", unordered, ordered)
                self.convert("paths", "act", ordered, staged_act)
                self.convert("json", "paths", source, direct_paths)
                self.convert("json", "act", source, direct_act)
                self.assertEqual(read_paths(direct_paths), read_paths(ordered))
                self.assertEqual(direct_act.read_bytes(), staged_act.read_bytes())
                self.convert("json", "metta", source, expected)
                self.convert("paths", "metta", direct_paths, actual)
                self.assertEqual(set(actual.read_text().splitlines()), set(expected.read_text().splitlines()))
                self.assertEqual(list(self.scratch.iterdir()), [])

    def test_shortcut_failures_preserve_output_and_clean_intermediates(self):
        cases = [("mm2", "paths", b"(bad"),
                 ("upaths", "act", None)]
        for target in ["upaths", "paths", "act"]:
            for bad in [b"", b'{"ok":1,"bad":', b'{"ok":1} trailing']:
                cases.append(("json", target, bad))
        for source_format, target_format, content in cases:
            with self.subTest(source=source_format, target=target_format, content=content):
                source = self.root / ("input." + source_format)
                output = self.root / ("output." + target_format)
                if content is None:
                    source.mkdir()
                else:
                    source.write_bytes(content)
                output.write_bytes(b"existing destination")
                before_files = set(self.root.iterdir())
                result = self.convert(source_format, target_format, source, output, success=False)
                self.assertIn("conversion failed:", result.stderr)
                self.assertEqual(output.read_bytes(), b"existing destination")
                self.assertEqual(list(self.scratch.iterdir()), [])
                self.assertEqual(set(self.root.iterdir()), before_files)
        for source_format, target_format in [("mm2", "paths"), ("upaths", "act"),
                                             ("json", "paths"), ("json", "act")]:
            with self.subTest(source=source_format, target=target_format, invalid_options=True):
                source = self.root / ("input." + source_format)
                output = self.root / ("output." + target_format)
                output.write_bytes(b"existing destination")
                self.convert(source_format, target_format, source, output, xmx=0, success=False)
                self.assertEqual(output.read_bytes(), b"existing destination")
                self.assertEqual(list(self.scratch.iterdir()), [])

    def test_streaming_conversion_matrix(self):
        source = self.root / "input.mm2"
        source.write_text('(p z a) (p a z) (p z a) (v $x $x) () "two words"')
        unordered = self.root / "input.upaths"
        self.convert("mm2", "upaths", source, unordered)
        records = read_paths(unordered)
        for source_format in ["mm2", "metta", "upaths", "paths", "act"]:
            input_path = self.root / ("matrix-input." + source_format)
            self.convert("mm2", source_format, source, input_path)
            expected = sorted(set(records)) if source_format in ["paths", "act"] else records
            for target_format in ["mm2", "metta", "upaths", "paths", "act"]:
                with self.subTest(source=source_format, target=target_format):
                    output = self.root / ("matrix-output." + target_format)
                    self.convert(source_format, target_format, input_path, output)
                    check = self.root / "check.upaths"
                    self.convert(target_format, "upaths", output, check)
                    self.assertEqual(read_paths(check),
                                     sorted(set(expected)) if target_format in ["paths", "act"] else expected)
                    self.assertEqual(list(self.scratch.iterdir()), [])

    def test_full_unification_and_template_application(self):
        # Variables on either side, repeated-variable constraints, and cyclic
        # substitutions (including cycles discarded by a constant template).
        cases = [
            ("(p $x $x) (p a b) (p a a)", "[3] p a $", "[2] out _1", "(out a) (out b) (out a)"),
            ("(p $x a) (p b b) (p a b)", "[3] p $ _1", "[2] out _1", "(out a) (out b)"),
            ("(p $x (f $x))", "[3] p $ $", "[4] q _2 _1 _2", "(q (f $a) $a (f $a))"),
            ("(p $x $x)", "[3] p $ $", "[4] q $ _1 _2", "(q $a $b $b)"),
            ("(p (f $y) $y) (p a (f a))", "[3] p $ [2] f _1", "ok", "ok"),
            ("(p z a) (p a z) (p z a)", "[3] p $ $", "[3] r _2 _1", "(r a z) (r z a) (r a z)"),
            ("(p a) (q a)", "[2] missing $", "_1", ""),
        ]
        source = self.root / "source.mm2"
        expected_file = self.root / "expected.mm2"
        check = self.root / "check.upaths"
        for data, pattern, template, expected in cases:
            source.write_text(data)
            expected_file.write_text(expected)
            self.convert("mm2", "upaths", expected_file, check)
            expected_records = read_paths(check)
            for source_format in ["mm2", "upaths", "paths", "act"]:
                input_path = self.root / ("unify-input." + source_format)
                self.convert("mm2", source_format, source, input_path)
                for target_format in ["mm2", "upaths", "paths", "act"]:
                    with self.subTest(data=data, pattern=pattern, template=template,
                                      source=source_format, target=target_format):
                        output = self.root / ("unify-output." + target_format)
                        self.convert(source_format, target_format, input_path, output,
                                     pattern=pattern, template=template)
                        self.convert(target_format, "upaths", output, check)
                        actual = read_paths(check)
                        self.assertEqual(sorted(set(actual)), sorted(set(expected_records)))
                        if source_format in ["mm2", "upaths"] and target_format in ["mm2", "upaths"]:
                            self.assertEqual(actual, expected_records)
                        self.assertEqual(list(self.scratch.iterdir()), [])

    def test_json_streaming_transform(self):
        source = self.root / "input.json"
        source.write_text('{"p":["z","a"],"q":true}')
        expected = self.root / "expected.mm2"
        expected.write_text("(result z 0) (result a 1)")
        check = self.root / "check.upaths"
        self.convert("mm2", "upaths", expected, check)
        records = read_paths(check)
        for target_format in ["mm2", "metta", "upaths", "paths", "act"]:
            with self.subTest(target=target_format):
                output = self.root / ("json-output." + target_format)
                self.convert("json", target_format, source, output,
                             pattern="[2] p [2] $ $", template="[3] result _2 _1")
                self.convert(target_format, "upaths", output, check)
                self.assertEqual(read_paths(check),
                                 sorted(records) if target_format in ["paths", "act"] else records)
                self.assertEqual(list(self.scratch.iterdir()), [])

    def test_streaming_expansion(self):
        source = self.root / "large.mm2"
        term = "x"
        for _ in range(11):
            term = f"(f {term} {term})"
        source.write_text(f"(p {term})")
        output = self.root / "large-output.mm2"
        self.convert("mm2", "mm2", source, output,
                     pattern="[2] p $", template="[3] q _1 _1")
        self.assertEqual(output.read_text(), f"(q {term} {term})\n")

    def test_invalid_expression_paths_in_debug(self):
        source = self.root / "empty.mm2"
        source.write_text("")
        output = self.root / "output.mm2"
        result = self.convert("mm2", "mm2", source, output)
        if "WARNING running in debug" not in result.stdout:
            self.skipTest("expression validation is debug-only")
        source = self.root / "bad.paths"
        for path in [b"", b"\x40", b"\xc3ab", b"\x02\xc1a", b"\x80", b"\x00\x00"]:
            write_paths(source, [path])
            for target_format, pattern in [("mm2", "$"), ("upaths", "[1] $")]:
                with self.subTest(path=path, target=target_format):
                    output.write_bytes(b"keep me")
                    self.convert("paths", target_format, source, output,
                                 pattern=pattern, success=False)
                    self.assertEqual(output.read_bytes(), b"keep me")
                    self.assertEqual(list(self.scratch.iterdir()), [])

    def test_direct_streams_need_no_scratch_directory(self):
        source = self.root / "input.mm2"
        source.write_text("(p z) (p a) (p z)")
        for source_format in ["mm2", "upaths", "paths"]:
            input_path = self.root / ("stream-input." + source_format)
            self.convert("mm2", source_format, source, input_path)
            for target_format in ["mm2", "upaths"]:
                for pattern, template in [("$", "_1"), ("[2] p $", "[2] q _1")]:
                    with self.subTest(source=source_format, target=target_format, pattern=pattern):
                        output = self.root / ("stream-output." + target_format)
                        before = set(self.root.iterdir())
                        self.invoke("convert", source_format, target_format, pattern, template,
                                    input_path, output, "--temp-dir", self.root / "does-not-exist")
                        self.assertEqual(set(self.root.iterdir()), before | {output})
                        self.assertEqual(list(self.scratch.iterdir()), [])
                        self.assertGreater(output.stat().st_size, 0)

    def test_streaming_same_file_and_error_preservation(self):
        source = self.root / "same.mm2"
        source.write_text("(p a) (p b) (q c)")
        self.convert("mm2", "mm2", source, source, pattern="[2] p $", template="[2] r _1")
        self.assertEqual(source.read_text(), "(r a)\n(r b)\n")
        paths = self.root / "same.paths"
        self.convert("mm2", "paths", source, paths)
        self.convert("paths", "paths", paths, paths, pattern="[2] r $", template="one")
        self.assertEqual(len(read_paths(paths)), 1)
        for target_format in ["mm2", "upaths", "paths", "act"]:
            output = self.root / ("preserved." + target_format)
            output.write_bytes(b"keep me")
            source.write_text("(p a) (p b) (")
            self.convert("mm2", target_format, source, output, success=False,
                         pattern="[2] p $", template="[2] r _1")
            self.assertEqual(output.read_bytes(), b"keep me")
            self.assertEqual(list(self.scratch.iterdir()), [])

    def test_xmx_accepts_gib_and_rejects_invalid_budgets(self):
        source = self.root / "input.mm2"
        output = self.root / "output.paths"
        source.write_text("(a)")
        for budget in [1, 2]:
            with self.subTest(xmx=budget):
                self.convert("mm2", "paths", source, output, xmx=budget)
                self.assertEqual(read_paths(output), [b"\1\xc1a"])
        before = output.read_bytes()
        for budget in [0, "0.5", "NaN", "inf", "1e100", str(1 << 60)]:
            with self.subTest(xmx=budget):
                result = self.convert("mm2", "paths", source, output, xmx=budget, success=False)
                self.assertIn("--xmx", result.stderr)
                self.assertEqual(output.read_bytes(), before)
                self.assertEqual(list(self.scratch.iterdir()), [])
        help_text = self.invoke("convert", "--help").stdout
        self.assertIn("--xmx", help_text)
        self.assertIn("GiB", help_text)
        self.assertNotIn("--memory-mib", help_text)

    def test_act_reuses_repeated_lines(self):
        source = self.root / "input.paths"
        output = self.root / "output.act"
        suffix = b"x" * 140_000
        write_paths(source, [bytes([index]) + suffix for index in range(8)])
        self.convert("paths", "act", source, output)
        self.assertLess(output.stat().st_size, len(suffix) * 2)

    def test_explicit_cli_fields_and_default_output(self):
        source = self.root / "input with spaces.mm2"
        source.write_text("(a)")
        self.convert("mm2", "upaths", source)
        self.assertEqual(read_paths(source.with_suffix(".upaths")), [b"\1\xc1a"])
        self.convert("mm2", "act", source)
        self.assertTrue(source.with_suffix(".act").is_file())
        self.assertEqual(list(self.scratch.iterdir()), [])
        help_text = self.invoke("convert", "--help").stdout
        for field in ["<PATTERN>", "<TEMPLATE>", "<INPUT_PATH>", "[OUTPUT_PATH]"]:
            self.assertIn(field, help_text)
        output = self.root / "filtered.upaths"
        self.convert("mm2", "upaths", source, output, pattern="[1] a", template="matched")
        self.assertEqual(read_paths(output), [b"\xc7matched"])

    @unittest.skipUnless(Path("/dev/shm").is_dir() and os.access("/dev/shm", os.W_OK),
                         "mork ACT queries currently require writable /dev/shm")
    def test_streamed_act_is_queryable_on_disk(self):
        # Resolve through the fixed ACT directory while keeping the ACT on the test filesystem.
        act_directory = tempfile.TemporaryDirectory(prefix="mork-conversion-", dir="/dev/shm")
        self.addCleanup(act_directory.cleanup)
        act = self.root / "input.act"
        alias = Path(act_directory.name) / "input.act"
        alias.symlink_to(act)
        name = alias.relative_to("/dev/shm").with_suffix("").as_posix()
        source = self.root / "input.mm2"
        program = self.root / "query.mm2"
        output = self.root / "results.metta"
        source.write_text("(in 0 g0) (in 1 g1) (in 10 g10)")
        self.convert("mm2", "act", source, act)
        program.write_text(f"(exec 0 (I (ACT {name} (in $x $y))) (, (found $x $y)))")
        self.invoke("run", program, output, "--steps", "10")
        self.assertEqual(set(output.read_text().splitlines()),
                         {"(found 0 g0)", "(found 1 g1)", "(found 10 g10)"})


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mork", type=Path, default=MORK)
    args, remaining = parser.parse_known_args()
    MORK = args.mork.resolve()
    if not MORK.is_file():
        parser.error(f"mork binary not found: {MORK}; build it first")
    unittest.main(argv=[__file__, *remaining])
