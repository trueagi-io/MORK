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
                memory=1, pattern="$", template="_1"):
        args = ["convert", source, target, pattern, template, input_path]
        if output_path is not None:
            args.append(output_path)
        args += ["--memory-mib", str(memory), "--temp-dir", self.scratch]
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

    def test_external_sort_multiple_runs_and_empty_paths(self):
        source = self.root / "input.upaths"
        output = self.root / "output.paths"
        # Exceeds the 1 MiB budget and forces multiple runs and merge levels.
        records = [i.to_bytes(4, "big") + b"x" * 96 for i in range(20_000, -1, -1)]
        records += records[::7] + [b"", b"", b"\0", b"\0\xff", b"\xff"]
        write_paths(source, records)
        self.convert("upaths", "paths", source, output)
        self.assertEqual(read_paths(output), sorted(set(records)))
        self.assertEqual(list(self.scratch.iterdir()), [])
        write_paths(source, [])
        self.convert("upaths", "paths", source, output)
        self.assertEqual(read_paths(output), [])

    def test_sort_failure_preserves_output_and_cleans_runs(self):
        source = self.root / "input.upaths"
        output = self.root / "output.paths"
        write_paths(source, [i.to_bytes(4, "big") + b"x" * 96 for i in range(20_000)])
        valid = source.read_bytes()
        output.write_bytes(b"existing destination")
        oversized = zlib.compress(struct.pack("<I", 1 << 30))
        for damaged in [valid[:-1], valid + b"trailing", valid[:-1] + bytes([valid[-1] ^ 1]), oversized]:
            with self.subTest(size=len(damaged)):
                source.write_bytes(damaged)
                self.convert("upaths", "paths", source, output, success=False)
                self.assertEqual(output.read_bytes(), b"existing destination")
                self.assertEqual(list(self.scratch.iterdir()), [])
        source.write_bytes(valid)
        self.convert("upaths", "paths", source, output, memory=0, success=False)
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
        write_paths(source, [b"abc"])
        source.write_bytes(source.read_bytes()[:-1])
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
        self.convert("mm2", "act", source, direct, memory=0, success=False)
        self.assertEqual(direct.read_bytes(), before)
        self.assertEqual(list(self.scratch.iterdir()), [])

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
        output = self.root / "rejected.upaths"
        self.convert("mm2", "upaths", source, output, pattern="(a)", success=False)
        self.assertFalse(output.exists())

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
