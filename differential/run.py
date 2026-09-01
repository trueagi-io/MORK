#!/usr/bin/env python3
"""Differential test harness for the MORK kernel.

Runs every .mm2 program in the corpus through two builds of the `mork` CLI --
the ProductZipper reference (`cargo build --release -p mork`) and the leapfrog
join (`... --features leapfrog`) -- and compares, byte for byte, the space each
one dumps as well as the number of steps each one reports executing.  A program
may additionally carry a checked-in expected space, in which case the corpus
doubles as a plain regression suite that does not need two engines at all.

Standard library only, no build-time dependencies.  See README.md.
"""

import argparse
import concurrent.futures
import os
import re
import shutil
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(HERE)
DEFAULT_CORPUS = [os.path.join(HERE, "corpus"), os.path.join(REPO, "kernel", "resources")]

# `mork run` prints exactly one line of the form
#   executing 12 steps took 3 ms (unifications ...)
STEPS_RE = re.compile(rb"executing (\d+) steps")

# Directives live in ordinary mm2 comments so a program stays a runnable
# program.  Only the leading comment block is scanned.
DIRECTIVE_RE = re.compile(r"^\s*;+\s*@(\w[\w-]*)\s*(.*?)\s*$")

DEFAULT_STEPS = 1000000000000000  # the CLI's own default; means "run to fixpoint"


class Program:
    __slots__ = ("path", "name", "steps", "expect", "expect_steps", "aux",
                 "tags", "skip", "desc", "generated")

    def __init__(self, path, name):
        self.path = path
        self.name = name
        self.steps = DEFAULT_STEPS
        self.expect = None        # abs path to a checked-in space dump
        self.expect_steps = None  # int, pinned "executing N steps"
        self.aux = []             # extra --aux-path files
        self.tags = set()
        self.skip = None          # reason string
        self.desc = None
        self.generated = False


def parse_program(path, root):
    rel = os.path.relpath(path, root)
    name = os.path.splitext(rel)[0].replace(os.sep, "/")
    p = Program(path, name)
    base = os.path.dirname(path)

    if os.path.getsize(path) == 0:
        p.skip = "empty file"
        return p

    with open(path, "r", encoding="utf-8", errors="replace") as f:
        for line in f:
            stripped = line.strip()
            if not stripped:
                continue
            if not stripped.startswith(";"):
                break  # leading comment block is over
            m = DIRECTIVE_RE.match(line)
            if not m:
                continue
            key, val = m.group(1), m.group(2)
            if key == "steps":
                p.steps = int(val)
            elif key == "expect":
                # bare `@expect` -> the shared differential/expected tree, keyed by
                # the program's corpus-relative name; `@expect foo` -> next to the
                # program.  Only programs that ask for one get one, so a benchmark
                # whose space dump is tens of megabytes stays differential-only.
                p.expect = (os.path.join(base, val) if val
                            else os.path.join(HERE, "expected", name + ".expected"))
            elif key in ("expect-steps", "expect_steps"):
                p.expect_steps = int(val)
            elif key == "aux":
                p.aux.append(os.path.join(base, val))
            elif key == "tags":
                p.tags.update(val.split())
            elif key == "skip":
                p.skip = val or "declared @skip"
            elif key == "desc":
                p.desc = val

    return p


def discover(roots, filters, want_tags, include_slow):
    progs = []
    for root in roots:
        if not os.path.isdir(root):
            continue
        for dirpath, dirnames, filenames in os.walk(root):
            dirnames[:] = [d for d in sorted(dirnames) if not d.startswith(".")]
            for fn in sorted(filenames):
                if not fn.endswith(".mm2") or fn.startswith("#") or fn.startswith("."):
                    continue
                progs.append(parse_program(os.path.join(dirpath, fn), root))

    seen = {}
    for p in progs:
        seen.setdefault(p.name, p)
    progs = list(seen.values())
    progs.sort(key=lambda p: p.name)

    if filters:
        progs = [p for p in progs if any(f in p.name for f in filters)]
    if want_tags:
        progs = [p for p in progs if p.tags & want_tags]
    if not include_slow:
        for p in progs:
            if "slow" in p.tags and p.skip is None:
                p.skip = "tagged slow (pass --slow to include)"
    return progs


def run_engine(binary, prog, out_path, log_path, timeout):
    cmd = [binary, "run", prog.path, "--steps", str(prog.steps)]
    for a in prog.aux:
        cmd += ["--aux-path", a]
    cmd.append(out_path)
    t0 = time.time()
    try:
        cp = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                            timeout=timeout)
        out, code = cp.stdout, cp.returncode
    except subprocess.TimeoutExpired as e:
        out, code = (e.output or b"") + b"\n<TIMEOUT>\n", -9
    elapsed = time.time() - t0
    with open(log_path, "wb") as f:
        f.write(out)
    m = STEPS_RE.search(out)
    steps = int(m.group(1)) if m else None
    return code, steps, elapsed


def read_bytes(path):
    try:
        with open(path, "rb") as f:
            return f.read()
    except OSError:
        return None


def check(prog, pz_bin, lf_bin, workdir, timeout, update):
    if prog.skip:
        return ("SKIP", prog.skip, 0.0)

    slot = os.path.join(workdir, prog.name.replace("/", "__"))
    os.makedirs(os.path.dirname(slot) or workdir, exist_ok=True)
    problems = []
    total = 0.0

    results = {}
    for tag, binary in (("pz", pz_bin), ("lf", lf_bin)):
        if binary is None:
            continue
        code, steps, el = run_engine(binary, prog, slot + "." + tag + ".space",
                                     slot + "." + tag + ".log", timeout)
        total += el
        results[tag] = (code, steps, read_bytes(slot + "." + tag + ".space"))

    for tag, (code, steps, space) in results.items():
        if code != 0:
            problems.append("%s exited %d (see %s.%s.log)" % (tag, code, slot, tag))
        elif space is None:
            problems.append("%s wrote no space file" % tag)

    if "pz" in results and "lf" in results and not problems:
        pc, ps, pspace = results["pz"]
        lc, ls, lspace = results["lf"]
        if ps != ls:
            problems.append("step count differs: pz=%s lf=%s" % (ps, ls))
        if pspace != lspace:
            problems.append("space differs: pz=%d bytes lf=%d bytes%s"
                            % (len(pspace), len(lspace), first_diff(pspace, lspace)))

    # The reference arm for the expected file is the ProductZipper when present.
    ref_tag = "pz" if "pz" in results else ("lf" if "lf" in results else None)
    if ref_tag and not problems:
        _, ref_steps, ref_space = results[ref_tag]
        if update:
            if prog.expect is not None:
                os.makedirs(os.path.dirname(prog.expect), exist_ok=True)
                with open(prog.expect, "wb") as f:
                    f.write(ref_space)
            if prog.expect_steps is not None and prog.expect_steps != ref_steps:
                rewrite_expect_steps(prog.path, ref_steps)
        else:
            if prog.expect is not None:
                want = read_bytes(prog.expect)
                if want is None:
                    problems.append("expected file %s is missing" % prog.expect)
                else:
                    for tag, (_, _, space) in results.items():
                        if space != want:
                            problems.append("%s space != %s%s"
                                            % (tag, os.path.basename(prog.expect),
                                               first_diff(want, space)))
            if prog.expect_steps is not None:
                for tag, (_, steps, _) in results.items():
                    if steps != prog.expect_steps:
                        problems.append("%s executed %s steps, expected %d"
                                        % (tag, steps, prog.expect_steps))

    if problems:
        return ("FAIL", "; ".join(problems), total)
    return ("OK", "", total)


def first_diff(a, b):
    if a is None or b is None:
        return ""
    n = min(len(a), len(b))
    i = 0
    while i < n and a[i] == b[i]:
        i += 1
    line = a[:i].count(b"\n") + 1
    return " (first difference at byte %d, line %d)" % (i, line)


def rewrite_expect_steps(path, steps):
    with open(path, "r", encoding="utf-8") as f:
        text = f.read()
    new = re.sub(r"(?m)^(\s*;+\s*@expect[-_]steps\s+)\d+\s*$",
                 lambda m: m.group(1) + str(steps), text, count=1)
    if new != text:
        with open(path, "w", encoding="utf-8") as f:
            f.write(new)


def cargo_build(features, dest):
    cmd = ["cargo", "build", "--release", "-p", "mork"]
    if features:
        cmd += ["--features", features]
    print("+ " + " ".join(cmd), flush=True)
    cp = subprocess.run(cmd, cwd=REPO)
    if cp.returncode != 0:
        sys.exit("build failed: " + " ".join(cmd))
    built = os.path.join(REPO, "target", "release", "mork")
    os.makedirs(os.path.dirname(dest), exist_ok=True)
    shutil.copy2(built, dest)  # the two builds share target/release/mork
    return dest


def run_generators(outdir, names):
    gendir = os.path.join(HERE, "generators")
    if not os.path.isdir(gendir):
        return
    os.makedirs(outdir, exist_ok=True)
    for fn in sorted(os.listdir(gendir)):
        if not fn.endswith(".py"):
            continue
        if names and not any(n in fn for n in names):
            continue
        cp = subprocess.run([sys.executable, os.path.join(gendir, fn), outdir])
        if cp.returncode != 0:
            sys.exit("generator failed: " + fn)


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("filter", nargs="*", help="only run programs whose name contains one of these")
    ap.add_argument("--pz", help="path to the ProductZipper (no-feature) mork binary")
    ap.add_argument("--lf", help="path to the leapfrog mork binary")
    ap.add_argument("--build", action="store_true", help="cargo-build both binaries first")
    ap.add_argument("--single", choices=("pz", "lf"),
                    help="run only one engine (regression mode; needs expected files)")
    ap.add_argument("--corpus", action="append", default=None,
                    help="corpus root (repeatable); default: differential/corpus and kernel/resources")
    ap.add_argument("--workdir", default=os.path.join(REPO, "target", "differential"))
    ap.add_argument("--generated", action="store_true",
                    help="also run differential/generators/*.py and include what they emit")
    ap.add_argument("--slow", action="store_true", help="include programs tagged slow")
    ap.add_argument("--tag", action="append", default=[], help="only programs carrying this tag")
    ap.add_argument("--update-expected", action="store_true",
                    help="(re)write each program's .expected from the reference engine")
    ap.add_argument("--timeout", type=float, default=300.0, help="per-run timeout in seconds")
    ap.add_argument("-j", "--jobs", type=int, default=max(1, (os.cpu_count() or 2) // 2))
    ap.add_argument("--list", action="store_true", help="list the corpus and exit")
    ap.add_argument("-v", "--verbose", action="store_true")
    args = ap.parse_args()

    workdir = os.path.abspath(args.workdir)
    os.makedirs(workdir, exist_ok=True)

    roots = [os.path.abspath(r) for r in (args.corpus or DEFAULT_CORPUS)]
    gen_root = os.path.join(workdir, "generated")
    if args.generated:
        run_generators(gen_root, args.filter)
        roots.append(gen_root)

    progs = discover(roots, args.filter, set(args.tag), args.slow)
    if not progs:
        sys.exit("no programs matched")

    if args.list:
        for p in progs:
            bits = ["steps=%d" % p.steps]
            if p.expect:
                bits.append("expect")
            if p.tags:
                bits.append("tags=" + ",".join(sorted(p.tags)))
            if p.skip:
                bits.append("SKIP:" + p.skip)
            print("%-46s %s" % (p.name, " ".join(bits)))
        return 0

    pz = args.pz
    lf = args.lf
    if args.build:
        if args.single != "lf":
            pz = cargo_build(None, os.path.join(workdir, "mork-pz"))
        if args.single != "pz":
            lf = cargo_build("leapfrog", os.path.join(workdir, "mork-leapfrog"))
    if args.single == "pz":
        lf = None
    if args.single == "lf":
        pz = None
    if pz is None and lf is None:
        sys.exit("need --pz and/or --lf (or --build)")
    for b in (pz, lf):
        if b is not None and not os.access(b, os.X_OK):
            sys.exit("not executable: %s" % b)
    if pz is not None and lf is not None and os.path.abspath(pz) == os.path.abspath(lf):
        print("WARNING: --pz and --lf point at the same file; this compares a binary "
              "with itself and can only ever pass", file=sys.stderr)

    print("corpus  : %s" % ", ".join(roots))
    print("pz      : %s" % (pz or "-"))
    print("lf      : %s" % (lf or "-"))
    print("programs: %d\n" % len(progs), flush=True)

    counts = {"OK": 0, "FAIL": 0, "SKIP": 0}
    failures = []
    t0 = time.time()
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as ex:
        futs = {ex.submit(check, p, pz, lf, workdir, args.timeout,
                          args.update_expected): p for p in progs}
        for fut in concurrent.futures.as_completed(futs):
            p = futs[fut]
            status, detail, el = fut.result()
            counts[status] += 1
            if status == "FAIL":
                failures.append((p.name, detail))
                print("FAIL  %-42s %s" % (p.name, detail), flush=True)
            elif status == "SKIP":
                if args.verbose:
                    print("SKIP  %-42s %s" % (p.name, detail), flush=True)
            elif args.verbose:
                print("ok    %-42s %5.2fs" % (p.name, el), flush=True)

    print("\n%d ok, %d failed, %d skipped in %.1fs"
          % (counts["OK"], counts["FAIL"], counts["SKIP"], time.time() - t0))
    if failures:
        print("\nfailed:")
        for name, detail in sorted(failures):
            print("  %-42s %s" % (name, detail))
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
