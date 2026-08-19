#!/usr/bin/env python3
"""Benchmark paired MM2 programs: for each X, run X_naive.mm2 against X_<variant>.mm2 on both
engines, check the answer spaces agree, and report the ratio. Query-only time, best of 3."""
import glob, os, re, subprocess, sys
TOOK = re.compile(r"took (\d+) ms")
def run(binary, prog, out, steps, reps=3):
    """Best-of-`reps` query time and the resulting space, or (None, None) if the run failed.

    The target is cleared before every attempt and the exit status is checked: without both, a
    crashed or timed-out run leaves the PREVIOUS run's space in place and the caller compares
    stale output, which reads as agreement.
    """
    best = None
    for _ in range(reps):
        if os.path.exists(out):
            os.remove(out)
        try:
            r = subprocess.run([binary, "run", prog, "--steps", str(steps), out],
                               capture_output=True, timeout=600)
        except subprocess.TimeoutExpired:
            return None, None
        if r.returncode != 0 or not os.path.exists(out):
            return None, None
        m = TOOK.search(r.stdout.decode("utf-8", "replace"))
        ms = int(m.group(1)) if m else -1
        best = ms if best is None else min(best, ms)
    return best, open(out, "rb").read()
def key_lines(dump, prefixes):
    return sorted(l for l in dump.decode("utf-8", "replace").split("\n")
                  if any(l.startswith("(" + p) for p in prefixes))
def main(d, steps, prefixes):
    names = sorted({os.path.basename(f).rsplit("_", 1)[0] for f in glob.glob(d + "/*_naive.mm2")})
    print("%-22s %-10s %9s %9s %8s   %9s %9s %8s  %s" %
          ("example", "variant", "lf naive", "lf opt", "x", "pz naive", "pz opt", "x", "agree"))
    for n in names:
        base = f"{d}/{n}_naive.mm2"
        for v in sorted(glob.glob(f"{d}/{n}_*.mm2")):
            tag = os.path.basename(v)[len(n) + 1:-4]
            if tag == "naive":
                continue
            row, agree = [], []
            for e in ["lf", "pz"]:
                bn, bd = run(f"/tmp/paj-v4-{e}", base, f"/tmp/bp_{n}_{e}_n.space", steps)
                on, od = run(f"/tmp/paj-v4-{e}", v, f"/tmp/bp_{n}_{e}_o.space", steps)
                if bn is None or on is None:
                    row += ["t/o", "t/o", 0.0]; agree.append("?"); continue
                row += [bn, on, bn / max(on, 0.5)]
                agree.append("y" if key_lines(bd, prefixes) == key_lines(od, prefixes) else "N")
            print("%-22s %-10s %9s %9s %7.1fx   %9s %9s %7.1fx  %s" %
                  (n, tag, row[0], row[1], row[2], row[3], row[4], row[5], "".join(agree)))
if __name__ == "__main__":
    main(sys.argv[1], int(sys.argv[2]), sys.argv[3].split(","))
