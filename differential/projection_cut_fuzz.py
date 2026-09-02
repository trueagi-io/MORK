#!/usr/bin/env python3
"""Random-query validator for the projection cut.

Generates random conjunctive bodies, works out INDEPENDENTLY -- from the rule as stated, over the
generated syntax tree, never from the engine's mask -- which variables the cut may answer with a
single witness, predicts how much enumeration that removes, then runs the query on a stock build
and on a `projection_cut` build and checks three things:

  * the two builds agree on the answer space byte for byte,
  * the answers equal a join computed here in Python, from the generated facts, and
  * where a speed-up was predicted, a speed-up actually happened.

The rule, restated so this file is a second opinion rather than an echo: a body variable may be
answered with one witness iff (a) the body mentions it exactly once, (b) no template reads it, and
(c) everything after it inside its own conjunct also satisfies (a) and (b) -- it lies in the
conjunct's trailing run. Anything earlier in a conjunct decides which subtrie the later columns
are drawn from, so pinning it would drop answers rather than duplicates.

Three families:

  direct     relations of ground tuples, including the named shape
             `(, (R $x $_1 $y $_2 $_3) (Q $x $y))` -- `$_2 $_3` are cuttable, `$_1` is not,
             because `$y` follows it.
  schematic  the same shapes, but every don't-care value is a fuzzed QUERY EXPRESSION carrying
             variables of its own, so the cut binds schematic terms rather than symbols.
  meta       the space holds fuzzed queries as data -- `(f (R $x $_1 $y $_2 $_3))`,
             `(g (Q $x $y))`, `(data ...)` -- and the body queries over them in the
             `(, (f $f ...) (g $g ...) (data $f) (data $g))` shape.

Usage:  projection_cut_fuzz.py --base BIN --cut BIN [--cases N] [--seed S]
"""

import argparse, itertools, os, random, re, subprocess, sys, tempfile

TOOK = re.compile(r"took (\d+) ms")


# ---------------------------------------------------------------------------- queries

class Factor:
    def __init__(self, rel, cols):
        self.rel, self.cols = rel, cols

    def text(self):
        return "(%s %s)" % (self.rel, " ".join("$" + c for c in self.cols))


class Query:
    def __init__(self, factors, reads, family):
        self.factors, self.reads, self.family = factors, reads, family

    def body(self):
        return "(, %s)" % " ".join(f.text() for f in self.factors)

    def exec_atom(self):
        return "(exec 0 %s (, (out %s)))" % (self.body(), " ".join("$" + v for v in self.reads))

    def occurrences(self):
        occ = {}
        for f in self.factors:
            for c in f.cols:
                occ[c] = occ.get(c, 0) + 1
        return occ

    def cuttable(self):
        """The rule applied to the syntax tree -- independent of the engine's byte-level mask."""
        occ = self.occurrences()
        solo = lambda v: occ[v] == 1 and v not in self.reads
        cut = set()
        for f in self.factors:
            for c in reversed(f.cols):      # the conjunct's trailing run, and no further
                if not solo(c):
                    break
                cut.add(c)
        return cut


def named_shape():
    """The shape called out by name: jump the last two columns of R, but never `$_1`."""
    return Query([Factor("R", ["x0", "d0", "x1", "d1", "d2"]), Factor("Q", ["x0", "x1"])],
                 ["x0", "x1"], "direct")


def gen_query(rng, family):
    if family == "meta":
        # `(, (f $f ...) (g $g ...) (data $f) (data $g))` -- the join variables bind whole
        # query expressions; the don't-care tails are what the cut may answer.
        fac = [Factor("f", ["f"] + ["d%d" % i for i in range(rng.choice([1, 1, 2]))])]
        nd = len(fac[0].cols) - 1
        fac.append(Factor("g", ["g"] + ["d%d" % (nd + i) for i in range(rng.choice([0, 1, 2]))]))
        fac.append(Factor("data", ["f"]))
        fac.append(Factor("data", ["g"]))
        return Query(fac, ["f", "g"], "meta")

    nkeys = rng.choice([1, 1, 2])
    keys = ["x%d" % i for i in range(nkeys)]
    factors, dc = [], 0
    for fi in range(rng.choice([1, 2, 2, 3])):
        cols = list(keys) if fi == 0 else [rng.choice(keys)]
        if rng.random() < 0.4 and nkeys > 1:        # a don't-care BEFORE a key: never cuttable
            cols = [cols[0], "d%d" % dc] + cols[1:]
            dc += 1
        for _ in range(rng.choice([1, 1, 2, 2, 3])):
            cols.append("d%d" % dc)
            dc += 1
        factors.append(Factor("R%d" % fi, cols))
    return Query(factors, keys, family)


# ---------------------------------------------------------------------------- data

def query_expr(j):
    """A fuzzed query expression, used as a stored VALUE. Carries its own variables.

    Every index yields a DISTINCT expression -- the shape rotates but the relation names carry
    `j`. Duplicates would silently collapse in the trie, making the relation smaller than the
    generator believes and the predicted ratio a fiction.
    """
    shapes = [
        "(, (R%d $x $a $y $b $c) (Q%d $x $y))" % (j, j),
        "(, (f%d $p) (g%d $q) (data $p) (data $q))" % (j, j),
        "(P%d (= $l $r) $t%d)" % (j, j),
        "(, (S%d $u $v) (T%d $v $w $z))" % (j, j),
    ]
    return shapes[j % len(shapes)]


def gen_data(rng, q, nkey, fan):
    """Facts for every factor. Returns (facts, per-relation sizes, per-variable domains)."""
    keyvals = ["k%d" % i for i in range(nkey)]
    if q.family == "meta":
        keyvals = [query_expr(i) for i in range(nkey)]
    dcvals = [("w%d" % j) if q.family == "direct" else query_expr(j) for j in range(fan)]

    assert len(set(keyvals)) == len(keyvals), "key values must be distinct"
    assert len(set(dcvals)) == len(dcvals), "don't-care values must be distinct"
    facts, sizes, domains = [], {}, {}
    for f in q.factors:
        rows = []
        doms = [keyvals if not c.startswith("d") else dcvals for c in f.cols]
        # A full cross product would make a don't-care that PRECEDES a key independent of that
        # key: pinning it would still leave every suffix value reachable, so an engine that
        # wrongly cut a non-trailing variable would produce the right answers anyway and the
        # fuzzer would never notice. Correlate them instead -- each value of a leading
        # don't-care admits only a SLICE of the keys that follow it, so pinning it drops
        # answers and the check fails.
        lead_dc = [k for k, c in enumerate(f.cols)
                   if c.startswith("d") and any(not c2.startswith("d") for c2 in f.cols[k + 1:])]
        for combo in itertools.product(*doms):
            if lead_dc:
                drop = False
                for k in lead_dc:
                    slot = dcvals.index(combo[k])
                    for k2 in range(k + 1, len(f.cols)):
                        if not f.cols[k2].startswith("d"):
                            # keep only the keys congruent to this don't-care's slot
                            if keyvals.index(combo[k2]) % len(dcvals) != slot % len(dcvals):
                                drop = True
                if drop:
                    continue
            rows.append("(%s %s)" % (f.rel, " ".join(combo)))
        facts.extend(rows)
        key = f.rel + "/" + str(len(f.cols))
        sizes[key] = (sizes.get(key, (0, 0, 0))[0] + len(rows),
                      sum(1 for c in f.cols if not c.startswith("d")),
                      sum(1 for c in f.cols if c.startswith("d")))
        for c in f.cols:
            domains[c] = keyvals if not c.startswith("d") else dcvals
    return facts, sizes, domains, keyvals, dcvals


def predicted_ratio(q, fan):
    """Enumerated tuples over cut tuples: every don't-care contributes its fan-out unless cut."""
    cut = q.cuttable()
    base = after = 1
    for f in q.factors:
        for c in f.cols:
            if c.startswith("d"):
                base *= fan
                after *= 1 if c in cut else fan
    return base, after


def python_join(q, domains):
    """The answer set, computed here: project each factor onto the variables that outlive it
    (read, or shared with another factor), dedup, then join. Sound because every projected-away
    variable is a singleton, hence purely existential."""
    occ = q.occurrences()
    keep = lambda v: v in q.reads or occ[v] > 1
    rel = None
    for f in q.factors:
        cols = [c for c in f.cols if keep(c)]
        doms = [domains[c] for c in cols]
        tuples = {tuple(t) for t in itertools.product(*doms)} if cols else {()}
        if rel is None:
            rel, relcols = tuples, cols
            continue
        shared = [c for c in cols if c in relcols]
        li = [relcols.index(c) for c in shared]
        ri = [cols.index(c) for c in shared]
        newcols = relcols + [c for c in cols if c not in relcols]
        add = [cols.index(c) for c in cols if c not in relcols]
        out = set()
        for a in rel:
            for b in tuples:
                if all(a[x] == b[y] for x, y in zip(li, ri)):
                    out.add(a + tuple(b[i] for i in add))
        rel, relcols = out, newcols
    idx = [relcols.index(v) for v in q.reads]
    return {tuple(t[i] for i in idx) for t in rel}


# ---------------------------------------------------------------------------- running

def run(binary, prog, out, reps, timeout):
    """Best-of-`reps` query time and the resulting space, or (None, None) if it does not finish.

    A timeout is data, not an error: the two engines differ by orders of magnitude on some of
    these shapes, so the sizing ladder needs to be told when it has gone too far rather than
    having the run die.
    """
    best, dump = None, None
    for _ in range(reps):
        # Clear the target first and insist the process succeeded: otherwise a crashed or
        # timed-out run leaves the PREVIOUS run's space behind and the comparison silently
        # passes on stale output.
        if os.path.exists(out):
            os.remove(out)
        try:
            r = subprocess.run([binary, "run", prog, "--steps", "2", out],
                               capture_output=True, timeout=timeout)
        except subprocess.TimeoutExpired:
            return None, None
        if r.returncode != 0 or not os.path.exists(out):
            return None, None
        m = TOOK.search(r.stdout.decode("utf-8", "replace"))
        ms = int(m.group(1)) if m else -1
        best = ms if best is None else min(best, ms)
        with open(out, "rb") as fh:
            dump = fh.read()
    return best, dump


def parse_answers(dump):
    out = set()
    for line in dump.decode("utf-8", "replace").split("\n"):
        if line.startswith("(out "):
            out.add(line[5:-1].strip())
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--base", required=True)
    ap.add_argument("--cut", required=True)
    ap.add_argument("--cases", type=int, default=26)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--reps", type=int, default=2)
    ap.add_argument("--min-base-ms", type=int, default=20)
    ap.add_argument("--max-facts", type=int, default=250000)
    ap.add_argument("--keep", default=None)
    ap.add_argument("--family", default=None, help="force one family")
    ap.add_argument("--base-timeout", type=int, default=300, help="seconds before a size is too big")
    ap.add_argument("--label", default="", help="engine label for the report header")
    args = ap.parse_args()

    rng = random.Random(args.seed)
    tmp = args.keep or tempfile.mkdtemp(prefix="pcfuzz-")
    os.makedirs(tmp, exist_ok=True)
    families = ["direct", "schematic", "meta"]
    accepted, attempts = [], 0

    while len(accepted) < args.cases and attempts < args.cases * 60:
        attempts += 1
        if args.family:
            q = gen_query(rng, args.family)
        else:
            q = named_shape() if not accepted else gen_query(rng, families[attempts % 3])
        cut = q.cuttable()
        if not cut:
            continue                                   # report only where a jump is predicted

        # Grow the data until the ENUMERATION is long enough to time honestly, measuring it at
        # each step rather than predicting its cost: the two engines differ by orders of
        # magnitude on the schematic and meta shapes, so a tuple-count model that sizes the
        # leapfrog join sensibly can hand the ProductZipper a query it will not finish.
        prog = os.path.join(tmp, "case%02d.mm2" % len(accepted))
        chosen = None
        for nkey, fan in [(4, 6), (6, 8), (8, 10), (10, 12), (12, 14), (14, 16), (16, 20), (20, 24)]:
            facts, sizes, domains, keyvals, dcvals = gen_data(rng, q, nkey, fan)
            if len(facts) > args.max_facts:
                break
            base_t, after_t = predicted_ratio(q, fan)
            if base_t <= after_t:
                break
            with open(prog, "w") as fh:
                fh.write("\n".join(facts) + "\n" + q.exec_atom() + "\n")
            b_ms, b_dump = run(args.base, prog, prog + ".base.space", 1, args.base_timeout)
            if b_ms is None:
                break                                  # too big for this engine: keep the last
            chosen = (facts, sizes, domains, nkey, fan, base_t, after_t, b_ms, b_dump)
            if b_ms >= args.min_base_ms:
                break
        if chosen is None:
            continue
        facts, sizes, domains, nkey, fan, base_t, after_t, b_ms, b_dump = chosen
        if b_ms < args.min_base_ms:
            continue                                   # too fast to attribute a ratio to
        # rewrite the chosen size, since the ladder may have moved past it
        with open(prog, "w") as fh:
            fh.write("\n".join(facts) + "\n" + q.exec_atom() + "\n")
        if b_ms < 2000:
            b_ms, b_dump = run(args.base, prog, prog + ".base.space", args.reps, args.base_timeout)
        c_ms, c_dump = run(args.cut, prog, prog + ".cut.space", args.reps, args.base_timeout)
        if c_ms is None:
            print("  case %d: the cut build did not finish or exited nonzero" % len(accepted))
            c_ms, c_dump = args.base_timeout * 1000, None

        identical = (c_dump is not None and b_dump == c_dump)
        # The independent join models an EQUALITY join, which is what the engine performs only
        # when the joined values are ground. In the meta family the read variables bind whole
        # query expressions, so the engine joins them by UNIFICATION and renames their variables
        # on output; modelling that here would mean reimplementing the unifier. Those cases are
        # held to stock-vs-cut byte-identity instead -- the stock engine IS the reference -- plus
        # a non-empty answer space, so a silently empty result cannot pass.
        modelled = any(not v.startswith("(") for v in [domains[r][0] for r in q.reads])
        if modelled:
            want = {" ".join(t) for t in python_join(q, domains)}
            answers_ok = (parse_answers(b_dump) == want and parse_answers(c_dump) == want)
            nans = len(want)
        else:
            nans = len(parse_answers(b_dump))
            answers_ok = nans > 0
        speedup = b_ms / max(c_ms, 0.5)
        accepted.append(dict(q=q, sizes=sizes, nkey=nkey, fan=fan, facts=len(facts),
                             pred=base_t / after_t, b_ms=b_ms, c_ms=c_ms, speedup=speedup,
                             identical=identical, answers_ok=answers_ok, modelled=modelled,
                             cut=sorted(cut), nans=nans))

    ok = lambda c: c["identical"] and c["answers_ok"] and c["speedup"] >= 1.5
    print("%sseed=%d  cases=%d  attempts=%d  programs in %s\n" % (("engine=%s  " % args.label) if args.label else "", args.seed, len(accepted), attempts, tmp))
    hdr = "%-3s %-9s %-44s %8s %10s %8s %7s %9s %s" % (
        "#", "family", "body", "facts", "predicted", "base ms", "cut ms", "speedup", "ok")
    print(hdr); print("-" * len(hdr))
    for i, c in enumerate(accepted):
        b = c["q"].body()
        b = b if len(b) <= 44 else b[:41] + "..."
        print("%-3d %-9s %-44s %8d %9.0fx %8d %7d %8.1fx %s" %
              (i, c["q"].family, b, c["facts"], c["pred"], c["b_ms"], c["c_ms"], c["speedup"],
               "yes" if ok(c) else "NO"))
    print("\nrelation sizes and the variables the cut answered with one witness:")
    for i, c in enumerate(accepted):
        rels = ", ".join("%s:%d facts(%d key,%d dc)" % (r.split("/")[0], v[0], v[1], v[2])
                         for r, v in sorted(c["sizes"].items()))
        print("  %-3d keyvals=%-3d fanout=%-3d answers=%-5d cut=%-16s %s" %
              (i, c["nkey"], c["fan"], c["nans"], ",".join("$" + v for v in c["cut"]), rels))
    short = len(accepted) < args.cases
    if short:
        print("\nSHORT RUN: asked for %d cases, accepted %d. A run that cannot build its cases "
              "proves nothing, so this is a failure, not a pass." % (args.cases, len(accepted)))
    bad = [c for c in accepted if not ok(c)]
    print("\n%d/%d met the prediction | byte-identical: %d/%d | answer set correct: %d/%d" %
          (len(accepted) - len(bad), len(accepted),
           sum(1 for c in accepted if c["identical"]), len(accepted),
           sum(1 for c in accepted if c["answers_ok"]), len(accepted)))
    nm = [c for c in accepted if not c["modelled"]]
    if nm:
        print("(%d meta cases are checked by stock-vs-cut byte-identity and a non-empty answer "
              "space, not by the equality-join model -- see the note in the source)" % len(nm))
    if accepted:
        sp = sorted(c["speedup"] for c in accepted)
        print("speed-up: min %.1fx  median %.1fx  max %.1fx" % (sp[0], sp[len(sp) // 2], sp[-1]))
    if bad:
        print("\nFAILED:")
        for c in bad:
            print("  %s\n    identical=%s answers_ok=%s speedup=%.2fx predicted=%.0fx" %
                  (c["q"].body(), c["identical"], c["answers_ok"], c["speedup"], c["pred"]))
    return 1 if (bad or short) else 0


if __name__ == "__main__":
    sys.exit(main())
