#!/usr/bin/env python3
"""Exact checks on the arc_trace_probe traces of one run directory.

Usage: verify.py RUNDIR [OTHER_RUNDIR]
1. For every traced late landing that ends a comb run (next step types start
   with A,A): the record at +3 is an addition whose blocked candidate equals
   a(c-1) (the value the orbit left when it landed the comb's last value).
2. Post-landing structure per deep arc: maximal alternating S/A segments
   (ping-pong levels) from the landing to the wrap, with the k range of each.
3. If OTHER_RUNDIR is given: the arcs_all tables agree on the common arcs.
"""
import collections
import os
import sys


def read_trace_map(path):
    recs = {}
    order = []
    with open(path) as f:
        for line in f:
            if line.startswith("#") or line.startswith("..."):
                continue
            t = line.split()
            c = int(t[0])
            recs[c] = dict(clock=c, a=int(t[1]), h=int(t[2]), k=int(t[3]),
                           r=int(t[4]), step=t[5], cand=t[6], state=t[7],
                           cls=t[8])
            order.append(c)
    return recs, order


def read_lates(path):
    out = []
    with open(path) as f:
        for line in f:
            if line.startswith("#"):
                continue
            t = line.split()
            d = dict(clock=int(t[0]), value=int(t[1]))
            for kv in t[2:]:
                if "=" in kv:
                    k, v = kv.split("=", 1)
                    d[k] = v
            types = "".join(x.split(":")[1] for x in d["next8"].split(",") if ":" in x)
            d["types"] = types
            out.append(d)
    return out


def read_arcs(path):
    rows = []
    with open(path) as f:
        for line in f:
            if line.startswith("#") or not line.strip():
                continue
            rows.append(line.split())
    return rows


def segments(steps_ks):
    """Maximal alternating S/A stretches; returns [(start_offset, length, kmin, kmax)]."""
    segs = []
    start = 0
    for i in range(1, len(steps_ks) + 1):
        if i == len(steps_ks) or steps_ks[i][0] == steps_ks[i - 1][0]:
            ks = [k for _, k in steps_ks[start:i]]
            segs.append((start, i - start, min(ks), max(ks)))
            start = i
    return segs


def main():
    rundir = sys.argv[1]
    arcs = read_arcs(os.path.join(rundir, "arcs_all.txt"))
    deep = [r for r in arcs if r[18] == "DEEP"]
    print("check 1: blocked comb => +3 is an addition with candidate == a(c-1)")
    total_comb_ends = 0
    ok = 0
    bad = []
    unverifiable = 0
    for r in deep:
        idx = int(r[4])
        recs, order = read_trace_map(os.path.join(rundir, "trace_%d.txt" % idx))
        lates = read_lates(os.path.join(rundir, "lates_%d.txt" % idx))
        for d in lates:
            if not d["types"].startswith("AA"):
                continue
            total_comb_ends += 1
            c = d["clock"]
            if c - 1 not in recs or c + 3 not in recs:
                unverifiable += 1
                continue
            r3 = recs[c + 3]
            if r3["step"] == "A" and r3["state"] == "blocked" and int(r3["cand"]) == recs[c - 1]["a"]:
                ok += 1
            else:
                bad.append((idx, c, r3))
    print("  comb ends (late landing followed by A,A): %d; verified: %d; violations: %d; not in kept trace: %d"
          % (total_comb_ends, ok, len(bad), unverifiable))
    for b in bad[:10]:
        print("  violation:", b)
    print()

    print("check 2: post-landing ping-pong levels per deep arc")
    for r in deep:
        idx, value, end = int(r[4]), int(r[5]), int(r[2])
        recs, order = read_trace_map(os.path.join(rundir, "trace_%d.txt" % idx))
        post = [(recs[c]["step"], recs[c]["k"]) for c in order if c > idx]
        if len(post) != end - idx:
            print("  arc landing %d=%d: post-landing records kept %d of %d (trace truncated)" % (idx, value, len(post), end - idx))
        segs = segments(post)
        khist = collections.Counter(k for _, k in post)
        first_k1 = next((c for c in order if c > idx and recs[c]["k"] == 1), None)
        first_k2 = next((c for c in order if c > idx and recs[c]["k"] <= 2), None)
        subs_after = sum(1 for s, _ in post if s == "S")
        print("  arc landing %d=%d: %d steps to the wrap; k histogram %s; subtractions after landing %d; first k<=2 at %s; first k=1 at %s"
              % (idx, value, len(post), dict(sorted(khist.items())), subs_after,
                 "+%d" % (first_k2 - idx) if first_k2 else "never",
                 "+%d" % (first_k1 - idx) if first_k1 else "never"))
        desc = []
        for (s, n, kmin, kmax) in segs:
            desc.append("+%d:%d steps k%s" % (s + 1, n, ("=%d" % kmin) if kmin == kmax else "=%d/%d" % (kmin, kmax)))
        if len(desc) > 24:
            print("    segments (%d): %s ... %s" % (len(desc), "; ".join(desc[:12]), "; ".join(desc[-12:])))
        else:
            print("    segments (%d): %s" % (len(desc), "; ".join(desc)))
        # the two-addition and two-subtraction transitions
        aa = sum(1 for i in range(1, len(post)) if post[i][0] == "A" and post[i - 1][0] == "A")
        ss = sum(1 for i in range(1, len(post)) if post[i][0] == "S" and post[i - 1][0] == "S")
        print("    consecutive AA: %d, consecutive SS: %d" % (aa, ss))
    print()

    if len(sys.argv) >= 3:
        other = read_arcs(os.path.join(sys.argv[2], "arcs_all.txt"))
        n = min(len(arcs), len(other))
        same = all(arcs[i] == other[i] for i in range(n))
        print("check 3: arcs_all agreement on the first %d arcs of %s and %s: %s" % (n, rundir, sys.argv[2], "IDENTICAL" if same else "DIFFERENT"))
        if not same:
            for i in range(n):
                if arcs[i] != other[i]:
                    print("  first difference at arc", i + 1, arcs[i], other[i])
                    break


if __name__ == "__main__":
    main()
