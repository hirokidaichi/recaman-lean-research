#!/usr/bin/env python3
"""Frozen finite falsifier for H-20261011-03; no orbit assumptions."""
import argparse
import hashlib
import itertools
import json
from pathlib import Path


def scan(lo, hi):
    totals = dict(period_words=0, windows=0, eligible_pairs=0,
                  wrapping_pairs=0, nonpositive_mass_pairs=0, violations=0)
    first = None
    for p in range(lo, hi + 1):
        for bits in itertools.product("AS", repeat=p):
            totals["period_words"] += 1
            for u in range(p):
                for d in range(3 * p + 4):
                    totals["windows"] += 1
                    start = u - d
                    w = [bits[x % p] for x in range(start, u)]
                    if sum(a == b == "S" for a, b in zip(w, w[1:])) > 2:
                        continue
                    for i in range(d - 2):
                        if w[i:i + 3] != ["S"] * 3:
                            continue
                        q = start + i
                        for j in range(i):
                            if w[j] != "S":
                                continue
                            s = start + j
                            totals["eligible_pairs"] += 1
                            totals["wrapping_pairs"] += d > p
                            totals["nonpositive_mass_pairs"] += bits.count("A") <= bits.count("S")
                            if s % p == q % p:
                                totals["violations"] += 1
                                first = first or dict(word="".join(bits), u=u, d=d, s=s, q=q)
    return dict(period_min=lo, period_max=hi, max_lag="3*p+3", **totals,
                first_counterexample=first)


def control(word, u, d, s, q, dropped):
    e = lambda x: word[x % len(word)]
    count = sum(e(x) == e(x + 1) == "S" for x in range(u - d, u - 1))
    premises = dict(budget=count <= 2, earlier=u-d <= s < q,
                    containment=q + 2 < u, signs=all(e(x) == "S" for x in [s, q, q+1, q+2]))
    assert all(v for k, v in premises.items() if k != dropped)
    assert not premises[dropped] and s % len(word) == q % len(word)
    return dict(dropped=dropped, word=word, u=u, d=d, s=s, q=q,
                ss_count=count, premises=premises, phase_collision=True)


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("mode", choices=["discovery", "holdout", "controls"])
    mode = ap.parse_args().mode
    print(json.dumps(dict(mode=mode, source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()), sort_keys=True))
    if mode == "controls":
        for args in [("S", 4, 4, 0, 1, "budget"),
                     ("S", 3, 3, 0, 0, "earlier"),
                     ("S", 3, 3, 0, 1, "containment")]:
            print(json.dumps(control(*args), sort_keys=True))
    else:
        result = scan(1, 5) if mode == "discovery" else scan(6, 9)
        print(json.dumps(result, sort_keys=True))
        if result["violations"]:
            raise SystemExit(1)
