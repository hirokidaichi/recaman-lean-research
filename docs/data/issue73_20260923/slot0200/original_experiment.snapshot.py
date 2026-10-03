#!/usr/bin/env python3
"""H-20260920-03: exhaust every short-window assignment, not only minimal ones."""
import argparse
import hashlib
import itertools
import json
import subprocess


def is_p2(w):
    a = [1 if c == "A" else -1 for c in w]
    return sum(a) == 1 and sum((k+1)*s for k, s in enumerate(a)) == 0


def pairs(w):
    return sum(w[k:k+2] == "SS" for k in range(len(w)-1))


P2_WORDS = {d: {"".join(w) for w in itertools.product("AS", repeat=d) if is_p2(w)}
            for d in (3, 7, 11)}


def window(c, u, d):
    return "".join(c[(u-k) % len(c)] for k in range(1, d+1))


def examine(p):
    count = dict(cycles=0, assignments=0, nonminimal_assignments=0,
                 tight=0, tight_nonminimal=0, donor_checks=0, deleted_checks=0,
                 changed_nontight=0, violations=0)
    digest = hashlib.sha256()
    examples = {}
    for mask in range(1 << p):
        c = "".join("A" if mask >> u & 1 else "S" for u in range(p))
        digest.update((c+"\n").encode())
        count["cycles"] += 1
        options = []
        for u, b in enumerate(c):
            if b != "A":
                continue
            supplies = []
            for d in (3, 7, 11):
                w = window(c, u, d)
                if w in P2_WORDS[d]:
                    N = frozenset((u-k) % p for k, bit in enumerate(w, 1) if bit == "S")
                    supplies.append((u, d, N))
            if supplies:
                options.append([None] + [(u, d, N, supplies[0][1], supplies[0][2])
                                         for u, d, N in supplies])
        donors = []
        for u in range(p):
            w = window(c, u, 11)
            if w in P2_WORDS[11] and pairs(w) == 2:
                donors.append((u, (u-max(k for k, b in enumerate(w, 1) if b == "S")) % p))
        for assignment in itertools.product(*options):
            B = [rec for rec in assignment if rec is not None]
            if not B:
                continue
            count["assignments"] += 1
            nonminimal = any(d != m for u, d, N, m, M in B)
            count["nonminimal_assignments"] += nonminimal
            N = frozenset().union(*(rec[2] for rec in B))
            M = frozenset().union(*(rec[4] for rec in B))
            assert M <= N and len(B) <= len(M), (c, B, N, M)
            if len(B) == len(N):
                count["tight"] += 1
                count["tight_nonminimal"] += nonminimal
                assert M == N, (c, B, N, M)
                if nonminimal and "tight_nonminimal" not in examples:
                    examples["tight_nonminimal"] = dict(cycle=c, assignments=[[r[0], r[1], r[3]] for r in B], N=sorted(N))
                for u, s in donors:
                    count["donor_checks"] += 1
                    assert s not in N, (c, B, u, s)
            elif M != N:
                count["changed_nontight"] += 1
                if "changed_nontight" not in examples:
                    examples["changed_nontight"] = dict(cycle=c, assignments=[[r[0], r[1], r[3]] for r in B], N=sorted(N), M=sorted(M))
            for u, s in donors:
                count["deleted_checks"] += 1
                assert len(B) <= len(N - {s}), (c, B, u, s)
    return dict(kind="period", period=p, counts=count, examples=examples, sample_sha256=digest.hexdigest())


def control():
    # Dropping SS=2 remains false even though the chosen B window is minimal.
    c = "AAAASAAASSSS"
    w = window(c, 3, 11)
    assert is_p2(w) and pairs(w) == 3 and window(c, 7, 3) == "AAS"
    assert (3 - max(k for k, b in enumerate(w, 1) if b == "S")) % 12 == 4
    print(json.dumps(dict(kind="SS3_counterexample", cycle=c, donor=3, donor_window=w, B=[7], N=[4])), flush=True)


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--mode", choices=["discovery", "holdout"], required=True)
    args = ap.parse_args()
    print(json.dumps(dict(kind="provenance", mode=args.mode,
                         revision=subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip())), flush=True)
    control()
    totals = dict(nonminimal_assignments=0, changed_nontight=0, donor_checks=0)
    for p in (range(1, 13) if args.mode == "discovery" else (15,)):
        result = examine(p)
        for k in totals:
            totals[k] += result["counts"][k]
        print(json.dumps(result, sort_keys=True), flush=True)
    assert all(v > 0 for v in totals.values()), totals
    print(json.dumps(dict(status="PASS", scope=args.mode, totals=totals)), flush=True)
