#!/usr/bin/env python3
"""Frozen p=32,33 holdout for H-20260917-01 Q and H-20260920-01 W.

Seed 2026091801. One Random instance, p=32 then p=33. getrandbits(p),
bit u is A iff integer bit u is 1. Reject nonpositive mass and exact duplicate
bit words within the period; rotations are distinct. Accept exactly 2000 per p.
Every addition scans all d=1..p(p+1) until its first P2. Hall uses ALL supply
phases. Every subset of the short supply phases is tested for tightness.
The minimum 20 donor-bearing Hall words per p is an acceptance requirement.
No failures, empty targets, timeout or underfilled sample can return PASS.
"""
import argparse
import hashlib
import json
import random
import time

from short_owner_future import DONORS, WORDS, hall, regression, supply


def matching_hall(data):
    matches = {}

    def augment(u, used):
        for s in sorted(data[u][2]):
            if s in used:
                continue
            used.add(s)
            if s not in matches or augment(matches[s], used):
                matches[s] = u
                return True
        return False

    return all(augment(u, set()) for u in sorted(data))


def matching_regression():
    # Exhaust every positive word at p <= 10 (all rotations retained).
    counts = []
    for p in range(1, 11):
        n = 0
        for bits in range(1 << p):
            if 2 * bits.bit_count() <= p:
                continue
            cycle = "".join("A" if bits >> u & 1 else "S" for u in range(p))
            data = supply(cycle)
            assert matching_hall(data) == hall(data), (p, cycle)
            n += 1
        counts.append([p, n])
    print(json.dumps({"kind": "matching_regression", "period_counts": counts}), flush=True)


def run(seconds):
    started = time.monotonic()
    rng = random.Random(2026091801)
    for p in (32, 33):
        seen = set()
        digest = hashlib.sha256()
        counts = dict(period=p, accepted=0, draws=0, hall_words=0, donor_words=0,
                      donors=0, tight_short_subsets=0, Q_cases=0, Q_nonempty=0,
                      W_cases=0, Q_violations=0, W_violations=0, max_full_U=0)
        while len(seen) < 2000:
            if time.monotonic() - started > seconds:
                print(json.dumps({"status": "INCOMPLETE_TIMEOUT", "counts": counts}), flush=True)
                raise SystemExit(2)
            bits = rng.getrandbits(p)
            counts["draws"] += 1
            if 2 * bits.bit_count() <= p or bits in seen:
                continue
            seen.add(bits)
            cycle = "".join("A" if bits >> u & 1 else "S" for u in range(p))
            digest.update((cycle + "\n").encode("ascii"))
            counts["accepted"] += 1
            data = supply(cycle)
            counts["max_full_U"] = max(counts["max_full_U"], len(data))
            if not matching_hall(data):
                print(json.dumps({"status": "HALL_COUNTEREXAMPLE", "word": cycle}), flush=True)
                raise SystemExit(1)
            counts["hall_words"] += 1
            donor_list = []
            for u, (d, w, _) in data.items():
                if d == 11 and w in DONORS:
                    off = max(k for k, b in enumerate(w, 1) if b == "S")
                    donor_list.append((u, 1 << ((u - off) % p)))
            counts["donor_words"] += bool(donor_list)
            counts["donors"] += len(donor_list)
            short = [u for u in data if data[u][0] in (3, 7, 11)]
            cov = [sum(1 << s for s in data[u][2]) for u in short]
            neighborhoods = [0] * (1 << len(short))
            for mask in range(1 << len(short)):
                if mask:
                    low = mask & -mask
                    i = low.bit_length() - 1
                    neighborhoods[mask] = neighborhoods[mask ^ low] | cov[i]
                if neighborhoods[mask].bit_count() != mask.bit_count():
                    continue
                counts["tight_short_subsets"] += 1
                B = [u for i, u in enumerate(short) if mask >> i & 1]
                for u, sbit in donor_list:
                    if u in B:
                        continue
                    counts["Q_cases"] += 1
                    counts["Q_nonempty"] += bool(B)
                    if neighborhoods[mask] & sbit:
                        counts["Q_violations"] += 1
                        print(json.dumps({"status": "Q_COUNTEREXAMPLE", "word": cycle,
                                          "B": B, "donor": u}), flush=True)
                        raise SystemExit(1)
                for u in B:
                    if data[u][1] == WORDS[1]:
                        counts["W_cases"] += 1
                        if cycle[(u + 1) % p] != "A":
                            counts["W_violations"] += 1
                            print(json.dumps({"status": "W_COUNTEREXAMPLE", "word": cycle,
                                              "B": B, "member": u}), flush=True)
                            raise SystemExit(1)
            if counts["accepted"] % 500 == 0:
                print(json.dumps({"kind": "progress", **counts}), flush=True)
        counts["sample_sha256"] = digest.hexdigest()
        print(json.dumps({"kind": "period_complete", **counts}), flush=True)
        if counts["donor_words"] < 20 or counts["W_cases"] == 0 or counts["Q_nonempty"] == 0:
            print(json.dumps({"status": "INSUFFICIENT_TARGETS", "period": p}), flush=True)
            raise SystemExit(2)
    print(json.dumps({"status": "PASS", "elapsed_seconds": time.monotonic() - started}), flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--mode", choices=("regression", "holdout"), required=True)
    parser.add_argument("--seconds", type=int, default=1800)
    args = parser.parse_args()
    if args.mode == "regression":
        regression()
        matching_regression()
    else:
        run(args.seconds)
