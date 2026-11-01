#!/usr/bin/env python3
"""H-20260920-02. Frozen local exhaustion and p13/14 all-mass holdout.

Standalone implementation. Cycles chronological, windows newest first.
Only short supply (lags <=11) is used, including nonpositive-mass cycles.
"""
import argparse
import hashlib
import itertools
import json
import subprocess


def p2(w):
    signs = [1 if b == "A" else -1 for b in w]
    return sum(signs) == 1 and sum(k * b for k, b in enumerate(signs, 1)) == 0


def minimal(w):
    return not any(p2(w[:d]) for d in range(1, len(w)))


def ss(w):
    return sum(x == y == "S" for x, y in zip(w, w[1:]))


def past(cycle, u, d):
    return "".join(cycle[(u - k) % len(cycle)] for k in range(1, d + 1))


def bits(w, t, member=True):
    return {**({t: "A"} if member else {}),
            **{t - k: b for k, b in enumerate(w, 1)}}


def compatible(a, b):
    return all(a[x] == b[x] for x in a.keys() & b.keys())


def emit(record):
    print(json.dumps(record, sort_keys=True), flush=True)


def local():
    donors = ["".join(w) for w in itertools.product("AS", repeat=11)
              if p2(w) and ss(w) == 2]
    assert len(donors) == 12 and sum(minimal(w) for w in donors) == 7
    rows = []
    for w in donors:
        off = max(k for k, b in enumerate(w, 1) if b == "S")
        donor = bits(w, 0, False)  # No donor-current-A hypothesis.
        covers = []
        for v in ("AAS", "SAAAASS", "ASAASAS"):
            for k, b in enumerate(v, 1):
                if b != "S":
                    continue
                t = k - off
                if not compatible(donor, bits(v, t)):
                    continue
                covers.append([v, t, k])
                assert v != "AAS", (w, v, t, k)
                if v == "SAAAASS":
                    assert not compatible(donor, bits("AAS", t + 2)), (w, t)
                for shift in (-101, -1, 0, 1, 101):
                    translated = bits(w, shift, False)
                    assert compatible(translated, bits(v, shift + t))
                    if v == "SAAAASS":
                        assert not compatible(translated, bits("AAS", shift + t + 2))
        rows.append(dict(window=w, minimal=minimal(w), oldest=off, raw_covers=covers))
    emit(dict(kind="local_donor_table", words=rows, translations=5))
    root = bits("SAAAASS", 0)
    possible = []
    for v in ("AAS", "SAAAASS", "ASAASAS"):
        for k, b in enumerate(v, 1):
            if b == "S" and compatible(root, bits(v, k - 1)):
                possible.append([v, k - 1, k])
    assert possible == [["AAS", 2, 3], ["SAAAASS", 0, 1], ["ASAASAS", 6, 7]]
    # Exclude w2 by E-357, exclude same w1 by own(0)=-7 and function-ness.
    assert [x for x in possible if x[0] != "ASAASAS" and x[1] != 0] == [["AAS", 2, 3]]
    members = {-3: "AAS", 0: "SAAAASS", 2: "AAS"}
    own = {-3: -6, 0: -7, 2: -1}
    stream = {}
    subtractions = set()
    for t, w in members.items():
        assert compatible(stream, bits(w, t))
        stream.update(bits(w, t))
        local_s = {t - k for k, b in enumerate(w, 1) if b == "S"}
        assert own[t] in local_s
        subtractions |= local_s
    assert subtractions == set(own.values())
    assert stream[1] == stream[2] == "A"
    # Weaken onto or function-ness: mem={0}, next two signs S are consistent.
    weak_stream = {**root, 1: "S", 2: "S"}
    assert compatible(root, weak_stream)
    emit(dict(kind="future_member_models", raw_newest_owners=possible,
              members=members, own=own, without_onto_members=[0],
              without_function_relation={0: [-7, -6, -1]}, weakened_future="SS"))
    emit(dict(status="PASS", scope="local"))


def holdout():
    for p in (13, 14):
        counters = dict(cycles=0, donors=0, nonminimal_donors=0, tight_nonempty=0,
                        checks=0, nonminimal_checks=0, nonpositive_checks=0,
                        future_member_checks=0, violations=0)
        digest = hashlib.sha256()
        examples = {}
        for mask in range(1 << p):
            cycle = "".join("A" if mask & (1 << u) else "S" for u in range(p))
            digest.update((cycle + "\n").encode())
            counters["cycles"] += 1
            data = {}
            for u, b in enumerate(cycle):
                if b != "A":
                    continue
                for d in range(1, 12):
                    w = past(cycle, u, d)
                    if p2(w):
                        data[u] = (d, w, frozenset((u-k) % p for k, c in enumerate(w, 1) if c == "S"))
                        break
            donors = []
            for u in range(p):  # Donor current sign deliberately unrestricted.
                w = past(cycle, u, 11)
                if p2(w) and ss(w) == 2:
                    is_min = minimal(w)
                    sstar = (u - max(k for k, c in enumerate(w, 1) if c == "S")) % p
                    donors.append((u, w, is_min, sstar))
                    counters["donors"] += 1
                    counters["nonminimal_donors"] += not is_min
            us = tuple(data)
            for size in range(1, len(us) + 1):
                for B in itertools.combinations(us, size):
                    N = frozenset().union(*(data[u][2] for u in B))
                    assert len(B) <= len(N), (cycle, B, N, "short Hall")
                    if len(B) != len(N):
                        continue
                    counters["tight_nonempty"] += 1
                    for u in B:
                        if data[u][1] == "SAAAASS":
                            counters["future_member_checks"] += 1
                            v = (u + 2) % p
                            assert v in B and data[v][0] == 3 and data[v][1] == "AAS", (cycle, B, u)
                    for u, w, is_min, sstar in donors:
                        counters["checks"] += 1
                        counters["nonminimal_checks"] += not is_min
                        nonpositive = cycle.count("A") * 2 <= p
                        counters["nonpositive_checks"] += nonpositive
                        assert sstar not in N, (cycle, u, w, B, sorted(N))
                        if not is_min and "nonminimal" not in examples:
                            examples["nonminimal"] = dict(cycle=cycle, donor=u, window=w, B=B, N=sorted(N))
                        if nonpositive and "nonpositive" not in examples:
                            examples["nonpositive"] = dict(cycle=cycle, donor=u, window=w, B=B, N=sorted(N))
        assert counters["nonminimal_checks"] > 0 and counters["nonpositive_checks"] > 0
        assert counters["future_member_checks"] > 0
        emit(dict(kind="holdout", period=p, sample_sha256=digest.hexdigest(),
                  counters=counters, examples=examples))
    emit(dict(status="PASS", scope="holdout_p13_p14_all_mass"))


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--mode", choices=("local", "holdout"), required=True)
    args = ap.parse_args()
    emit(dict(kind="provenance", revision=subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip(), mode=args.mode))
    local() if args.mode == "local" else holdout()
