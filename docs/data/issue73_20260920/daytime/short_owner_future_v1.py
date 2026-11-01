#!/usr/bin/env python3
"""H-20260920-01: exact local falsification and periodic regression.

No import from the overnight probes. A/S strings are chronological for cycles
and newest-first for windows. The local list is exhaustive, not sampled.
"""
import argparse
import itertools
import json

WORDS = ("AAS", "SAAAASS", "ASAASAS")
DONORS = ("AAASSSASASA", "ASAAASSSASA", "ASASAAASSSA", "ASSAAAASSAS",
          "ASSAAASAASS", "SAAASAASSSA", "SAAASSAAASS")


def placed(word, clock):
    return {clock: "A", **{clock - k: bit for k, bit in enumerate(word, 1)}}


def compatible(a, b):
    return all(a[x] == b[x] for x in a.keys() & b.keys())


def covers(root, subtraction):
    return [(w, subtraction + k, k) for w in WORDS
            for k, c in enumerate(w, 1) if c == "S"
            and compatible(root, placed(w, subtraction + k))]


def supply(cycle):
    p = len(cycle)
    result = {}
    for u, c in enumerate(cycle):
        if c != "A":
            continue
        mass = moment = 0
        cover = set()
        window = []
        for d in range(1, p * (p + 1) + 1):
            b = cycle[(u - d) % p]
            window.append(b)
            sign = 1 if b == "A" else -1
            mass += sign
            moment += d * sign
            if b == "S":
                cover.add((u - d) % p)
            if mass == 1 and moment == 0:
                result[u] = (d, "".join(window), frozenset(cover))
                break
    return result


def subsets(items):
    items = tuple(items)
    for n in range(len(items) + 1):
        yield from itertools.combinations(items, n)


def neighbors(data, B):
    return frozenset().union(*(data[u][2] for u in B))


def hall(data):
    return all(len(B) <= len(neighbors(data, B)) for B in subsets(data))


def local():
    root = placed(WORDS[1], 0)
    old = covers(root, -7)
    new = covers(root, -1)
    assert old == [("SAAAASS", 0, 7)], old
    assert new == [("AAS", 2, 3), ("SAAAASS", 0, 1)], new
    # After own(0)=-7, single-valued ownership removes the second new candidate.
    assert [x for x in new if x[1] != 0] == [("AAS", 2, 3)]
    for t in (-101, -11, -1, 0, 1, 7, 101):
        assert covers(placed(WORDS[1], t), t - 7) == [("SAAAASS", t, 7)]
        assert covers(placed(WORDS[1], t), t - 1) == [
            ("AAS", t + 2, 3), ("SAAAASS", t, 1)]
    print(json.dumps({"kind": "local_exhaustive", "older_S_owners": old,
                      "newest_S_owners": new, "translation_checks": 7}))
    # Actual finite owner family: three members, onto and single-valued own.
    members = {-3: "AAS", 0: WORDS[1], 2: "AAS"}
    own = {-3: -6, 0: -7, 2: -1}
    bits = {}
    all_s = set()
    for t, w in members.items():
        assert compatible(bits, placed(w, t))
        bits.update(placed(w, t))
        ws = {t - k for k, b in enumerate(w, 1) if b == "S"}
        assert own[t] in ws
        all_s |= ws
    assert all_s == set(own.values()) and bits[1] == "A"
    # Dropping onto: one member, own(0)=-7, next symbol S is consistent.
    weakened = {**root, 1: "S"}
    assert weakened[1] == "S" and -7 in {x for x, b in weakened.items() if b == "S"}
    assert {-1, -6, -7} != {-7}
    print(json.dumps({"kind": "models", "nonempty_members": sorted(members),
                      "own": own, "next": bits[1],
                      "without_onto": {"members": [0], "own": {0: -7}, "next": "S"},
                      "without_function": {"members": [0], "owns": [-7, -6, -1], "next": "S"}}))
    # Independently exhaust donor/root overlapping placements, including donor A.
    placements = []
    for w in DONORS:
        off = max(k for k, c in enumerate(w, 1) if c == "S")
        dr = placed(w, 0)
        for v, t, k in covers(dr, -off):
            assert v == WORDS[1] and k == 1
            assert dr[t + 1] == "S"
            placements.append((w, off, v, t, k, dr[t + 1]))
    assert len(placements) == 3
    print(json.dumps({"kind": "donor_cover", "placements": placements}))


def regression():
    controls = [("w_positive", "SSAAAASAAA"),
                ("q_nonempty", "SSAASAAA"),
                ("E240", "AAAASSAAAASAAASASS"),
                ("offset11_is_A", "AAAASAAASASASSS"),
                ("proper_U_candidate", "SSAAAASAAAAAAAAASAAA")]
    for label, cycle in controls:
        data = supply(cycle)
        assert hall(data)
        tight = [B for B in subsets(data) if B and len(B) == len(neighbors(data, B))
                 and all(data[u][0] in (3, 7, 11) for u in B)]
        ws = [(B, u) for B in tight for u in B if data[u][1] == WORDS[1]]
        assert all(cycle[(u + 1) % len(cycle)] == "A" for B, u in ws)
        donors = [u for u, (d, w, _) in data.items() if d == 11 and w in DONORS]
        qs = 0
        for u in donors:
            off = max(k for k, c in enumerate(data[u][1], 1) if c == "S")
            for B in tight:
                if u not in B:
                    qs += 1
                    assert (u - off) % len(cycle) not in neighbors(data, B)
        if label == "w_positive":
            assert ws
        if label == "q_nonempty":
            assert qs
        if label == "E240":
            B = (2, 8, 11, 13)
            assert B in tight and any(data[u][0] == 7 for u in B)
        if label == "offset11_is_A":
            assert data[3][1] in DONORS and cycle[(3 - 11) % len(cycle)] == "A"
        print(json.dumps({"kind": "periodic_regression", "label": label,
                          "word": cycle, "U": {u: [d, w, sorted(c)] for u, (d, w, c) in data.items()},
                          "Q_nonempty": qs, "W_cases": ws,
                          "proper_W": [(B, u) for B, u in ws if len(B) < len(data)]}))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--mode", choices=["local", "regression", "all"], default="all")
    args = parser.parse_args()
    if args.mode in ("local", "all"):
        local()
    if args.mode in ("regression", "all"):
        regression()
    print(json.dumps({"status": "PASS", "scope": args.mode}))
