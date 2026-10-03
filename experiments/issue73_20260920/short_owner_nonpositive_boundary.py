#!/usr/bin/env python3
"""Explicit zero/negative-mass examples for the no-positive-drift theorem.

Only short windows are enumerated; the positive-period all-lag scan bound is
not used or claimed to be valid for these cycles.
"""
import json
from short_owner_negative_controls import p2, word_at
from short_owner_future import subsets

for cycle in ["ASASASSSAAAASS", "ASASASSSAAAASSS", "ASASASSSAAAASSSS"]:
    p = len(cycle)
    data = {}
    for u, c in enumerate(cycle):
        if c != "A":
            continue
        for d in range(1, 12):
            w = word_at(cycle, u, d)
            if p2(w):
                data[u] = (d, w, {(u - k) % p for k, b in enumerate(w, 1) if b == "S"})
                break
    donors = [u for u, (d, w, _) in data.items() if d == 11
              and sum(w[i:i + 2] == "SS" for i in range(10)) == 2]
    tight = []
    for B in subsets(data):
        N = set().union(*(data[b][2] for b in B)) if B else set()
        assert len(B) <= len(N)
        if B and len(B) == len(N):
            for u in donors:
                off = max(k for k, b in enumerate(data[u][1], 1) if b == "S")
                assert (u - off) % p not in N
            tight.append({"B": B, "N": sorted(N)})
    assert donors and tight and 2 * cycle.count("A") - p <= 0
    print(json.dumps(dict(cycle=cycle, p=p, mass=2 * cycle.count("A") - p,
                          short_windows={u: [d, w, sorted(N)] for u, (d, w, N) in data.items()},
                          donors=donors, nonempty_tight=tight,
                          scope="short windows d<=11 only; no claim of complete all-lag supply at nonpositive mass")))
