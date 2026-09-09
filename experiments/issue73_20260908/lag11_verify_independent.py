#!/usr/bin/env python3
"""Independent recomputation of H_inject11 assignment, U7-disjointness, pairwise injectivity.

Does not import lag11_safe_charge.py. Rebuilds types, chosen offsets, and both
obstructions from the P2 identities alone.
"""
from __future__ import annotations

import hashlib
import itertools
import json
import subprocess

# CSP assignment: U7-safe offsets with no Z-window pair at δ=j-i.
# Wrap-around injectivity is a separate cyclic regression.
CHOSEN = {
    (1, 2, 9, 10, 11): 10,
    (1, 3, 8, 10, 11): 3,
    (1, 4, 7, 10, 11): 4,
    (1, 4, 8, 9, 11): 4,
    (1, 5, 6, 10, 11): 6,
    (1, 5, 7, 9, 11): 7,
    (1, 5, 8, 9, 10): 8,
    (2, 3, 7, 10, 11): 10,
    (2, 3, 8, 9, 11): 9,
    (2, 4, 6, 10, 11): 4,
    (2, 4, 7, 9, 11): 4,
    (2, 4, 8, 9, 10): 4,
    (2, 5, 6, 9, 11): 6,
    (2, 6, 7, 8, 10): 7,
    (4, 5, 6, 7, 11): 6,
    (4, 5, 6, 8, 10): 6,
    (4, 5, 7, 8, 9): 7,
}


def sign_at(tau, rel):
    """ε(t+rel) for a min-lag-11 A at t of type tau. rel in [-11,0] is forced."""
    if rel == 0:
        return 1
    i = -rel
    if 1 <= i <= 11:
        return -1 if i in tau else 1
    return None


def u7_conflict(tau, i, kind):
    s = -i
    if kind == "lag3":
        tp = s + 3
        need = {tp: 1, tp - 1: 1, tp - 2: 1, tp - 3: -1}
    elif kind == "lag7h1":
        tp = s + 7
        need = {tp: 1, **{tp - o: (-1 if o in (1, 6, 7) else 1) for o in range(1, 8)}}
    else:
        tp = s + 5
        need = {tp: 1, **{tp - o: (-1 if o in (2, 5, 7) else 1) for o in range(1, 8)}}
    hits = []
    for rel, val in need.items():
        have = sign_at(tau, rel)
        if have is not None and have != val:
            hits.append((rel, have, val))
    return hits


def main():
    print("protocol=H-20260908-01 independent verification of lag-11 injection", flush=True)
    print(
        "source_revision="
        + subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip(),
        flush=True,
    )
    print(
        "script_sha256="
        + hashlib.sha256(__import__("pathlib").Path(__file__).read_bytes()).hexdigest(),
        flush=True,
    )
    # rebuild 17 types
    raw = [
        s
        for s in itertools.combinations(range(1, 12), 5)
        if sum(s) == 33
    ]
    types = []
    for s in raw:
        def pref(p, s=s):
            inside = [x for x in s if x <= p]
            return len(inside) == (p - 1) // 2 and sum(inside) == p * (p + 1) // 4

        if not pref(3) and not pref(7):
            types.append(tuple(s))
    assert set(types) == set(CHOSEN)
    assert len(types) == 17

    bad_u7 = []
    for tau, i in CHOSEN.items():
        assert i in tau
        for kind in ("lag3", "lag7h1", "lag7h2"):
            hits = u7_conflict(tau, i, kind)
            if not hits:
                bad_u7.append((tau, i, kind))
    print("U7_UNCONFLICTED=" + json.dumps(bad_u7), flush=True)

    collisions = 0
    for tau, i in CHOSEN.items():
        for sig, j in CHOSEN.items():
            if (tau, i) == (sig, j):
                continue
            delta = j - i
            conflict = False
            for rel in range(-11, 1):
                a = sign_at(tau, rel)
                b = sign_at(sig, rel - delta)
                if a is not None and b is not None and a != b:
                    conflict = True
                    break
            # also forced A at both t and t+delta
            if sign_at(tau, delta) == -1 or sign_at(sig, -delta) == -1:
                conflict = True
            if not conflict:
                collisions += 1
                print("OPEN_PAIR=" + json.dumps({"tau": tau, "i": i, "sig": sig, "j": j, "delta": delta}), flush=True)
    print("OPEN_COLLISION_PAIRS=" + str(collisions), flush=True)
    if bad_u7 or collisions:
        print("FAIL: assignment is not a proved injection", flush=True)
    else:
        print("PASS: every chosen S is U7-incompatible and every distinct type pair conflicts at collision distance", flush=True)


if __name__ == "__main__":
    main()
