#!/usr/bin/env python3
"""Independent recomputation of a lag-15 type-to-offset assignment.

Does not import lag15_csp.py. Rebuilds the 155 types, U7/φ11 blocks, and
pairwise Z-clashes from the P2 identities and the frozen φ11 table.
"""
from __future__ import annotations

import hashlib
import itertools
import json
import subprocess
import sys

CHOSEN11 = {
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


def sign_at(tau, rel, width=15):
    if rel == 0:
        return 1
    i = -rel
    if 1 <= i <= width:
        return -1 if i in tau else 1
    return None


def u7_conflict(tau, i, kind, width=15):
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
        have = sign_at(tau, rel, width)
        if have is not None and have != val:
            hits.append((rel, have, val))
    return hits


def phi11_conflict(tau15, i, tau11, i11):
    s = -i
    tp = s + i11
    hits = []
    have = sign_at(tau15, tp)
    if have is not None and have != 1:
        hits.append((tp, have, 1))
    for k in range(1, 12):
        have = sign_at(tau15, tp - k)
        need = -1 if k in tau11 else 1
        if have is not None and have != need:
            hits.append((tp - k, have, need))
    return hits


def load_assignment(path):
    chosen = None
    with open(path) as f:
        for line in f:
            if line.startswith("ASSIGNMENT="):
                chosen = json.loads(line.split("=", 1)[1])
    if chosen is None:
        raise SystemExit("no ASSIGNMENT in " + path)
    return {tuple(row["type"]): row["offset"] for row in chosen}


def main():
    print("protocol=H-20260908-04 independent verification of lag-15 injection", flush=True)
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
    src = sys.argv[1] if len(sys.argv) > 1 else None
    if src is None:
        print("usage: lag15_verify.py ASSIGNMENT_LOG", flush=True)
        return 2
    chosen = load_assignment(src)
    raw = [s for s in itertools.combinations(range(1, 16), 7) if sum(s) == 60]
    types = []
    for s in raw:
        def pref(p, s=s):
            inside = [x for x in s if x <= p]
            return len(inside) == (p - 1) // 2 and sum(inside) == p * (p + 1) // 4

        if not pref(3) and not pref(7) and not pref(11):
            types.append(tuple(s))
    print("raw_lag15=" + str(len(raw)), flush=True)
    print("min_lag15=" + str(len(types)), flush=True)
    if set(types) != set(chosen):
        print("FAIL: assignment type set != min-lag-15 types", flush=True)
        print("MISSING=" + json.dumps([list(t) for t in sorted(set(types) - set(chosen))]), flush=True)
        print("EXTRA=" + json.dumps([list(t) for t in sorted(set(chosen) - set(types))]), flush=True)
        return 1
    bad_block = []
    for tau, i in chosen.items():
        if i not in tau:
            bad_block.append(("not_S", tau, i))
            continue
        u7 = {k: u7_conflict(tau, i, k) for k in ("lag3", "lag7h1", "lag7h2")}
        if any(not hits for hits in u7.values()):
            bad_block.append(("u7", list(tau), i, {k: len(v) for k, v in u7.items()}))
        u11 = []
        for tau11, i11 in CHOSEN11.items():
            if not phi11_conflict(tau, i, tau11, i11):
                u11.append((tau11, i11))
        if u11:
            bad_block.append(("phi11", list(tau), i, u11[:3]))
    print("N_UNBLOCKED=" + str(len(bad_block)), flush=True)
    if bad_block[:5]:
        print("UNBLOCKED=" + json.dumps(bad_block[:5], default=str), flush=True)
    collisions = 0
    for tau, i in chosen.items():
        for sig, j in chosen.items():
            if (tau, i) == (sig, j):
                continue
            delta = j - i
            conflict = False
            for rel in range(-15, 1):
                a = sign_at(tau, rel)
                b = sign_at(sig, rel - delta)
                if a is not None and b is not None and a != b:
                    conflict = True
                    break
            if sign_at(tau, delta) == -1 or sign_at(sig, -delta) == -1:
                conflict = True
            if not conflict:
                collisions += 1
                if collisions <= 5:
                    print(
                        "OPEN_PAIR="
                        + json.dumps(
                            {"tau": tau, "i": i, "sig": sig, "j": j, "delta": delta}
                        ),
                        flush=True,
                    )
    print("OPEN_COLLISION_PAIRS=" + str(collisions), flush=True)
    if bad_block or collisions:
        print("FAIL: assignment is not a proved injection", flush=True)
        return 1
    print(
        "PASS: every chosen S is U7- and φ11-incompatible and every distinct "
        "type pair conflicts at collision distance",
        flush=True,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
