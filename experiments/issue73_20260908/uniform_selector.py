#!/usr/bin/env python3
"""Falsify a d-independent selector on min-lag P2 windows.

H-20260908-06: is there a closed-form F(S-set) or F(blocked-set) that
reproduces φ7 and is a blocked pairwise-injective charge on the 17 lag-11
types and the 155 lag-15 types?

This is not a period census and not a lag-19 table. A surviving F would be
a candidate all-lag rule. Failure of the declared family is a stop of
lag-by-lag, not a refutation of E-070.
"""
from __future__ import annotations

import hashlib
import itertools
import json
import subprocess

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

PHI7 = {
    (3,): 3,
    (1, 6, 7): 7,
    (2, 5, 7): 5,
}


def sign_at(tau, rel, width):
    if rel == 0:
        return 1
    i = -rel
    if 1 <= i <= width:
        return -1 if i in tau else 1
    return None


def u7_conflict(tau, i, kind, width):
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


def phi11_conflict(tau15, i, tau11, i11, width=15):
    s = -i
    tp = s + i11
    hits = []
    have = sign_at(tau15, tp, width)
    if have is not None and have != 1:
        hits.append((tp, have, 1))
    for k in range(1, 12):
        have = sign_at(tau15, tp - k, width)
        need = -1 if k in tau11 else 1
        if have is not None and have != need:
            hits.append((tp - k, have, need))
    return hits


def min_types(d):
    k = (d - 1) // 2
    target = d * (d + 1) // 4
    raw = [s for s in itertools.combinations(range(1, d + 1), k) if sum(s) == target]
    prev = [p for p in (3, 7, 11, 15) if p < d]
    out = []
    for s in raw:
        def pref(p, s=s):
            inside = [x for x in s if x <= p]
            return len(inside) == (p - 1) // 2 and sum(inside) == p * (p + 1) // 4

        if not any(pref(p) for p in prev):
            out.append(tuple(s))
    return out


def blocked11(tau):
    safe = []
    for i in tau:
        if all(u7_conflict(tau, i, k, 11) for k in ("lag3", "lag7h1", "lag7h2")):
            safe.append(i)
    return safe


def blocked15(tau):
    safe = []
    for i in tau:
        if not all(u7_conflict(tau, i, k, 15) for k in ("lag3", "lag7h1", "lag7h2")):
            continue
        if any(not phi11_conflict(tau, i, t11, i11) for t11, i11 in CHOSEN11.items()):
            continue
        safe.append(i)
    return safe


def open_pairs(chosen, width):
    n = 0
    sample = []
    items = list(chosen.items())
    for tau, i in items:
        for sig, j in items:
            if (tau, i) == (sig, j):
                continue
            delta = j - i
            conflict = False
            for rel in range(-width, 1):
                a = sign_at(tau, rel, width)
                b = sign_at(sig, rel - delta, width)
                if a is not None and b is not None and a != b:
                    conflict = True
                    break
            if sign_at(tau, delta, width) == -1 or sign_at(sig, -delta, width) == -1:
                conflict = True
            if not conflict:
                n += 1
                if len(sample) < 3:
                    sample.append({"tau": tau, "i": i, "sig": sig, "j": j, "delta": delta})
    return n, sample


def median(xs):
    xs = sorted(xs)
    return xs[len(xs) // 2]


def closest(xs, target):
    return min(xs, key=lambda x: (abs(x - target), x))


def main():
    print("protocol=H-20260908-06 uniform selector on min-lag windows", flush=True)
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

    print("PHI7_VS_RAW_S", flush=True)
    for tau, ch in PHI7.items():
        s = list(tau)
        preds = {
            "min": min(s),
            "max": max(s),
            "median": median(s),
            "min_ge3": min(x for x in s if x >= 3),
            "closest_d2": closest(s, 7 / 2 if len(s) > 1 else 3),
        }
        print(json.dumps({"type": tau, "phi7": ch, "preds": preds, "match": [k for k, v in preds.items() if v == ch]}), flush=True)

    types11 = min_types(11)
    types15 = min_types(15)
    print("N11=" + str(len(types11)), flush=True)
    print("N15=" + str(len(types15)), flush=True)
    assert len(types11) == 17
    assert len(types15) == 155

    safe11 = {t: blocked11(t) for t in types11}
    safe15 = {t: blocked15(t) for t in types15}
    empty11 = [t for t, s in safe11.items() if not s]
    empty15 = [t for t, s in safe15.items() if not s]
    print("UNCOVERED11=" + str(len(empty11)), flush=True)
    print("UNCOVERED15=" + str(len(empty15)), flush=True)
    uniq11 = sum(1 for s in safe11.values() if len(s) == 1)
    uniq15 = sum(1 for s in safe15.values() if len(s) == 1)
    print("UNIQUE_BLOCKED11=" + str(uniq11), flush=True)
    print("UNIQUE_BLOCKED15=" + str(uniq15), flush=True)

    selectors = [
        ("min_blocked", lambda s: min(s)),
        ("max_blocked", lambda s: max(s)),
        ("median_blocked", median),
        ("closest_halfwidth", None),  # filled per width
    ]

    def run_family(name, types, safe, width, half):
        print("FAMILY=" + name, flush=True)
        for sel_name, fn in [
            ("min_blocked", lambda s: min(s)),
            ("max_blocked", lambda s: max(s)),
            ("median_blocked", median),
            ("closest_d2", lambda s, h=half: closest(s, h)),
        ]:
            chosen = {t: fn(safe[t]) for t in types}
            nopen, sample = open_pairs(chosen, width)
            disagree_csp = None
            if width == 11:
                disagree_csp = sum(1 for t in types if chosen[t] != CHOSEN11[t])
            rec = {
                "selector": sel_name,
                "width": width,
                "open_pairs": nopen,
                "disagree_csp11": disagree_csp,
                "sample": sample,
            }
            print("RESULT=" + json.dumps(rec, default=list), flush=True)

    run_family("lag11", types11, safe11, 11, 11 / 2)
    run_family("lag15", types15, safe15, 15, 15 / 2)

    # Does any selector equal φ7 on the three U7 windows using the raw S-set?
    print("CONCLUSION_PHI7=no raw-S selector among {min,max,median,min_ge3} fits all three U7 types", flush=True)


if __name__ == "__main__":
    raise SystemExit(main())
