#!/usr/bin/env python3
"""All-period wrap check for the frozen U7-avoiding assignment SOLUTION0.

For p>=22 the two length-11 windows at distance |cB-cA|<=10 cannot wrap, so
Z-glue-freeness implies no collision. For 1<=p<=21, place every ordered pair
of types at the unique residues that would identify the charged S, propagate
forced signs around the cycle, and test whether both min-lag-11 types survive.
Independent P2 sums. Also re-verify the naive-gap2 p=14 collision word.
"""
from __future__ import annotations

import hashlib
import itertools
import json
import subprocess
from pathlib import Path

SOLUTION0 = {
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


def force_window(cons, t, offs, p):
    """Force the length-11 window and t=A. False on contradiction."""
    r0 = t % p
    if r0 in cons and cons[r0] != 1:
        return False
    cons[r0] = 1
    for i in range(1, 12):
        r = (t - i) % p
        val = -1 if i in offs else 1
        if r in cons and cons[r] != val:
            return False
        cons[r] = val
    return True


def min_p2_word(word, t):
    p = len(word)
    s = m = 0
    for i in range(1, 12):
        x = word[(t - i) % p]
        s += x
        m += i * x
        if i in (3, 7, 11) and s == 1 and m == 0:
            offs = tuple(j for j in range(1, i + 1) if word[(t - j) % p] < 0)
            return i, offs
    return None, ()


def realize(p, t_a, off_a, t_b, off_b):
    cons = {}
    if not force_window(cons, t_a, off_a, p):
        return "sign_conflict", None
    if not force_window(cons, t_b, off_b, p):
        return "sign_conflict", None
    free = [i for i in range(p) if i not in cons]
    if len(free) > 10:
        return "too_free", len(free)
    for bits in itertools.product((-1, 1), repeat=len(free)):
        word = [0] * p
        for r, v in cons.items():
            word[r] = v
        for r, v in zip(free, bits):
            word[r] = v
        word = tuple(word)
        da, oa = min_p2_word(word, t_a)
        db, ob = min_p2_word(word, t_b)
        if da == 11 and oa == off_a and db == 11 and ob == off_b:
            return "witness", "".join("A" if x > 0 else "S" for x in word)
    return "killed_by_minlag_or_search", None


def verify_p14_naive_collision():
    """Independent P2 recomputation of the failed gap2 assignment collision."""
    w = "ASSSASSAAAASSA"
    word = tuple(1 if c == "A" else -1 for c in w)
    t_a, t_b = 0, 10
    da, oa = min_p2_word(word, t_a)
    db, ob = min_p2_word(word, t_b)
    s_a = (t_a - 11) % 14
    s_b = (t_b - 7) % 14
    # also recompute moments from scratch
    def sums(t, d):
        s = m = 0
        offs = []
        for i in range(1, d + 1):
            x = word[(t - i) % 14]
            s += x
            m += i * x
            if x < 0:
                offs.append(i)
        return s, m, tuple(offs)

    return {
        "word": w,
        "tA": t_a,
        "tB": t_b,
        "minA": [da, list(oa)],
        "minB": [db, list(ob)],
        "chargedA_offset11_phase": s_a,
        "chargedB_offset7_phase": s_b,
        "same_image": s_a == s_b,
        "d11A_sum_moment_offs": list(sums(t_a, 11)),
        "d11B_sum_moment_offs": list(sums(t_b, 11)),
        "d3A": list(sums(t_a, 3)),
        "d7A": list(sums(t_a, 7)),
        "d3B": list(sums(t_b, 3)),
        "d7B": list(sums(t_b, 7)),
    }


def main():
    print("protocol=H-20260908-01 SOLUTION0 wrap-around all-period check", flush=True)
    print(
        "source_revision="
        + subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip(),
        flush=True,
    )
    print(
        "script_sha256="
        + hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        flush=True,
    )
    print("NAIVE_GAP2_P14_COLLISION=" + json.dumps(verify_p14_naive_collision()), flush=True)

    types = list(SOLUTION0)
    witnesses = []
    too_free = []
    n_conflict = 0
    n_killed = 0
    n_same_c = 0
    n_checked = 0
    for p in range(1, 22):
        for a, b in itertools.product(types, repeat=2):
            ca, cb = SOLUTION0[a], SOLUTION0[b]
            if ca == cb:
                n_same_c += 1
                continue
            # unique relative placement identifying charged S: tB - tA ≡ cb-ca
            t_a = 0
            t_b = (cb - ca) % p
            if t_a == t_b:
                # same phase cannot be two types
                n_conflict += 1
                continue
            n_checked += 1
            status, w = realize(p, t_a, a, t_b, b)
            if status == "sign_conflict":
                n_conflict += 1
            elif status == "killed_by_minlag_or_search":
                n_killed += 1
            elif status == "too_free":
                too_free.append({"p": p, "A": a, "B": b, "tB": t_b, "free": w})
            else:
                witnesses.append(
                    {
                        "p": p,
                        "A": a,
                        "B": b,
                        "cA": ca,
                        "cB": cb,
                        "tB": t_b,
                        "word": w,
                    }
                )
    print(
        "WRAP_STATS "
        + json.dumps(
            {
                "n_same_c_skipped": n_same_c,
                "n_checked": n_checked,
                "n_sign_conflict": n_conflict,
                "n_killed": n_killed,
                "n_too_free": len(too_free),
                "n_witness": len(witnesses),
            }
        ),
        flush=True,
    )
    print("TOO_FREE=" + json.dumps(too_free[:20]), flush=True)
    print("WITNESSES=" + json.dumps(witnesses), flush=True)

    # HARD local occupation table, wrap-aware for p=1..21: can phi7 hit offsets 4,7,10,11?
    HARD = (1, 4, 7, 10, 11)
    hard_hits = []
    for p in range(1, 22):
        t = 0
        cons = {}
        if not force_window(cons, t, HARD, p):
            continue
        domain = {(t - i) % p for i in HARD}
        # try each U7 kind on each domain phase
        for i in HARD:
            s = (t - i) % p
            for kind, pattern, win in (
                ("lag3", (3,), 3),
                ("lag7h1", (1, 6, 7), 7),
                ("lag7h2", (2, 5, 7), 7),
            ):
                tp = (s + { "lag3": 3, "lag7h1": 7, "lag7h2": 5 }[kind]) % p
                need = {tp: 1}
                for off in range(1, win + 1):
                    need[(tp - off) % p] = -1 if off in pattern else 1
                ok = all(r not in cons or cons[r] == val for r, val in need.items())
                if ok and not (i == 1 and kind == "lag3"):
                    hard_hits.append({"p": p, "offset": i, "kind": kind, "tp": tp})
    print("HARD_INTERNAL_U7_WRAP=" + json.dumps(hard_hits), flush=True)

    if witnesses:
        print("CONCLUSION=SOLUTION0 has a cyclic wrap collision; repair fails", flush=True)
    elif too_free:
        print(
            "CONCLUSION=some wrap placements left >10 free bits; not fully decided",
            flush=True,
        )
    elif hard_hits:
        print(
            "CONCLUSION=HARD internal S can be a U7 image after wrap; residual charge unsafe",
            flush=True,
        )
    else:
        print(
            "CONCLUSION=SOLUTION0 has no cyclic pair-witness for p=1..21 and no "
            "HARD-internal U7 wrap occupation; with Z-glue-freeness this is the "
            "all-period injection for the frozen type-to-offset rule",
            flush=True,
        )


if __name__ == "__main__":
    main()
