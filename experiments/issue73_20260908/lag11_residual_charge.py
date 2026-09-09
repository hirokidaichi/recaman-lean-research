#!/usr/bin/env python3
"""One permitted repair: type-indexed residual charge, injectivity on Z and cycles.

Gap-2 S is never a U7 image (following-gap partition). Gap2-less types charge a
window-forced U7-incompatible S. Pairwise glue of two 11-windows at the unique
offset that would identify the charged S. Independent P2 sums.
"""
from __future__ import annotations

import hashlib
import itertools
import json
import subprocess
from pathlib import Path

LAG3 = (3,)
LAG7H1 = (1, 6, 7)
LAG7H2 = (2, 5, 7)

# Frozen assignment: exact internal gap-2 if any (smallest such offset),
# else the smallest U7-incompatible internal offset from the local table.
CHARGE = {
    (1, 2, 9, 10, 11): 10,  # gap2-less, safe gap=1
    (1, 3, 8, 10, 11): 3,  # gap2
    (1, 4, 7, 10, 11): 4,  # HARD, safe gap=3
    (1, 4, 8, 9, 11): 11,  # gap2
    (1, 5, 6, 10, 11): 6,  # gap2-less, safe gap=1
    (1, 5, 7, 9, 11): 7,  # gap2
    (1, 5, 8, 9, 10): 8,  # gap2-less, safe gap=3
    (2, 3, 7, 10, 11): 10,  # gap2-less, safe gap=3
    (2, 3, 8, 9, 11): 11,  # gap2
    (2, 4, 6, 10, 11): 4,  # gap2
    (2, 4, 7, 9, 11): 4,  # gap2
    (2, 4, 8, 9, 10): 4,  # gap2
    (2, 5, 6, 9, 11): 11,  # gap2
    (2, 6, 7, 8, 10): 10,  # gap2
    (4, 5, 6, 7, 11): 6,  # gap2-less, safe gap=1
    (4, 5, 6, 8, 10): 8,  # gap2
    (4, 5, 7, 8, 9): 7,  # gap2
}


def p2_offsets(d):
    k = (d - 1) // 2
    target = d * (d + 1) // 4
    return [s for s in itertools.combinations(range(1, d + 1), k) if sum(s) == target]


def is_minimal(s):
    def pref(p):
        inside = tuple(x for x in s if x <= p)
        kk = (p - 1) // 2
        return len(inside) == kk and sum(inside) == p * (p + 1) // 4

    return not pref(3) and not pref(7)


def window_signs(offsets):
    """Map relative time k=t+k -> sign. k in -11..0."""
    w = {0: 1}
    for i in range(1, 12):
        w[-i] = -1 if i in offsets else 1
    return w


def glue_consistent(off_a, off_b, c_a, c_b):
    """Place type A at t=0 and type B at t=c_b-c_a, so charged S coincide at -c_a.

    Returns None if some forced sign conflicts, else the merged relative signs.
    """
    t_a = 0
    t_b = c_b - c_a
    merged = {}
    for t, offs in ((t_a, off_a), (t_b, off_b)):
        w = window_signs(offs)
        for rel, val in w.items():
            k = t + rel
            if k in merged and merged[k] != val:
                return None
            merged[k] = val
    return merged, t_a, t_b


def p2_from_map(signs, t, d):
    s = m = 0
    offs = []
    for i in range(1, d + 1):
        if t - i not in signs:
            return None, ()
        x = signs[t - i]
        s += x
        m += i * x
        if x < 0:
            offs.append(i)
    return (s == 1 and m == 0), tuple(offs)


def min_p2_from_map(signs, t):
    for d in (3, 7, 11):
        ok, offs = p2_from_map(signs, t, d)
        if ok is None:
            return "unknown", ()
        if ok:
            return d, offs
    return None, ()


def try_complete_cycle(merged, t_a, t_b, off_a, off_b, p):
    """Try to realize the glue as a period-p word. Unassigned positions free."""
    # Need signs on a complete set of residues. For each residue, collect constraints.
    cons = {}
    for k, v in merged.items():
        r = k % p
        if r in cons and cons[r] != v:
            return False
        cons[r] = v
    free = [i for i in range(p) if i not in cons]
    # If too many free, search is 2^|free|; cap at 12 free bits.
    if len(free) > 12:
        return "too_free"
    for bits in itertools.product((-1, 1), repeat=len(free)):
        word = [0] * p
        for r, v in cons.items():
            word[r] = v
        for r, v in zip(free, bits):
            word[r] = v
        word = tuple(word)
        # verify both phases still have the intended min-lag-11 types
        def check(t, offs):
            d, o = None, ()
            s = m = 0
            found = None
            for i in range(1, 12):
                x = word[(t - i) % p]
                s += x
                m += i * x
                if i in (3, 7, 11) and s == 1 and m == 0:
                    oo = tuple(j for j in range(1, i + 1) if word[(t - j) % p] < 0)
                    found = (i, oo)
                    break
            return found == (11, offs)

        if word[t_a % p] > 0 and word[t_b % p] > 0 and check(t_a, off_a) and check(t_b, off_b):
            return "".join("A" if x > 0 else "S" for x in word)
    return False


def exhaust_injection(pmin, pmax):
    collisions = []
    u7_hits = []
    n = 0
    for p in range(pmin, pmax + 1):
        for raw in itertools.product((-1, 1), repeat=p):
            occupied = set()
            u11 = []
            for t, e in enumerate(raw):
                if e < 0:
                    continue
                s = m = 0
                dfound = None
                offs = ()
                for i in range(1, 12):
                    x = raw[(t - i) % p]
                    s += x
                    m += i * x
                    if i in (3, 7, 11) and s == 1 and m == 0:
                        offs = tuple(j for j in range(1, i + 1) if raw[(t - j) % p] < 0)
                        dfound = i
                        break
                if dfound is None:
                    continue
                if dfound == 3 and offs == LAG3:
                    occupied.add((t - 3) % p)
                elif dfound == 7 and offs == LAG7H1:
                    occupied.add((t - 7) % p)
                elif dfound == 7 and offs == LAG7H2:
                    occupied.add((t - 5) % p)
                if dfound == 11 and offs in CHARGE:
                    u11.append((t, offs))
            if not u11:
                continue
            phi = {}
            for t, offs in u11:
                c = CHARGE[offs]
                s = (t - c) % p
                n += 1
                if s in occupied and len(u7_hits) < 10:
                    u7_hits.append(
                        {
                            "p": p,
                            "word": "".join("A" if x > 0 else "S" for x in raw),
                            "t": t,
                            "type": offs,
                            "c": c,
                            "s": s,
                        }
                    )
                if s in phi and phi[s][0] != t:
                    if len(collisions) < 10:
                        collisions.append(
                            {
                                "p": p,
                                "word": "".join("A" if x > 0 else "S" for x in raw),
                                "t1": phi[s],
                                "t2": (t, offs, c),
                                "s": s,
                            }
                        )
                else:
                    phi[s] = (t, offs, c)
    return n, collisions, u7_hits


def main():
    print("protocol=H-20260908-01 residual charge injectivity", flush=True)
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
    raw = p2_offsets(11)
    minimal = [s for s in raw if is_minimal(s)]
    assert len(minimal) == 17
    assert set(minimal) == set(CHARGE)
    print("CHARGE=" + json.dumps({str(k): v for k, v in CHARGE.items()}), flush=True)

    by_c = {}
    for offs, c in CHARGE.items():
        by_c.setdefault(c, []).append(offs)
    print("BY_OFFSET=" + json.dumps({str(k): v for k, v in by_c.items()}), flush=True)

    # Pairwise glue on Z
    types = list(CHARGE)
    z_ok = []
    z_conflict = 0
    z_same_t = 0
    witnesses = []
    for a, b in itertools.product(types, repeat=2):
        ca, cb = CHARGE[a], CHARGE[b]
        if ca == cb:
            z_same_t += 1
            continue
        g = glue_consistent(a, b, ca, cb)
        if g is None:
            z_conflict += 1
            continue
        merged, ta, tb = g
        da, oa = min_p2_from_map(merged, ta)
        db, ob = min_p2_from_map(merged, tb)
        rec = {
            "A": a,
            "B": b,
            "cA": ca,
            "cB": cb,
            "tB_minus_tA": tb - ta,
            "minA": [da, oa],
            "minB": [db, ob],
        }
        # Both windows are fully present, so min lag is decided.
        if da == 11 and oa == a and db == 11 and ob == b:
            z_ok.append(rec)
            # try small periods
            for p in range(max(12, abs(tb - ta) + 1), 25):
                w = try_complete_cycle(merged, ta, tb, a, b, p)
                if w and w not in (False, "too_free"):
                    rec = dict(rec)
                    rec["cycle"] = {"p": p, "word": w}
                    witnesses.append(rec)
                    break
            else:
                rec = dict(rec)
                rec["cycle"] = None
                z_ok[-1] = rec
        else:
            rec["killed_by_minlag"] = True
            z_conflict += 1

    print("Z_SAME_OFFSET_PAIRS=" + str(z_same_t), flush=True)
    print("Z_SIGN_OR_MINLAG_CONFLICT=" + str(z_conflict), flush=True)
    print("Z_CONSISTENT_GLUES=" + str(len(z_ok)), flush=True)
    print("Z_GLUES=" + json.dumps(z_ok, sort_keys=True), flush=True)
    print("CYCLE_WITNESSES=" + json.dumps(witnesses, sort_keys=True), flush=True)

    n12, col12, u712 = exhaust_injection(1, 12)
    print(
        "EXHAUST_1_12 "
        + json.dumps({"n": n12, "collisions": col12, "u7": u712}, sort_keys=True),
        flush=True,
    )
    n14, col14, u714 = exhaust_injection(13, 14)
    print(
        "EXHAUST_13_14 "
        + json.dumps({"n": n14, "collisions": col14, "u7": u714}, sort_keys=True),
        flush=True,
    )

    if witnesses or col12 or col14 or u712 or u714:
        print("CONCLUSION=repair assignment collides or hits phi7 on a concrete word", flush=True)
    elif z_ok:
        print(
            "CONCLUSION=Z-consistent glues exist but no cyclic witness through p=24; "
            "exhaust p<=14 no collision; not an all-period injection theorem",
            flush=True,
        )
    else:
        print(
            "CONCLUSION=every distinct-offset pair of types is sign-inconsistent or "
            "loses minimality of lag 11; candidate all-period injection",
            flush=True,
        )


if __name__ == "__main__":
    main()
