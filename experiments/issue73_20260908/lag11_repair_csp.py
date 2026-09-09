#!/usr/bin/env python3
"""One repair: assign each min lag-11 type a U7-avoiding S offset with no Z-glue.

Allowed charges: exact following gap 2, or an S whose three U7 patterns
conflict with the forced length-11 window. Search assignments whose
distinct-offset pairs are all sign-inconsistent on Z. Then re-check
cyclic wrap by exhaust p<=14 and by attempting completions of any
surviving glue (should be none).
"""
from __future__ import annotations

import hashlib
import itertools
import json
import subprocess
from pathlib import Path

LAG7H1 = (1, 6, 7)
LAG7H2 = (2, 5, 7)


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


def window_of(offsets):
    w = {0: 1}
    for i in range(1, 12):
        w[-i] = -1 if i in offsets else 1
    return w


def u7_possible(window, s_time, kind):
    if kind == "lag3":
        tp = s_time + 3
        need = {tp: 1, tp - 1: 1, tp - 2: 1, tp - 3: -1}
    elif kind == "lag7h1":
        tp = s_time + 7
        need = {tp: 1}
        for off in range(1, 8):
            need[tp - off] = -1 if off in LAG7H1 else 1
    else:
        tp = s_time + 5
        need = {tp: 1}
        for off in range(1, 8):
            need[tp - off] = -1 if off in LAG7H2 else 1
    return all(rel not in window or window[rel] == val for rel, val in need.items())


def options_of(offsets):
    o = list(offsets)
    w = window_of(offsets)
    rows = []
    for j, i in enumerate(o):
        if j == 0:
            gap_kind, gap = "ge", i + 1
        else:
            gap_kind, gap = "eq", i - o[j - 1]
        kinds = [k for k in ("lag3", "lag7h1", "lag7h2") if u7_possible(w, -i, k)]
        allowed = (gap_kind == "eq" and gap == 2) or (not kinds)
        rows.append(
            {
                "offset": i,
                "shift": -j,
                "gap_kind": gap_kind,
                "gap": gap,
                "u7": kinds,
                "allowed": allowed,
            }
        )
    return rows


def glue_ok(off_a, off_b, c_a, c_b):
    if c_a == c_b:
        return False  # same recovery, not a collision
    t_a, t_b = 0, c_b - c_a
    merged = {}
    for t, offs in ((t_a, off_a), (t_b, off_b)):
        w = window_of(offs)
        for rel, val in w.items():
            k = t + rel
            if k in merged and merged[k] != val:
                return False
            merged[k] = val
    # both windows fully present: check min lag remains 11 with the same offsets
    def minp2(t, offs):
        s = m = 0
        for i in range(1, 12):
            x = merged[t - i]
            s += x
            m += i * x
            if i in (3, 7, 11) and s == 1 and m == 0:
                oo = tuple(j for j in range(1, i + 1) if merged[t - j] < 0)
                return i, oo
        return None, ()

    da, oa = minp2(t_a, off_a)
    db, ob = minp2(t_b, off_b)
    return da == 11 and oa == off_a and db == 11 and ob == off_b


def assignment_collides(types, charge):
    bad = []
    for a, b in itertools.product(types, repeat=2):
        if glue_ok(a, b, charge[a], charge[b]):
            bad.append((a, b, charge[a], charge[b], charge[b] - charge[a]))
    return bad


def exhaust(pmin, pmax, charge):
    cols = []
    u7s = []
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
                        offs = tuple(
                            j for j in range(1, i + 1) if raw[(t - j) % p] < 0
                        )
                        dfound = i
                        break
                if dfound is None:
                    continue
                if dfound == 3 and offs == (3,):
                    occupied.add((t - 3) % p)
                elif dfound == 7 and offs == LAG7H1:
                    occupied.add((t - 7) % p)
                elif dfound == 7 and offs == LAG7H2:
                    occupied.add((t - 5) % p)
                if dfound == 11 and offs in charge:
                    u11.append((t, offs))
            if not u11:
                continue
            phi = {}
            for t, offs in u11:
                c = charge[offs]
                s = (t - c) % p
                n += 1
                if s in occupied and len(u7s) < 5:
                    u7s.append({"p": p, "t": t, "offs": offs, "s": s})
                if s in phi and phi[s][0] != t and len(cols) < 5:
                    cols.append(
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
    return n, cols, u7s


def main():
    print("protocol=H-20260908-01 one-repair CSP on U7-avoiding offsets", flush=True)
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
    types = [s for s in p2_offsets(11) if is_minimal(s)]
    assert len(types) == 17
    allowed = {}
    for offs in types:
        opts = options_of(offs)
        print("TYPE " + json.dumps({"offsets": offs, "options": opts}), flush=True)
        allowed[offs] = [r["offset"] for r in opts if r["allowed"]]
    print("ALLOWED=" + json.dumps({str(k): v for k, v in allowed.items()}), flush=True)
    uncovered = [t for t in types if not allowed[t]]
    print("UNCOVERED=" + json.dumps(uncovered), flush=True)
    if uncovered:
        print("CONCLUSION=some type has no U7-avoiding charge; repair fails", flush=True)
        return

    # Precompute colliding offset-pairs of types
    pair_bad = {}
    for a, b in itertools.product(types, repeat=2):
        for ca, cb in itertools.product(allowed[a], allowed[b]):
            if glue_ok(a, b, ca, cb):
                pair_bad.setdefault((a, b), set()).add((ca, cb))
    print(
        "N_TYPE_PAIRS_WITH_SOME_GLUE="
        + str(len(pair_bad)),
        flush=True,
    )
    print(
        "GLUE_KEYS="
        + json.dumps([[list(a), list(b), [list(x) for x in sorted(v)]] for (a, b), v in pair_bad.items()]),
        flush=True,
    )

    # Backtrack: types with fewest options first
    order = sorted(types, key=lambda t: len(allowed[t]))
    found = []

    def rec(i, ch):
        if len(found) >= 3:
            return
        if i == len(order):
            found.append(dict(ch))
            return
        t = order[i]
        for c in allowed[t]:
            ok = True
            for u, cu in ch.items():
                if (t, u) in pair_bad and (c, cu) in pair_bad[(t, u)]:
                    ok = False
                    break
                if (u, t) in pair_bad and (cu, c) in pair_bad[(u, t)]:
                    ok = False
                    break
            if not ok:
                continue
            ch[t] = c
            rec(i + 1, ch)
            del ch[t]

    rec(0, {})
    print("N_SOLUTIONS_SHOWN=" + str(len(found)), flush=True)
    if not found:
        print(
            "CONCLUSION=no assignment of U7-avoiding offsets is Z-glue-free; "
            "the one repair fails",
            flush=True,
        )
        return
    for i, ch in enumerate(found):
        print("SOLUTION%d=" % i + json.dumps({str(k): v for k, v in ch.items()}), flush=True)
        n, cols, u7s = exhaust(1, 14, ch)
        print(
            "SOLUTION%d_EXHAUST_1_14=" % i
            + json.dumps({"n": n, "collisions": cols, "u7": u7s}),
            flush=True,
        )
    print(
        "CONCLUSION=found a Z-glue-free U7-avoiding assignment; cyclic wrap still checked",
        flush=True,
    )


if __name__ == "__main__":
    main()
