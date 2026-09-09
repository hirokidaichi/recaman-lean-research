#!/usr/bin/env python3
"""Complete CSP: injective φ7∪φ11-blocked charges for all min-lag-15 types.

One unit (H-20260908-04). Unsatisfiability stops lag-by-lag. A solution is a
candidate all-period injection, not E-070.
"""
from __future__ import annotations

import hashlib
import itertools
import json
import subprocess
import sys

from lag11_verify_independent import CHOSEN
from lag11_safe_charge import u7_possible

LAG15 = 15
LAG15_K = 7
LAG15_TARGET = 15 * 16 // 4  # 60


def p2_offsets(d):
    k = (d - 1) // 2
    target = d * (d + 1) // 4
    return [s for s in itertools.combinations(range(1, d + 1), k) if sum(s) == target]


def has_prefix(offs, p):
    inside = tuple(x for x in offs if x <= p)
    kk = (p - 1) // 2
    return len(inside) == kk and sum(inside) == p * (p + 1) // 4


def min_lag15():
    return [
        s
        for s in p2_offsets(LAG15)
        if not has_prefix(s, 3) and not has_prefix(s, 7) and not has_prefix(s, 11)
    ]


def sign_at(offs, rel, width=LAG15):
    if rel == 0:
        return 1
    i = -rel
    if 1 <= i <= width:
        return -1 if i in offs else 1
    return None


def phi11_possible(window_offs, s_time, tau, i_tau):
    tp = s_time + i_tau
    if sign_at(window_offs, tp) == -1:
        return False
    for k in range(1, 12):
        have = sign_at(window_offs, tp - k)
        need = -1 if k in tau else 1
        if have is not None and have != need:
            return False
    return True


def safe_offsets(offs):
    window = {0: 1}
    for i in range(1, LAG15 + 1):
        window[-i] = -1 if i in offs else 1
    safe = []
    for i in offs:
        s_time = -i
        u7 = any(u7_possible(window, s_time, k) for k in ("lag3", "lag7h1", "lag7h2"))
        u11 = any(phi11_possible(offs, s_time, tau, it) for tau, it in CHOSEN.items())
        if not u7 and not u11:
            safe.append(i)
    return safe


def signs(tau, t=0, width=LAG15):
    out = {t: 1}
    for k in range(1, width + 1):
        out[t - k] = -1 if k in tau else 1
    return out


def merge_ok(a, b):
    out = dict(a)
    for k, v in b.items():
        if k in out and out[k] != v:
            return False
        out[k] = v
    return True


def pair_open(tau, i, sig, j):
    """True when the Z-windows at collision distance can merge (bad for injection)."""
    if tau == sig and i == j:
        return False
    return merge_ok(signs(tau, 0), signs(sig, j - i))


def search(types, options):
    n = len(types)
    nopts = [len(options[t]) for t in range(n)]
    # conflict[i][a][j] = bitmask of options of j that cannot coexist with i:=a
    conflict = [[ [0] * n for _ in range(nopts[i]) ] for i in range(n)]
    n_open_combos = 0
    n_checked = 0
    for i in range(n):
        for a, ia in enumerate(options[i]):
            for j in range(n):
                if i == j:
                    continue
                mask = 0
                for b, jb in enumerate(options[j]):
                    n_checked += 1
                    if pair_open(types[i], ia, types[j], jb) or pair_open(
                        types[j], jb, types[i], ia
                    ):
                        mask |= 1 << b
                        n_open_combos += 1
                conflict[i][a][j] = mask
    domains0 = [(1 << nopts[i]) - 1 for i in range(n)]
    assigned = [-1] * n
    nodes = [0]
    sol = []

    def propagate(dom):
        changed = True
        while changed:
            changed = False
            for i in range(n):
                d = dom[i]
                if d == 0:
                    return False
                if assigned[i] >= 0:
                    continue
                if d & (d - 1) == 0:
                    a = d.bit_length() - 1
                    assigned[i] = a
                    changed = True
                    for j in range(n):
                        if i == j:
                            continue
                        nd = dom[j] & ~conflict[i][a][j]
                        if nd != dom[j]:
                            dom[j] = nd
                            if nd == 0:
                                return False
                            changed = True
        return True

    def rec(dom):
        nodes[0] += 1
        if nodes[0] % 100000 == 0:
            nset = sum(1 for x in assigned if x >= 0)
            print("PROGRESS_NODES=" + str(nodes[0]) + " assigned=" + str(nset), flush=True)
        saved = assigned[:]
        if not propagate(dom):
            assigned[:] = saved
            return False
        best = None
        for i in range(n):
            if assigned[i] >= 0:
                continue
            bits = dom[i].bit_count()
            if bits == 0:
                assigned[:] = saved
                return False
            if best is None or bits < best[0] or (bits == best[0] and i < best[1]):
                best = (bits, i)
        if best is None:
            sol.append(assigned[:])
            assigned[:] = saved
            return True
        i = best[1]
        d = dom[i]
        order = list(range(nopts[i]))
        # fewest-conflicts first (LCV)
        def lcv(a):
            cut = 0
            for j in range(n):
                if assigned[j] >= 0 or i == j:
                    continue
                cut += (dom[j] & conflict[i][a][j]).bit_count()
            return cut

        order.sort(key=lcv)
        for a in order:
            if not (d & (1 << a)):
                continue
            assigned[i] = a
            ndom = dom[:]
            ok = True
            for j in range(n):
                if j == i:
                    ndom[j] = 1 << a
                    continue
                ndom[j] = ndom[j] & ~conflict[i][a][j]
                if ndom[j] == 0:
                    ok = False
                    break
            if ok and rec(ndom):
                assigned[:] = saved
                return True
            assigned[i] = -1
        assigned[:] = saved
        return False

    found = rec(domains0[:])
    return {
        "found": found,
        "n_checked": n_checked,
        "n_open_combos": n_open_combos,
        "nodes": nodes[0],
        "assignment": sol[0] if sol else None,
        "nopts": nopts,
    }


def main():
    print("protocol=H-20260908-04 CSP search for injective U7∪φ11-safe lag-15 charges", flush=True)
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
    types = min_lag15()
    print("raw_lag15=" + str(len(p2_offsets(LAG15))), flush=True)
    print("min_lag15=" + str(len(types)), flush=True)
    options = []
    uncovered = []
    n_safe = []
    for tau in types:
        safe = safe_offsets(tau)
        options.append(safe)
        n_safe.append(len(safe))
        print("OPTIONS=" + json.dumps({"type": list(tau), "safe": safe}), flush=True)
        if not safe:
            uncovered.append(list(tau))
    print(
        "SAFE_COUNTS=" + json.dumps({str(k): n_safe.count(k) for k in sorted(set(n_safe))}),
        flush=True,
    )
    print("N_UNCOVERED=" + str(len(uncovered)), flush=True)
    if uncovered:
        print(
            "CONCLUSION=some min-lag-15 type has no blocked S; lag-by-lag STOP",
            flush=True,
        )
        return 1
    sys.setrecursionlimit(10000)
    rec = search(types, options)
    print("N_OPTION_PAIRS_CHECKED=" + str(rec["n_checked"]), flush=True)
    print("N_OPEN_OPTION_COMBOS=" + str(rec["n_open_combos"]), flush=True)
    print("SEARCH_NODES=" + str(rec["nodes"]), flush=True)
    if not rec["found"]:
        print(
            "CONCLUSION=no choice of φ7∪φ11-blocked offsets is pairwise injective; "
            "lag-by-lag type-to-offset class STOPPED",
            flush=True,
        )
        return 0
    chosen = []
    for k, tau in enumerate(types):
        a = rec["assignment"][k]
        chosen.append({"type": list(tau), "offset": options[k][a]})
    print("ASSIGNMENT=" + json.dumps(chosen), flush=True)
    n_open = 0
    for a, b in itertools.product(range(len(types)), repeat=2):
        if a == b:
            continue
        ia = options[a][rec["assignment"][a]]
        ib = options[b][rec["assignment"][b]]
        if pair_open(types[a], ia, types[b], ib):
            n_open += 1
            if n_open <= 5:
                print(
                    "OPEN="
                    + json.dumps(
                        {
                            "a": list(types[a]),
                            "ia": ia,
                            "b": list(types[b]),
                            "ib": ib,
                        }
                    ),
                    flush=True,
                )
    print("OPEN_PAIRS=" + str(n_open), flush=True)
    if n_open == 0:
        print(
            "CONCLUSION=found a pairwise-injective φ7∪φ11-blocked offset choice",
            flush=True,
        )
        return 0
    print("CONCLUSION=search bug: reported solution has open pairs", flush=True)
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
