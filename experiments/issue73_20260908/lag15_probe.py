#!/usr/bin/env python3
"""Discovery: does every min-lag-15 type have an S incompatible with U7 and the
lag-11 CSP charge? One pass; a single uncovered type stops lag-by-lag.
"""
from __future__ import annotations

import hashlib
import itertools
import json
import subprocess

from lag11_verify_independent import CHOSEN
from lag11_safe_charge import analyze as analyze11, u7_possible

LAG15_TARGET = 15 * 16 // 4  # 60
LAG15_K = 7


def p2_offsets(d, k=None, target=None):
    k = (d - 1) // 2 if k is None else k
    target = d * (d + 1) // 4 if target is None else target
    return [s for s in itertools.combinations(range(1, d + 1), k) if sum(s) == target]


def has_prefix(offs, p):
    inside = tuple(x for x in offs if x <= p)
    kk = (p - 1) // 2
    return len(inside) == kk and sum(inside) == p * (p + 1) // 4


def sign_at(offs, rel, width):
    if rel == 0:
        return 1
    i = -rel
    if 1 <= i <= width and rel <= 0:
        return -1 if i in offs else 1
    return None


def phi11_possible(window_offs, s_time, tau, i_tau):
    """Can a min-lag-11 of type tau charged at i_tau occupy s_time?
    t' = s_time + i_tau, window of tau at t' must match forced signs.
    """
    tp = s_time + i_tau
    # t' is A
    if sign_at(window_offs, tp, 15) == -1:
        return False
    for k in range(1, 12):
        have = sign_at(window_offs, tp - k, 15)
        need = -1 if k in tau else 1
        if have is not None and have != need:
            return False
    return True


def main():
    print("protocol=H-20260908-01 lag-15 incompatibility probe", flush=True)
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
    raw = p2_offsets(15)
    print("raw_lag15=" + str(len(raw)), flush=True)
    minimal = [s for s in raw if not has_prefix(s, 3) and not has_prefix(s, 7) and not has_prefix(s, 11)]
    print("min_lag15=" + str(len(minimal)), flush=True)
    uncovered = []
    n_safe = []
    for offs in minimal:
        window = {0: 1}
        for i in range(1, 16):
            window[-i] = -1 if i in offs else 1
        safe = []
        for i in offs:
            s_time = -i
            u7 = [k for k in ("lag3", "lag7h1", "lag7h2") if u7_possible(window, s_time, k)]
            u11 = []
            for tau, it in CHOSEN.items():
                if phi11_possible(offs, s_time, tau, it):
                    u11.append((tau, it))
            if not u7 and not u11:
                safe.append(i)
        n_safe.append(len(safe))
        if not safe:
            uncovered.append(list(offs))
            if len(uncovered) <= 5:
                print("UNCOVERED_TYPE=" + json.dumps(list(offs)), flush=True)
    print("SAFE_COUNTS=" + json.dumps({str(k): n_safe.count(k) for k in sorted(set(n_safe))}), flush=True)
    print("N_UNCOVERED=" + str(len(uncovered)), flush=True)
    if uncovered:
        print("CONCLUSION=some min-lag-15 type has no S blocked by U7 and the lag-11 charge; lag-by-lag STOP candidate", flush=True)
    else:
        print("CONCLUSION=every min-lag-15 type has an S incompatible with U7∪φ11; method extends one more lag", flush=True)


if __name__ == "__main__":
    main()
