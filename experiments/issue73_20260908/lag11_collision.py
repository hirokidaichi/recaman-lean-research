#!/usr/bin/env python3
"""Finite overlap check: can two chosen lag-11 charges hit the same S?

For each pair of minimal types with chosen offsets i,j, set δ=i-j and
force both windows. A sign contradiction means that pair cannot collide.
A consistent overlap is a collision skeleton; we then ask whether both
windows remain minimal lag-11 (no P2 at 3 or 7).
"""
from __future__ import annotations

import hashlib
import itertools
import json
import subprocess

from lag11_safe_charge import analyze, minimal_lag11


def choose(offsets):
    rec = analyze(offsets)
    safe = rec["safe"]
    safe.sort(key=lambda r: (0 if r["gap_kind"] == "eq" and r["gap"] == 2 else 1, r["offset"]))
    return safe[0]["offset"]


def window_signs(offsets, t=0):
    """Map time -> sign on {t} ∪ {t-1..t-11}."""
    signs = {t: 1}
    for k in range(1, 12):
        signs[t - k] = -1 if k in offsets else 1
    return signs


def merge(a, b):
    out = dict(a)
    for k, v in b.items():
        if k in out and out[k] != v:
            return None
        out[k] = v
    return out


def has_p2(signs, t, d):
    s = m = 0
    for i in range(1, d + 1):
        e = signs.get(t - i)
        if e is None:
            return None  # unknown
        s += e
        m += i * e
    return s == 1 and m == 0


def main():
    print("protocol=H-20260908-01 pairwise charge collision of lag-11 types", flush=True)
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
    types = minimal_lag11()
    chosen = [(tau, choose(tau)) for tau in types]
    print("CHOSEN=" + json.dumps([{"type": t, "offset": i} for t, i in chosen]), flush=True)

    collisions = []
    blocked = 0
    for (tau, i), (sig, j) in itertools.product(chosen, repeat=2):
        if (tau, i) == (sig, j):
            # same type, same offset: collision iff two distinct t with t-i = t'-i
            # hence t=t'. No distinct collision.
            continue
        # t1 - i = t2 - j  ⇒  (t2-t1) = j-i. Place tau at 0, sig at j-i.
        delta = j - i
        # shared S at -i = delta - j
        a = window_signs(tau, 0)
        b = window_signs(sig, delta)
        m = merge(a, b)
        if m is None:
            blocked += 1
            continue
        # both must still look like min-lag-11: P2 at 11 true, not at 3 or 7
        # windows fully determined on their 11 past signs, so this is exact
        p2_tau = [d for d in (3, 7, 11) if has_p2(m, 0, d)]
        p2_sig = [d for d in (3, 7, 11) if has_p2(m, delta, d)]
        tau_min11 = p2_tau == [11]
        sig_min11 = p2_sig == [11]
        if tau_min11 and sig_min11:
            collisions.append(
                {
                    "type_a": tau,
                    "offset_a": i,
                    "type_b": sig,
                    "offset_b": j,
                    "delta": delta,
                    "shared_S": -i,
                    "signs": {str(k): v for k, v in sorted(m.items())},
                }
            )
    print("blocked_inconsistent_pairs=" + str(blocked), flush=True)
    print("N_COLLISION_SKELETONS=" + str(len(collisions)), flush=True)
    for c in collisions[:20]:
        print("COLLISION=" + json.dumps({"type_a": c["type_a"], "ia": c["offset_a"], "type_b": c["type_b"], "ib": c["offset_b"], "delta": c["delta"]}), flush=True)
    if collisions:
        print("CONCLUSION=chosen offsets admit overlapping min-lag-11 windows sharing an S; assignment not injective", flush=True)
    else:
        print("CONCLUSION=no two chosen charges can share an S; pairwise window obstruction gives injectivity of this assignment", flush=True)


if __name__ == "__main__":
    main()
