#!/usr/bin/env python3
"""Search a choice of U7-safe offsets that is pairwise injective at the
correct collision distance δ = j-i.

The first assignment failed cyclic regression because collision.py used δ=i-j.
"""
from __future__ import annotations

import hashlib
import itertools
import json
import subprocess

from lag11_safe_charge import analyze, minimal_lag11


def signs(tau, t=0):
    out = {t: 1}
    for k in range(1, 12):
        out[t - k] = -1 if k in tau else 1
    return out


def merge_ok(a, b):
    out = dict(a)
    for k, v in b.items():
        if k in out and out[k] != v:
            return False
        out[k] = v
    return True


def pair_collides(tau, i, sig, j):
    if (tau, i) == (sig, j):
        return False
    delta = j - i
    return merge_ok(signs(tau, 0), signs(sig, delta))


def main():
    print("protocol=H-20260908-01 CSP search for injective U7-safe lag-11 charges", flush=True)
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
    options = []
    for tau in types:
        safe = [r["offset"] for r in analyze(tau)["safe"]]
        assert safe, tau
        options.append((tau, safe))
        print("OPTIONS=" + json.dumps({"type": tau, "safe": safe}), flush=True)

    # greedy: backtrack
    assignment = [None] * len(types)

    def ok_prefix(k):
        tau, i = types[k], assignment[k]
        for n in range(k):
            if pair_collides(types[n], assignment[n], tau, i):
                return False
            if pair_collides(tau, i, types[n], assignment[n]):
                return False
        return True

    def rec(k):
        if k == len(types):
            return True
        tau, safe = options[k]
        for i in safe:
            assignment[k] = i
            if ok_prefix(k) and rec(k + 1):
                return True
        assignment[k] = None
        return False

    found = rec(0)
    if not found:
        print("CONCLUSION=no choice of U7-safe offsets is pairwise injective; this charge class fails", flush=True)
        return
    chosen = [{"type": types[k], "offset": assignment[k]} for k in range(len(types))]
    print("ASSIGNMENT=" + json.dumps(chosen), flush=True)
    # verify all ordered pairs
    n_open = 0
    for a, b in itertools.product(range(len(types)), repeat=2):
        if a == b:
            continue
        if pair_collides(types[a], assignment[a], types[b], assignment[b]):
            n_open += 1
            print("OPEN=" + json.dumps({"a": types[a], "ia": assignment[a], "b": types[b], "ib": assignment[b]}), flush=True)
    print("OPEN_PAIRS=" + str(n_open), flush=True)
    print("CONCLUSION=found a pairwise-injective U7-safe offset choice" if n_open == 0 else "CONCLUSION=search bug", flush=True)


if __name__ == "__main__":
    main()
