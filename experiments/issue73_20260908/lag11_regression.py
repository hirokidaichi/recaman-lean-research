#!/usr/bin/env python3
"""Regression of the H_inject11 map on cyclic words. Not a proof."""
from __future__ import annotations

import hashlib
import itertools
import json
import subprocess

from lag11_verify_independent import CHOSEN


def min_p2(word, t, cap=11):
    p = len(word)
    s = m = 0
    offs = []
    for d in range(1, cap + 1):
        x = word[(t - d) % p]
        s += x
        m += d * x
        if x < 0:
            offs.append(d)
        if (s, m) == (1, 0):
            return d, tuple(offs)
    return None, ()


def phi7(word, t, d, offs):
    p = len(word)
    if d == 3 and offs == (3,):
        return (t - 3) % p
    if d == 7 and offs == (1, 6, 7):
        return (t - 7) % p
    if d == 7 and offs == (2, 5, 7):
        return (t - 5) % p
    return None


def phi11(t, offs, p):
    i = CHOSEN[offs]
    return (t - i) % p


def main():
    print("protocol=H-20260908-01 cyclic regression of phi11", flush=True)
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
    nword = n11 = 0
    for p in range(1, 19):
        for raw in itertools.product((-1, 1), repeat=p):
            if sum(raw) <= 0:
                continue
            nword += 1
            u7 = {}
            u11 = {}
            for t, e in enumerate(raw):
                if e < 0:
                    continue
                d, offs = min_p2(raw, t)
                if d is None:
                    continue
                img7 = phi7(raw, t, d, offs)
                if img7 is not None:
                    u7[t] = img7
                if d == 11:
                    assert offs in CHOSEN, (p, t, offs)
                    u11[t] = phi11(t, offs, p)
                    n11 += 1
            imgs7 = list(u7.values())
            imgs11 = list(u11.values())
            if len(set(imgs7)) != len(imgs7):
                raise SystemExit("U7 not injective " + str(raw))
            if len(set(imgs11)) != len(imgs11):
                raise SystemExit(
                    "U11 not injective "
                    + json.dumps({"p": p, "word": "".join("A" if x > 0 else "S" for x in raw), "u11": u11})
                )
            if set(imgs7) & set(imgs11):
                raise SystemExit(
                    "U7/U11 image collision "
                    + json.dumps(
                        {
                            "p": p,
                            "word": "".join("A" if x > 0 else "S" for x in raw),
                            "u7": u7,
                            "u11": u11,
                            "hit": sorted(set(imgs7) & set(imgs11)),
                        }
                    )
                )
    print(json.dumps({"positive_words": nword, "lag11_events": n11, "max_period": 18}), flush=True)
    print("PASS: no image collision and both maps injective on p=1..18 positive words", flush=True)


if __name__ == "__main__":
    main()
