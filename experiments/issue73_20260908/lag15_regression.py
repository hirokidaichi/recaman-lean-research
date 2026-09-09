#!/usr/bin/env python3
"""Cyclic regression of the H_inject15 map. Not a proof."""
from __future__ import annotations

import hashlib
import itertools
import json
import subprocess
import sys

from lag11_verify_independent import CHOSEN as CHOSEN11


def load_assignment(path):
    with open(path) as f:
        for line in f:
            if line.startswith("ASSIGNMENT="):
                rows = json.loads(line.split("=", 1)[1])
                return {tuple(r["type"]): r["offset"] for r in rows}
    raise SystemExit("no ASSIGNMENT in " + path)


def min_p2(word, t, cap=15):
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


def phi7(d, offs, t, p):
    if d == 3 and offs == (3,):
        return (t - 3) % p
    if d == 7 and offs == (1, 6, 7):
        return (t - 7) % p
    if d == 7 and offs == (2, 5, 7):
        return (t - 5) % p
    return None


def main():
    print("protocol=H-20260908-04 cyclic regression of phi15", flush=True)
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
        print("usage: lag15_regression.py ASSIGNMENT_LOG", flush=True)
        return 2
    chosen15 = load_assignment(src)
    pmax = int(sys.argv[2]) if len(sys.argv) > 2 else 18
    nword = n15 = n11 = 0
    for p in range(1, pmax + 1):
        for raw in itertools.product((-1, 1), repeat=p):
            nword += 1
            u7 = {}
            u11 = {}
            u15 = {}
            for t, e in enumerate(raw):
                if e < 0:
                    continue
                d, offs = min_p2(raw, t)
                if d is None:
                    continue
                img7 = phi7(d, offs, t, p)
                if img7 is not None:
                    u7[t] = img7
                if d == 11:
                    if offs not in CHOSEN11:
                        raise SystemExit("unknown lag-11 type " + str(offs))
                    u11[t] = (t - CHOSEN11[offs]) % p
                    n11 += 1
                if d == 15:
                    if offs not in chosen15:
                        raise SystemExit("unknown lag-15 type " + str(offs))
                    u15[t] = (t - chosen15[offs]) % p
                    n15 += 1
            for name, imgs in (("U7", u7), ("U11", u11), ("U15", u15)):
                vals = list(imgs.values())
                if len(set(vals)) != len(vals):
                    raise SystemExit(
                        name
                        + " not injective "
                        + json.dumps(
                            {
                                "p": p,
                                "word": "".join("A" if x > 0 else "S" for x in raw),
                                "map": {str(k): v for k, v in imgs.items()},
                            }
                        )
                    )
            hits = []
            if set(u7.values()) & set(u11.values()):
                hits.append("U7∩U11")
            if set(u7.values()) & set(u15.values()):
                hits.append("U7∩U15")
            if set(u11.values()) & set(u15.values()):
                hits.append("U11∩U15")
            if hits:
                raise SystemExit(
                    "image collision "
                    + json.dumps(
                        {
                            "hits": hits,
                            "p": p,
                            "word": "".join("A" if x > 0 else "S" for x in raw),
                            "u7": u7,
                            "u11": u11,
                            "u15": u15,
                        }
                    )
                )
    print(
        json.dumps(
            {
                "words": nword,
                "lag11_events": n11,
                "lag15_events": n15,
                "max_period": pmax,
            }
        ),
        flush=True,
    )
    print(
        "PASS: no image collision and φ7,φ11,φ15 injective on all cyclic words p=1.."
        + str(pmax),
        flush=True,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
