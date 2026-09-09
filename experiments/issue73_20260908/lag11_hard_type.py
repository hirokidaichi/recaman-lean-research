#!/usr/bin/env python3
"""Discovery-only: residual S after φ7 for the hard lag-11 type (1,4,7,10,11).

Uses previously enumerated p=1..18 positive words as a NEW property check
on the hard type, not as a holdout for E-067. Stop this charge class if some
occurrence has empty residual (all five S already taken by φ7).
"""
from __future__ import annotations

import hashlib
import itertools
import json
import subprocess
from collections import Counter
from pathlib import Path

HARD = (1, 4, 7, 10, 11)


def p2_min(word, t, cap=11):
    p = len(word)
    s = m = 0
    for d in range(1, cap + 1):
        x = word[(t - d) % p]
        s += x
        m += d * x
        if (s, m) == (1, 0):
            offs = tuple(sorted(i for i in range(1, d + 1) if word[(t - i) % p] < 0))
            return d, offs
    return None, ()


def phi7(word, t, d, offs):
    p = len(word)
    if d == 3:
        assert offs == (3,)
        return (t - 3) % p, "lag3"
    if d == 7 and offs == (1, 6, 7):
        return (t - 7) % p, "lag7h1"
    if d == 7 and offs == (2, 5, 7):
        return (t - 5) % p, "lag7h2"
    return None, None


def main() -> None:
    print("protocol=H-20260908-01 hard type residual after phi7", flush=True)
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
    occ = 0
    empty = 0
    residual_sizes = Counter()
    empty_witness = None
    taken_kinds = Counter()
    for p in range(1, 19):
        for raw in itertools.product((-1, 1), repeat=p):
            if sum(raw) <= 0:
                continue
            images = {}
            hard_ts = []
            for t, e in enumerate(raw):
                if e < 0:
                    continue
                d, offs = p2_min(raw, t)
                if d is None:
                    continue
                img, kind = phi7(raw, t, d, offs)
                if img is not None:
                    images[t] = (img, kind)
                if d == 11 and offs == HARD:
                    hard_ts.append(t)
            occupied = {img for img, _ in images.values()}
            for t in hard_ts:
                occ += 1
                domain = {(t - i) % p for i in HARD}
                residual = domain - occupied
                residual_sizes[len(residual)] += 1
                for i in HARD:
                    s = (t - i) % p
                    if s in occupied:
                        # who took it?
                        takers = [k for k, (img, kind) in images.items() if img == s]
                        for k in takers:
                            taken_kinds[(i, images[k][1])] += 1
                if not residual:
                    empty += 1
                    if empty_witness is None:
                        empty_witness = {
                            "period": p,
                            "word": "".join("A" if x > 0 else "S" for x in raw),
                            "t": t,
                            "domain": sorted(domain),
                            "phi7": {str(k): v for k, v in images.items()},
                        }
    print("HARD_OCCURRENCES=" + str(occ), flush=True)
    print("EMPTY_RESIDUAL=" + str(empty), flush=True)
    print("RESIDUAL_SIZES=" + json.dumps(dict(sorted(residual_sizes.items()))), flush=True)
    print(
        "TAKEN_OFFSET_KIND="
        + json.dumps({str(k): v for k, v in taken_kinds.items()}),
        flush=True,
    )
    if empty_witness:
        print("EMPTY_WITNESS=" + json.dumps(empty_witness, sort_keys=True), flush=True)
        print("STOP: hard type can have all five S taken by phi7; gap-type extension collides", flush=True)
    else:
        print("NO_EMPTY_RESIDUAL_THROUGH_P18: not an all-period theorem", flush=True)


if __name__ == "__main__":
    main()
