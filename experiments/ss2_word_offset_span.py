#!/usr/bin/env python3
"""Frozen fixed-SS2 offset-span falsifier H-20261001-05 (abstract words)."""
import argparse
import hashlib
import json
from pathlib import Path

from terminal_a_budget import data

CORE = "SAAASSAAASS"


def mass_one_prefixes(word):
    height = moment = 0
    out = []
    for j, bit in enumerate(word, 1):
        sign = 1 if bit == "A" else -1
        height += sign
        moment += j * sign
        if height == 1 and j < len(word):
            out.append([j, moment])
    return out


def expected_prefixes(k):
    out = [[2*k+3, 3*k+4], [2*k+5, 3*k+3], [2*k+7, 3*k+4]]
    if k:
        out += [[2*k+11+2*i, 3*k-i] for i in range(3*k)]
    return out


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("phase", choices=["discovery", "holdout"])
    args = parser.parse_args()
    low, high = (0, 10) if args.phase == "discovery" else (11, 80)
    rows = []
    for k in range(low, high+1):
        word = "SA"*k + CORE + "AS"*(3*k)
        d = data(word)
        positions = [j for j, b in enumerate(word, 1) if b == "S"]
        assert d["minimal"] and d["mass"] == 1 and d["moment"] == 0, (k, d)
        assert d["ss"] == 2 and d["tail"] == 0 and "SAAS" not in "A"+word, (k, d)
        assert positions[0] == 1 and positions[-1] == 8*k+11 and len(word) == 8*k+11
        actual = mass_one_prefixes(word)
        assert actual == expected_prefixes(k), (k, actual, expected_prefixes(k))
        assert all(moment > 0 for _, moment in actual)
        rows.append({"k": k, **d, "marked_s": positions[0], "oldest_s": positions[-1],
                     "offset_span": positions[-1]-positions[0],
                     "complete_proper_mass_one_prefixes": actual})
    out = {"protocol": "H-20261001-05", "phase": args.phase,
           "base": "cbe51b7b1216f9700f432eb14803277113c02af4",
           "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
           "k_range": [low, high], "rows": rows}
    if args.phase == "discovery":
        out["negative_controls"] = {
            "wrong_core_k1": data("SA" + "AAASSSASASA" + "AS"*3),
            "one_extra_AS_k1": data("SA" + CORE + "AS"*4),
        }
    print(json.dumps(out, indent=2))


if __name__ == "__main__":
    main()
