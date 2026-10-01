#!/usr/bin/env python3
"""Exact reproduction and prefix-classification checker for H-20261001-04.

The q=0..40 ranges reuse E-361 data. This script was frozen for reruns
after an initial exploratory probe; it is not an independent new holdout.
"""
import hashlib
import json
from pathlib import Path

from terminal_a_budget import data, witness, witnesses


def main():
    out = {
        "base": "cbe51b7b1216f9700f432eb14803277113c02af4",
        "protocol": "H-20261001-04",
        "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "construction_source_sha256": hashlib.sha256(
            Path(__file__).with_name("terminal_a_budget.py").read_bytes()).hexdigest(),
        "reused_discovery": witnesses(0, 10),
        "reused_holdout": witnesses(11, 40),
        "prefix_classification": [],
        "boundary_controls": [],
    }
    for q in range(3, 41):
        n = q*q - 2*q - 2
        word = witness(q)
        actual = []
        height = moment = 0
        for j, bit in enumerate(word, 1):
            sign = 1 if bit == "A" else -1
            height += sign
            moment += j * sign
            if height == 1 and j < len(word):
                actual.append([j, moment])
        expected = [[1, 1]] + [[2*i+3, -i-2] for i in range(1, n+1)] + [[2*n+5, -n-3]]
        assert actual == expected, (q, actual, expected)
        out["prefix_classification"].append({
            "q": q, "n": n, "proper_mass_one_prefix_count": len(actual),
            "actual_equals_complete_expected": actual == expected,
            "actual_sha256": hashlib.sha256(json.dumps(actual).encode()).hexdigest(),
        })
        if q == 3:
            out["q3_exact_prefixes"] = actual
    for q in range(4):
        n = max(q*q - 2*q - 2, 0)
        word = "AAAS" + "SA"*n + "S"*q + "A"*max(q-1, 0)
        out["boundary_controls"].append({"q": q, "n": n, "word": word, **data(word)})
    print(json.dumps(out, indent=2))


if __name__ == "__main__":
    main()
