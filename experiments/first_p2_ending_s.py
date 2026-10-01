#!/usr/bin/env python3
"""Frozen literal falsifier for H-20261001-02; computation is not a proof."""
import argparse
import hashlib
import itertools
import json
from pathlib import Path


def inspect(word):
    height = moment = 0
    ceiling = 0
    hits = []
    defects = []
    for n, bit in enumerate(word, 1):
        sign = 1 if bit == "A" else -1
        height += sign
        moment += n * sign
        ceiling = max(ceiling, height)
        if height == 1 and moment == 0:
            hits.append(n)
        defects.append(moment - n * (height - 1))
    return dict(mass=height, moment=moment, ceiling=ceiling,
                p2_prefixes=hits, defects=defects)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("phase", choices=["discovery", "holdout"])
    args = parser.parse_args()
    low, high = (0, 11) if args.phase == "discovery" else (12, 16)
    counts = dict(words=0, ceiling_two_words=0, no_p2_nonempty_words=0,
                  words_with_p2=0, first_p2_violations=0, defect_violations=0)
    for length in range(low, high + 1):
        for bits in itertools.product("AS", repeat=length):
            word = "".join(bits)
            d = inspect(word)
            counts["words"] += 1
            if d["ceiling"] > 2:
                continue
            counts["ceiling_two_words"] += 1
            if d["p2_prefixes"]:
                counts["words_with_p2"] += 1
                if word[d["p2_prefixes"][0] - 1] != "S":
                    counts["first_p2_violations"] += 1
            elif length:
                counts["no_p2_nonempty_words"] += 1
                if d["defects"][-1] <= 0:
                    counts["defect_violations"] += 1
    controls = {w: inspect(w) for w in
                ["", "A", "ASSA", "AAS", "AASASSA", "AAASSSASASA"]}
    assert controls["AASASSA"]["p2_prefixes"] == [3, 7]
    assert controls["AASASSA"]["ceiling"] == 2
    assert controls["AAASSSASASA"]["p2_prefixes"] == [11]
    assert controls["AAASSSASASA"]["ceiling"] == 3
    out = dict(protocol="H-20261001-02", base_revision=
               "65f457efdd36a2ec8f47283a9ddc36e173333d56", phase=args.phase,
               lengths=[low, high], source_sha256=
               hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
               counts=counts, controls=controls)
    print(json.dumps(out, indent=2, sort_keys=True))
    assert counts["first_p2_violations"] == counts["defect_violations"] == 0


if __name__ == "__main__":
    main()
