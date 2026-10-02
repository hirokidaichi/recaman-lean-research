#!/usr/bin/env python3
"""H-20261002-01 finite falsifier; reused ranges, never an all-length proof."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

from ss2_short_tight import data, p2_words


def suffix_covers(w, current="A", low=True):
    r = data(w)["oldest"]
    out = []
    for c in range(1, r):
        if w[c-1] != current:
            continue
        v = w[c:r]
        q = data(v)
        if q["mass"] == 1 and q["moment"] == 0 and (not low or q["ss"] <= 1):
            out.append({"current_offset": c, "window": v, "ss": q["ss"],
                        "endpoint": r})
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("phase", choices=["discovery", "holdout"])
    phase = ap.parse_args().phase
    lengths = [3, 7, 11, 15, 19] if phase == "discovery" else [23]
    rows, controls = [], {}
    for length in lengths:
        p2 = donors = candidates = 0
        tails = {}
        for w in p2_words(length):
            p2 += 1
            d = data(w)
            if d["ss"] == 2 and d["minimal"]:
                donors += 1
                tails[d["tail"]] = tails.get(d["tail"], 0) + 1
                candidates += sum(w[c-1] == "A" for c in range(1, d["oldest"]))
                assert not suffix_covers(w), (w, suffix_covers(w))
                if "without_current_A" not in controls and suffix_covers(w, "S"):
                    controls["without_current_A"] = {"donor": d, "covers": suffix_covers(w, "S")}
            if d["ss"] == 2 and not d["minimal"] and "without_minimality" not in controls:
                if suffix_covers(w):
                    controls["without_minimality"] = {"donor": d, "covers": suffix_covers(w)}
            if d["ss"] >= 3 and d["minimal"] and "without_SS2" not in controls:
                if suffix_covers(w):
                    controls["without_SS2"] = {"donor": d, "covers": suffix_covers(w)}
        rows.append(dict(length=length, p2=p2, minimal_ss2=donors,
                         current_A_suffix_candidates=candidates, terminal_A_lengths=tails,
                         violations=0))
    # Removing low-SS admits the identical donor as its own endpoint cover.
    d = data("SAAASSAAASS")
    assert d["minimal"] and d["ss"] == 2
    controls["without_cover_lowSS"] = {"donor": d, "cover_current_offset": 0,
                                       "same_window": True}
    root = Path(__file__).resolve().parents[1]
    out = dict(protocol="H-20261002-01", phase=phase, reused_ranges=True,
               base=subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip(),
               source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
               lengths=lengths, rows=rows, negative_controls=controls)
    print(json.dumps(out, indent=2))


if __name__ == "__main__":
    main()
