#!/usr/bin/env python3
"""Frozen falsifier for H-20261001-01; exact integer word arithmetic only."""
import argparse
import hashlib
import itertools
import json
from pathlib import Path


def data(word):
    height = moment = ss = 0
    previous = None
    p2_prefixes = []
    max_height = 0
    for j, bit in enumerate(word, 1):
        sign = 1 if bit == "A" else -1
        height += sign
        moment += j * sign
        max_height = max(max_height, height)
        ss += previous == bit == "S"
        if height == 1 and moment == 0:
            p2_prefixes.append(j)
        previous = bit
    tail = len(word) - len(word.rstrip("A"))
    return dict(length=len(word), mass=height, moment=moment, ss=ss,
                tail=tail, max_height=max_height, p2_prefixes=p2_prefixes,
                minimal=p2_prefixes == [len(word)])


def p2_words(length):
    # mass=1 fixes the A count. moment=0 fixes the sum of A offsets.
    if length % 4 != 3:
        return
    target = length * (length + 1) // 4
    for positions in itertools.combinations(range(1, length + 1), (length + 1) // 2):
        if sum(positions) == target:
            chosen = set(positions)
            yield "".join("A" if j in chosen else "S" for j in range(1, length + 1))


def small_crosscheck():
    total = 0
    for length in range(12):
        literal = set()
        for bits in itertools.product("AS", repeat=length):
            word = "".join(bits)
            # Independent direct sums, not the recurrence used by data().
            signs = [1 if bit == "A" else -1 for bit in bits]
            if sum(signs) == 1 and sum(j * s for j, s in enumerate(signs, 1)) == 0:
                literal.add(word)
        assert literal == set(p2_words(length)), length
        total += len(literal)
    return dict(binary_words=2**12 - 1, p2_words=total, lengths=[0, 11])


def census(length):
    counts = dict(p2=0, minimal=0, a_ended=0, minimal_a_ended=0,
                  ceiling_two=0, weak_bound_violations=0,
                  strict_bound_violations=0, prefix_lemma_violations=0)
    extrema = {}
    for word in p2_words(length):
        d = data(word)
        assert d["mass"] == 1 and d["moment"] == 0
        counts["p2"] += 1
        counts["minimal"] += d["minimal"]
        counts["a_ended"] += d["tail"] > 0
        counts["minimal_a_ended"] += d["minimal"] and d["tail"] > 0
        if d["tail"] > d["ss"]:
            counts["weak_bound_violations"] += 1
        if d["minimal"] and d["tail"] > 0 and d["tail"] >= d["ss"]:
            counts["strict_bound_violations"] += 1
        if d["max_height"] <= 2:
            counts["ceiling_two"] += 1
            if not any(word[j - 1] == "S" for j in d["p2_prefixes"]):
                counts["prefix_lemma_violations"] += 1
        if d["minimal"]:
            extrema[d["ss"]] = max(extrema.get(d["ss"], 0), d["tail"])
    return dict(length=length, counts=counts,
                max_minimal_tail_by_ss=dict(sorted(extrema.items())))


def witness(q):
    if q < 3:
        return ["AAS", "SAAAASS", "AAASSSASASA"][q]
    n = q*q - 2*q - 2
    return "AAAS" + "SA"*n + "S"*q + "A"*(q - 1)


def witnesses(low, high):
    rows = []
    for q in range(low, high + 1):
        word = witness(q)
        d = data(word)
        assert d["minimal"] and d["ss"] == q and d["tail"] == max(0, q - 1), (q, d)
        assert d["mass"] == 1 and d["moment"] == 0
        rows.append(dict(q=q, **d))
    return rows


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("phase", choices=["discovery", "holdout"])
    args = parser.parse_args()
    out = dict(protocol="H-20261001-01", phase=args.phase,
               source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    if args.phase == "discovery":
        out["crosscheck"] = small_crosscheck()
        out["negative_controls"] = {w: data(w) for w in ["AASASSA", "ASSA", "A"]}
        out["census"] = [census(n) for n in [3, 7, 11, 15, 19]]
        out["sharp_witnesses"] = witnesses(0, 10)
    else:
        out["census"] = [census(23)]
        out["sharp_witnesses"] = witnesses(11, 40)
    print(json.dumps(out, ensure_ascii=False, sort_keys=True, indent=2))
    assert all(row["counts"][key] == 0 for row in out["census"] for key in
               ["weak_bound_violations", "strict_bound_violations", "prefix_lemma_violations"])


if __name__ == "__main__":
    main()
