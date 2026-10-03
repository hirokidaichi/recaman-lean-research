#!/usr/bin/env python3
"""Finite semantic controls for H-20260920-03; this is not a proof."""

import hashlib
import itertools
import json


def window(cycle, u, lag):
    return "".join(cycle[(u - k) % len(cycle)] for k in range(1, lag + 1))


def p2(word):
    signs = [1 if bit == "A" else -1 for bit in word]
    return sum(signs) == 1 and sum(k * sign for k, sign in enumerate(signs, 1)) == 0


def nhood(cycle, assignments):
    p = len(cycle)
    return sorted({(u - k) % p for u, lag in assignments
                   for k, bit in enumerate(window(cycle, u, lag), 1) if bit == "S"})


def record(cycle, u, m, lag):
    return dict(period=len(cycle), cycle=cycle, B=[u], m=m, lag=lag,
                prefix=window(cycle, u, m), full=window(cycle, u, lag),
                N_m=nhood(cycle, [(u, m)]), N_lag=nhood(cycle, [(u, lag)]),
                full_P2=p2(window(cycle, u, lag)))


def main():
    counts = dict(cycles=0, source_strict_tight=0, card_tight_identity=0,
                  card_strict_tight_singleton=0, card_strict_nontight_singleton=0)
    examples = {}
    for p in range(1, 13):
        for bits in itertools.product("AS", repeat=p):
            cycle = "".join(bits)
            counts["cycles"] += 1
            for u, bit in enumerate(cycle):
                if bit != "A":
                    continue
                for m in range(1, 12):
                    if not p2(window(cycle, u, m)):
                        continue
                    nm = nhood(cycle, [(u, m)])
                    for lag in range(m, 12):
                        nl = nhood(cycle, [(u, lag)])
                        if lag > m and len(nl) == 1 and nm == nl:
                            counts["source_strict_tight"] += 1
                            examples.setdefault("source_strict_tight", record(cycle, u, m, lag))
                        if not p2(window(cycle, u, lag)):
                            continue
                        least = all(not p2(window(cycle, u, k)) for k in range(1, m))
                        if not least:
                            continue
                        if lag == m and len(nl) == 1:
                            counts["card_tight_identity"] += 1
                            examples.setdefault("card_tight_identity", record(cycle, u, m, lag))
                        if lag > m and len(nl) == 1:
                            counts["card_strict_tight_singleton"] += 1
                            assert nm == nl
                            examples.setdefault("card_strict_tight_singleton", record(cycle, u, m, lag))
                        if lag > m and nm != nl and len(nl) != 1:
                            counts["card_strict_nontight_singleton"] += 1
                            examples.setdefault("card_strict_nontight_singleton", record(cycle, u, m, lag))
    assert counts["source_strict_tight"] > 0
    assert counts["card_tight_identity"] > 0
    assert counts["card_strict_nontight_singleton"] > 0
    assert counts["card_strict_tight_singleton"] == 0
    print(json.dumps(dict(kind="singleton_scan", range="p=1..12", counts=counts,
                          examples=examples), sort_keys=True))

    exact = record("AASSSAAAASSSS", 7, 3, 3)
    assert exact["prefix"] == "AAS" and exact["N_m"] == exact["N_lag"] == [4]
    weakened = record("ASAAASASS", 4, 3, 7)
    assert weakened["full_P2"] and weakened["prefix"] == "AAS"
    assert weakened["N_m"] != weakened["N_lag"]
    print(json.dumps(dict(kind="fixed_controls", exact_tight_identity=exact,
                          strict_nontight=weakened), sort_keys=True))


if __name__ == "__main__":
    main()
