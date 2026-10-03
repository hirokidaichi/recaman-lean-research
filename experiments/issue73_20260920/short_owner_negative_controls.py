#!/usr/bin/env python3
"""Fixed discovery p=1..12: attack the short donor theorem's hypotheses.

Find first examples after dropping ONLY donor SS=2, donor minimality, or
short-subset tightness; retain current A phases, period positivity, genuine
least supply windows and donor exclusion from B. These are not counterexamples
to the full theorem. Do not use the p32/33 holdout.
"""
import json
from short_owner_future import supply, subsets, neighbors


def word_at(cycle, u, d):
    return "".join(cycle[(u - k) % len(cycle)] for k in range(1, d + 1))


def p2(w):
    a = [1 if b == "A" else -1 for b in w]
    return sum(a) == 1 and sum(k * s for k, s in enumerate(a, 1)) == 0


def run():
    found = {}
    examined = 0
    for p in range(1, 13):
        for bits in range(1 << p):
            if bits.bit_count() * 2 <= p:
                continue
            examined += 1
            cycle = "".join("A" if bits >> u & 1 else "S" for u in range(p))
            data = supply(cycle)
            short = {u: rec for u, rec in data.items() if rec[0] <= 11}
            for u0, c in enumerate(cycle):
                if c != "A":
                    continue
                w = word_at(cycle, u0, 11)
                if not p2(w):
                    continue
                ss = w.count("SS")  # Replace below: overlapping pairs must be counted.
                ss = sum(w[i:i + 2] == "SS" for i in range(10))
                minimal = all(not p2(w[:d]) for d in range(1, 11))
                sstar = (u0 - max(k for k, b in enumerate(w, 1) if b == "S")) % p
                for B in subsets([u for u in short if u != u0]):
                    if not B:
                        continue
                    N = neighbors(short, B)
                    if sstar not in N:
                        continue
                    tight = len(N) == len(B)
                    mode = ("drop_ss2" if minimal and ss != 2 and tight else
                            "drop_donor_minimality" if not minimal and ss == 2 and tight else
                            "drop_tightness" if minimal and ss == 2 and not tight else None)
                    if mode and mode not in found:
                        out = dict(kind=mode, period=p, word=cycle, donor=u0,
                                   donor_window=w, donor_ss=ss, donor_minimal=minimal,
                                   donor_oldest_phase=sstar, B=B, N=sorted(N), tight=tight,
                                   B_lags=[short[b][0] for b in B],
                                   B_windows=[short[b][1] for b in B])
                        # Direct witness verification, from the string rather than cache.
                        assert cycle[u0] == "A" and u0 not in B and p2(w)
                        for b in B:
                            d = short[b][0]
                            bw = word_at(cycle, b, d)
                            assert cycle[b] == "A" and d in (3, 7, 11) and p2(bw)
                            assert all(not p2(bw[:f]) for f in range(1, d))
                        assert sstar in N
                        found[mode] = out
                        print(json.dumps(out), flush=True)
            if len(found) == 3:
                print(json.dumps({"status": "ALL_THREE_CONTROLS_FOUND", "examined_words": examined,
                                  "last_period": p, "range_exhausted": False}), flush=True)
                return
    print(json.dumps({"status": "FINITE_SEARCH_COMPLETE", "examined_words": examined,
                      "found": sorted(found), "range": [1, 12]}), flush=True)


if __name__ == "__main__":
    run()
