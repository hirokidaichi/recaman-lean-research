"""Non-LLM baseline falsifier for the H conjecture (E-509): simulated annealing.

Objective (to maximize), designed because max_{p<k}(e-s) is flat at 0:
    score(w) = (e(w) - s(w)) + LAMBDA * u + 0.05 * tight(w) / len(w)^2   (LAMBDA = 0.5)
where e counts endable A clocks with window inside w, s counts S in w, and u
counts endables whose shortest window is unclean (E-511: an H counterexample
needs unclean endables, and H+ = "e + u <= s" already fails at length 34).
Trading one unit of slack for two unclean endables pushes the search into the
unclean region where the Clean Window proof of H does not apply.
H forbids e - s >= 1 on every subword, so a word with score >= 1 is a candidate
counterexample, which is then re-checked by margin() and the naive reference.

Usage: python3 local_search.py --len 40 --iters 200000 --seed 1
Output: OBSERVED only (a finite heuristic search is never evidence that H holds).
"""
from __future__ import annotations

import argparse
import json
import math
import random
import time

from hmargin import endable, margin, naive_margin, unclean


LAMBDA = 0.5


def score(w: str) -> float:
    m, _, _, tight = margin(w)
    if m >= 1:
        return 1000.0 + m
    u = unclean(w)
    return (endable(w) - w.count("S")) + LAMBDA * u + 0.05 * tight / len(w) ** 2


def mutate(w: str, rng: random.Random) -> str:
    n = len(w)
    r = rng.random()
    if r < 0.6:  # flip one letter
        i = rng.randrange(n)
        return w[:i] + ("S" if w[i] == "A" else "A") + w[i + 1:]
    if r < 0.8:  # swap two letters
        i, j = rng.randrange(n), rng.randrange(n)
        lst = list(w)
        lst[i], lst[j] = lst[j], lst[i]
        return "".join(lst)
    # replace a random segment with a known equality block (keeps length)
    block = rng.choice(["SAAA", "SSAAAASAAA", "A", "AAS", "SSA"])
    i = rng.randrange(n)
    return (w[:i] + block + w[i:])[:n]


def anneal(n: int, iters: int, seed: int, t0: float = 1.0, t1: float = 0.01) -> dict:
    rng = random.Random(seed)
    w = "".join(rng.choice("AS") for _ in range(n))
    cur = score(w)
    best, best_w = cur, w
    found = []
    start = time.time()
    for it in range(iters):
        T = t0 * (t1 / t0) ** (it / max(1, iters - 1))
        v = mutate(w, rng)
        sv = score(v)
        if sv >= cur or rng.random() < math.exp((sv - cur) / T):
            w, cur = v, sv
            if cur > best:
                best, best_w = cur, w
            if cur >= 1000:
                found.append(w)
                break
    out = dict(n=n, iters=iters, seed=seed, best_score=round(best, 4), best_word=best_w,
               lam=LAMBDA, best_e_minus_s=endable(best_w) - best_w.count("S"),
               best_unclean=unclean(best_w),
               seconds=round(time.time() - start, 2), candidates=found)
    for c in found:  # independent recheck of any candidate
        out.setdefault("recheck", []).append(dict(word=c, margin=margin(c)[0],
                                                  naive=naive_margin(c) if len(c) <= 60 else None))
    return out


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--len", type=int, nargs="+", default=[40])
    ap.add_argument("--iters", type=int, default=100000)
    ap.add_argument("--seeds", type=int, default=3)
    ap.add_argument("--lam", type=float, default=0.5,
                    help="weight of unclean endables; 1.0 makes score the H+ margin e+u-s")
    args = ap.parse_args()
    global LAMBDA
    LAMBDA = args.lam
    for n in args.len:
        for s in range(args.seeds):
            print(json.dumps(anneal(n, args.iters, s)), flush=True)


if __name__ == "__main__":
    main()
