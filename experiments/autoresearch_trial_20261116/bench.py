"""Fixed-budget benchmark for falsifier search strategies (autoresearch / OpenEvolve style).

A strategy is a Python file defining

    def search(n: int, evaluate, budget: int, rng: random.Random) -> list[str]

`evaluate(word)` returns dict(e, s, u, hplus, h) where
    e     = endable A clocks with window inside word,
    s     = number of S,
    u     = endables whose shortest window is unclean (E-511),
    hplus = e + u - s   (H+ margin on the whole word; H+ is REFUTED at length 34),
    h     = max over subwords of (e - s)  (H margin; >= 1 would refute H, E-509),
    longwin32 = endables whose shortest window has length >= 32 (needed by any
            H violation, because E-372 settles windows of length <= 31).
Each call costs one unit of `budget`; calls beyond the budget raise BudgetExceeded.

Tasks (deterministic, hardware independent):
  rediscover : n = 34, metric = best hplus found (known answer: >= 1 exists,
               E-511 found it by exhaustive search; H+ holds for n <= 32).
  hunt       : n in {40, 64}, metric = lexicographic (best h, longwin32) (h >= 1
               would be a candidate counterexample to H; rechecked independently).

Output is OBSERVED evidence about search strategies, never evidence about H.
Usage: python3 bench.py strategies/anneal.py --budget 200000 --seeds 3
"""
from __future__ import annotations

import argparse
import importlib.util
import json
import random
import sys
import time
from pathlib import Path

from hmargin import endable, longwin, margin, naive_margin, unclean


class BudgetExceeded(Exception):
    pass


class Evaluator:
    def __init__(self, budget: int):
        self.budget = budget
        self.calls = 0
        self.best_hplus = (-10**9, "")
        self.best_h = (-10**9, "")
        self.first_hplus_hit = None
        # graded signals (the headline metrics are flat at 0 for every baseline)
        self.max_u_at = {0: 0, -1: 0}       # max unclean count among words with hplus >= 0 / >= -1
        self.best_hunt = ((-10**9, -1), "")  # lexicographic (h, longwin32)

    def __call__(self, word: str) -> dict:
        if self.calls >= self.budget:
            raise BudgetExceeded
        if not word or set(word) - {"A", "S"}:
            raise ValueError("word must be a non-empty string over {A,S}")
        self.calls += 1
        e, s, u = endable(word), word.count("S"), unclean(word)
        h = margin(word)[0]
        hp = e + u - s
        if hp > self.best_hplus[0]:
            self.best_hplus = (hp, word)
        if hp >= 1 and self.first_hplus_hit is None:
            self.first_hplus_hit = self.calls
        if h > self.best_h[0]:
            self.best_h = (h, word)
        for lvl in (0, -1):
            if hp >= lvl and u > self.max_u_at[lvl]:
                self.max_u_at[lvl] = u
        lw = longwin(word, 32) if len(word) >= 35 else 0
        if (h, lw) > self.best_hunt[0]:
            self.best_hunt = ((h, lw), word)
        return dict(e=e, s=s, u=u, hplus=hp, h=h, longwin32=lw)


def load(path: str):
    spec = importlib.util.spec_from_file_location("strategy", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def run_task(mod, n: int, budget: int, seed: int) -> dict:
    ev = Evaluator(budget)
    t0 = time.time()
    try:
        mod.search(n, ev, budget, random.Random(seed))
    except BudgetExceeded:
        pass
    out = dict(n=n, seed=seed, calls=ev.calls, seconds=round(time.time() - t0, 2),
               best_hplus=ev.best_hplus[0], best_hplus_word=ev.best_hplus[1],
               first_hplus_hit=ev.first_hplus_hit,
               best_h=ev.best_h[0], best_h_word=ev.best_h[1],
               max_u_at_hplus0=ev.max_u_at[0], max_u_at_hplus_m1=ev.max_u_at[-1],
               best_hunt=list(ev.best_hunt[0]), best_hunt_word=ev.best_hunt[1])
    if ev.best_h[0] >= 1:  # independent recheck of an H candidate
        w = ev.best_h[1]
        out["h_recheck_naive"] = naive_margin(w) if len(w) <= 80 else "too long for naive"
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("strategy")
    ap.add_argument("--budget", type=int, default=200000)
    ap.add_argument("--seeds", type=int, default=3)
    ap.add_argument("--tasks", nargs="+", default=["rediscover", "hunt"])
    args = ap.parse_args()
    mod = load(args.strategy)
    rows = []
    for task in args.tasks:
        sizes = [34] if task == "rediscover" else [40, 64]
        for n in sizes:
            for seed in range(args.seeds):
                r = dict(task=task, strategy=Path(args.strategy).name, **run_task(mod, n, args.budget, seed))
                rows.append(r)
                print(json.dumps(r), flush=True)
    red = [r for r in rows if r["task"] == "rediscover"]
    if red:
        hits = sum(r["best_hplus"] >= 1 for r in red)
        print(f"# rediscover: {hits}/{len(red)} seeds found an H+ violation; "
              f"best hplus per seed = {[r['best_hplus'] for r in red]}", file=sys.stderr)
    hunt = [r for r in rows if r["task"] == "hunt"]
    if hunt:
        print(f"# hunt: best H margin per run = {[r['best_h'] for r in hunt]} (>=1 would need recheck)",
              file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
