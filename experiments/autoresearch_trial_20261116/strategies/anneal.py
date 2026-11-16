"""Baseline strategy: simulated annealing on hplus (+ small h term), random restarts."""
import math


def search(n, evaluate, budget, rng):
    restarts = 10
    per = budget // restarts
    for _ in range(restarts):
        w = "".join(rng.choice("AS") for _ in range(n))
        cur = evaluate(w)["hplus"]
        for it in range(per - 1):
            T = 2.0 * (0.02 / 2.0) ** (it / max(1, per - 2))
            i = rng.randrange(n)
            if rng.random() < 0.7:
                v = w[:i] + ("S" if w[i] == "A" else "A") + w[i + 1:]
            else:
                j = rng.randrange(n)
                lst = list(w)
                lst[i], lst[j] = lst[j], lst[i]
                v = "".join(lst)
            sv = evaluate(v)["hplus"]
            if sv >= cur or rng.random() < math.exp((sv - cur) / T):
                w, cur = v, sv
    return []
