"""Search strategy evolved by OpenEvolve (seed = the anneal baseline).

Task: find a word w over {A,S} of length n (n = 34) with hplus(w) = e + u - s >= 1,
where e = endable A clocks, s = #S, u = endables whose shortest window is unclean.
Such words exist (found by exhaustive search); the baselines never find one.

Definitions (F[i] = height before step i, A = +1, S = -1):
  * A clock b is endable if some t < b with b - t = 3 (mod 4) has
    F[b] = F[t] + 1 and sum_{v=t+1..b} (F[v] - F[t]) = 0 (mass 1, moment 0).
  * Its shortest window (largest such t) is unclean if some u with t < u < b has
    F[u] = F[t] and sum_{v=t+1..u} (F[v] - F[t]) >= 0.

`evaluate(word)` returns dict(e, s, u, hplus, h, longwin32) and costs one unit of
budget; exceeding the budget raises an exception that ends the search (fine).
"""
import math


# EVOLVE-BLOCK-START
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
# EVOLVE-BLOCK-END
