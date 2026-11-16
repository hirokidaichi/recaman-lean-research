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
    cache = {}

    def f(x):
        r = cache.get(x)
        if r is None:
            d = evaluate(x)
            r = 2.0 * d["hplus"] + d["u"] + 0.05 * d["e"]
            cache[x] = r
        return r

    restarts = 40
    per = budget // restarts
    for _ in range(restarts):
        pa = rng.choice((0.35, 0.5, 0.6, 0.7))
        w = "".join("A" if rng.random() < pa else "S" for _ in range(n))
        cur = f(w)
        for it in range(per - 1):
            T = 1.5 * (0.15 / 1.5) ** (it / max(1, per - 2))
            r = rng.random()
            i = rng.randrange(n)
            if r < 0.5:
                v = w[:i] + ("S" if w[i] == "A" else "A") + w[i + 1:]
            elif r < 0.75:
                j = rng.randrange(n)
                lst = list(w)
                lst[i], lst[j] = lst[j], lst[i]
                v = "".join(lst)
            elif r < 0.9:
                j = rng.randrange(n)
                a, b = min(i, j), max(i, j) + 1
                v = w[:a] + w[a:b][::-1] + w[b:]
            else:
                j = rng.randrange(n)
                c = w[i]
                t = w[:i] + w[i + 1:]
                v = t[:j] + c + t[j:]
            sv = f(v)
            if sv >= cur or rng.random() < math.exp((sv - cur) / T):
                w, cur = v, sv
    return []
# EVOLVE-BLOCK-END
