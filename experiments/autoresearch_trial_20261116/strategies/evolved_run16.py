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
    calls = 0

    def ev(w):
        nonlocal calls
        calls += 1
        r = evaluate(w)
        # u を先に伸ばす目的関数(平坦面 hplus=0 に勾配を作る)
        h = r["hplus"]
        bonus = 0.0
        if h >= 0:
            bonus += 1.0  # 採点対象の領域(hplus>=0)に入る段差
        if h >= 1:
            bonus += 3.0  # 解は強く固定する
        return h + bonus + 0.5 * r["u"] + 0.05 * r["e"]

    def flip(w, i):
        return w[:i] + ("S" if w[i] == "A" else "A") + w[i + 1:]

    while calls < budget - 60:
        pS = rng.uniform(0.15, 0.6)
        w = "".join("S" if rng.random() < pS else "A" for _ in range(n))
        cur = ev(w)
        best_loc = cur
        stale = 0
        tabu = {}
        for it in range(400):
            if calls >= budget - 60 or stale > 60:
                break
            cands = [(flip(w, i), i) for i in range(n)]
            for _ in range(8):
                i = rng.randrange(n)
                j = rng.randrange(n)
                if w[i] != w[j]:
                    lst = list(w)
                    lst[i], lst[j] = lst[j], lst[i]
                    cands.append(("".join(lst), i if rng.random() < 0.5 else j))
            bv, bs, bi = None, -1e9, 0
            for v, i in cands:
                if calls >= budget - 1:
                    return []
                sv = ev(v)
                if tabu.get(i, -1) > it:
                    continue
                sv += rng.random() * 1e-3
                if sv > bs:
                    bv, bs, bi = v, sv, i
            if bv is None:
                break
            w, cur = bv, bs
            tabu[bi] = it + rng.randint(4, 10)
            if cur > best_loc + 1e-2:
                best_loc = cur
                stale = 0
            else:
                stale += 1
    return []
# EVOLVE-BLOCK-END
