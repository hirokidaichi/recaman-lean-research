"""Domain-informed baseline: local search over token sequences.

Tokens are the EqClass blocks (SAAA, SSAAAASAAA, A) plus short defects that create
depth >= 2 excursions (where unclean windows live, E-511).  This is the kind of
skeleton a FunSearch/OpenEvolve prompt would start from; it measures how much a
human prior helps compared with letter-level annealing.
"""
import math

TOKENS = ["SAAA", "SSAAAASAAA", "A", "S", "SS", "SSS", "SSSS", "AAAA", "SA", "AS"]


def render(seq, n):
    w = "".join(TOKENS[i] for i in seq)
    if len(w) < n:
        w = w + "A" * (n - len(w))
    return w[:n]


def search(n, evaluate, budget, rng):
    restarts = 20
    per = budget // restarts
    for _ in range(restarts):
        seq = [rng.randrange(len(TOKENS)) for _ in range(n // 3)]
        cur = evaluate(render(seq, n))["hplus"]
        for it in range(per - 1):
            T = 1.5 * (0.02 / 1.5) ** (it / max(1, per - 2))
            new = list(seq)
            r = rng.random()
            i = rng.randrange(len(new))
            if r < 0.5:
                new[i] = rng.randrange(len(TOKENS))
            elif r < 0.75 and len(new) > 2:
                del new[i]
            else:
                new.insert(i, rng.randrange(len(TOKENS)))
            sv = evaluate(render(new, n))["hplus"]
            if sv >= cur or rng.random() < math.exp((sv - cur) / T):
                seq, cur = new, sv
    return []
