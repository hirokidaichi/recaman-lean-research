"""Control strategy: uniform random words (lower bound for any search method)."""


def search(n, evaluate, budget, rng):
    while True:
        evaluate("".join(rng.choice("AS") for _ in range(n)))
