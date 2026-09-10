#!/usr/bin/env python3
"""Falsifier for H-20260910-38: equality family a = ssCount+2 is never P2."""
from __future__ import annotations

A, S = True, False


def mass(w: list[bool]) -> int:
    return sum(1 if b else -1 for b in w)


def moment(w: list[bool]) -> int:
    def rec(xs: list[bool]) -> int:
        if not xs:
            return 0
        b, *rest = xs
        return (1 if b else -1) + mass(rest) + rec(rest)

    return rec(w)


def ss_count(w: list[bool]) -> int:
    return sum(1 for i in range(len(w) - 1) if (not w[i]) and (not w[i + 1]))


def eq_gaps(ps: list[int]) -> list[int]:
    if not ps:
        return [0]
    p, *rest = ps
    if not rest:
        return [1] * p + [0]
    return [1] * p + [0] + eq_gaps(rest)


def gap_word(a: int, gs: list[int]) -> list[bool]:
    if not gs:
        return [A] * a
    g, *rest = gs
    return [A] * a + [S] + gap_word(g, rest)


def predicted_twice_moment(ps: list[int]) -> int:
    m = len(ps)
    total = -2 * (m * m - 1)
    for j, p in enumerate(ps):
        total -= (4 * (m - j) - 2) * p
    return total


def main() -> None:
    print("protocol=H-20260910-38 equality family a=ssCount+2")
    hits = 0
    formula_fail = 0
    checked = 0
    # discovery n=1..8 i.e. m=2..9 one-groups, each p_j ≤ 4
    for m in range(2, 10):
        n = m - 1
        a = n + 2
        # all-zero
        ps0 = [0] * m
        w0 = gap_word(a, eq_gaps(ps0))
        tw0 = 2 * moment(w0)
        pred0 = predicted_twice_moment(ps0)
        checked += 1
        print(
            f"allzero n={n} a={a} len={len(w0)} mass={mass(w0)} "
            f"ss={ss_count(w0)} 2M={tw0} pred={pred0}"
        )
        if tw0 != pred0:
            formula_fail += 1
            print("FORMULA_FAIL", ps0)
        if mass(w0) == 1 and moment(w0) == 0:
            hits += 1
            print("HIT", ps0)
        # bounded ones
        limit = 3 if m <= 6 else 2
        from itertools import product

        for ps in product(range(limit + 1), repeat=m):
            ps = list(ps)
            if ps == ps0:
                continue
            w = gap_word(a, eq_gaps(ps))
            tw = 2 * moment(w)
            pred = predicted_twice_moment(ps)
            checked += 1
            if tw != pred:
                formula_fail += 1
                print("FORMULA_FAIL", ps, tw, pred)
                if formula_fail >= 5:
                    print("TOO_MANY_FORMULA_FAIL")
                    return
            if mass(w) == 1 and moment(w) == 0:
                hits += 1
                print("HIT", ps)
    print(f"checked={checked} formula_fail={formula_fail} p2_hits={hits}")
    print("DONE")


if __name__ == "__main__":
    main()
