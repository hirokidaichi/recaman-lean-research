#!/usr/bin/env python3
"""Min P2 SS=2 starting S: which SS-gaps survive?"""
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


def p2(w: list[bool]) -> bool:
    return mass(w) == 1 and moment(w) == 0


def ss_count(w: list[bool]) -> int:
    return sum(1 for i in range(len(w) - 1) if (not w[i]) and (not w[i + 1]))


def no_saas(w: list[bool]) -> bool:
    return not any(
        (not w[i]) and w[i + 1] and w[i + 2] and (not w[i + 3])
        for i in range(len(w) - 3)
    )


def ss_gap(w: list[bool]) -> int | None:
    idxs = [i for i in range(len(w) - 1) if (not w[i]) and (not w[i + 1])]
    if len(idxs) < 2:
        return None
    return idxs[1] - idxs[0]


def is_min(w: list[bool]) -> bool:
    # newest-first prefixes = initial segments
    for k in range(1, len(w)):
        if p2(w[:k]):
            return False
    return True


def main() -> None:
    print("protocol=H-20260910-39 min SS=2 P2 a=0 SS-gaps")
    print("example_SAAAASSASSA", "p2", p2([S,A,A,A,A,S,S,A,S,S,A]),
          "min", is_min([S,A,A,A,A,S,S,A,S,S,A]),
          "ss", ss_count([S,A,A,A,A,S,S,A,S,S,A]),
          "gap", ss_gap([S,A,A,A,A,S,S,A,S,S,A]))
    counts = {g: 0 for g in range(0, 8)}
    ge8 = 0
    total = 0
    min_total = 0
    hits = {g: [] for g in (2, 3, 4, 6, 7)}
    for n in range(5, 24, 2):
        rest = n - 1
        for mask in range(1 << rest):
            w = [S] + [bool((mask >> i) & 1) for i in range(rest)]
            if ss_count(w) != 2 or not p2(w):
                continue
            total += 1
            if not is_min(w):
                continue
            min_total += 1
            g = ss_gap(w)
            if g is None:
                continue
            if g >= 8:
                ge8 += 1
            elif 0 <= g < 8:
                counts[g] += 1
            if g in hits and no_saas(w) and len(hits[g]) < 5:
                hits[g].append("".join("A" if b else "S" for b in w))
    print(f"p2={total} min_p2={min_total} len<=23")
    print("MIN_GAPS", counts, "ge8", ge8)
    print("MIN_NOSAAS_FORBIDDEN", hits)
    print("DONE")


if __name__ == "__main__":
    main()
