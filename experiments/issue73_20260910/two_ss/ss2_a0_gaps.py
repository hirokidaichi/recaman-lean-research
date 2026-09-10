#!/usr/bin/env python3
"""Falsifier: can an abstract SS=2 P2 word starting S have SS-gap in {2,3,4,6,7}?"""
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


def no_saas(w: list[bool]) -> bool:
    for i in range(len(w) - 3):
        if (not w[i]) and w[i + 1] and w[i + 2] and (not w[i + 3]):
            return False
    return True


def ss_gap(w: list[bool]) -> int | None:
    idxs = [i for i in range(len(w) - 1) if (not w[i]) and (not w[i + 1])]
    if len(idxs) < 2:
        return None
    return idxs[1] - idxs[0]


def main() -> None:
    print("protocol=H-20260910-39 abstract SS=2 P2 a=0 SS-gaps")
    counts = {g: 0 for g in range(0, 8)}
    ge8 = 0
    hits = {g: [] for g in (2, 3, 4, 6, 7)}
    nosaas_hits = {g: [] for g in (2, 3, 4, 6, 7)}
    total = 0
    for n in range(5, 20, 2):
        rest = n - 1
        for mask in range(1 << rest):
            w = [S] + [bool((mask >> i) & 1) for i in range(rest)]
            if ss_count(w) != 2:
                continue
            if mass(w) != 1 or moment(w) != 0:
                continue
            total += 1
            g = ss_gap(w)
            if g is None:
                continue
            if g >= 8:
                ge8 += 1
            elif g < 8:
                counts[g] += 1
            if g in hits and len(hits[g]) < 3:
                hits[g].append("".join("A" if b else "S" for b in w))
            if g in nosaas_hits and no_saas(w) and len(nosaas_hits[g]) < 3:
                nosaas_hits[g].append("".join("A" if b else "S" for b in w))
    print(f"p2_ss2_a0_len<=19={total}")
    print("GAPS", counts, "ge8", ge8)
    print("FORBIDDEN_EXAMPLES", {g: hits[g] for g in hits})
    print("FORBIDDEN_NOSAAS", {g: nosaas_hits[g] for g in nosaas_hits})
    print("DONE")


if __name__ == "__main__":
    main()
