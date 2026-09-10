#!/usr/bin/env python3
"""Falsifier for H-20260910-37: P2 + ssCount=2 + leading AAAA, NoSAAS not assumed."""
from __future__ import annotations

A, S = True, False


def mass(w: list[bool]) -> int:
    return sum(1 if b else -1 for b in w)


def moment(w: list[bool]) -> int:
    m = 0
    acc = 0
    for i, b in enumerate(w):
        sign = 1 if b else -1
        rest = w[i + 1 :]
        acc = sign + mass(rest) + (0 if i == len(w) - 1 else 0)
        # Lean: moment (b::w) = sign b + mass w + moment w
    def rec(xs: list[bool]) -> int:
        if not xs:
            return 0
        b, *rest = xs
        return (1 if b else -1) + mass(rest) + rec(rest)

    return rec(w)


def ss_count(w: list[bool]) -> int:
    return sum(1 for i in range(len(w) - 1) if (not w[i]) and (not w[i + 1]))


def p2(w: list[bool]) -> bool:
    return mass(w) == 1 and moment(w) == 0


def leading_run(w: list[bool]) -> int:
    n = 0
    for b in w:
        if b:
            n += 1
        else:
            break
    return n


def enumerate_hits(max_len: int) -> list[list[bool]]:
    hits: list[list[bool]] = []
    # P2 mass=1 forces odd length.
    for n in range(7, max_len + 1, 4):  # length ≡ 3 (mod 4) is the a4 family; also try ≡1
        pass
    for n in range(7, max_len + 1, 2):
        rest_bits = n - 4
        for mask in range(1 << rest_bits):
            rest = [bool((mask >> i) & 1) for i in range(rest_bits)]
            w = [A, A, A, A] + rest
            if w[4] is A:
                continue  # leading run would be >4; still counted below via k≥4
            if ss_count(w) != 2:
                continue
            if p2(w):
                hits.append(w)
    return hits


def enumerate_leading_ge4(max_len: int) -> list[tuple[int, list[bool]]]:
    hits = []
    for n in range(7, max_len + 1, 2):
        # first bit of rest may be A (leading >4) or S
        rest_bits = n - 4
        for mask in range(1 << rest_bits):
            rest = [bool((mask >> i) & 1) for i in range(rest_bits)]
            w = [A, A, A, A] + rest
            if leading_run(w) < 4:
                continue
            if ss_count(w) != 2:
                continue
            if p2(w):
                hits.append((leading_run(w), w))
    return hits


def a4_word(p: int, q: int, r: int) -> list[bool]:
    # gapWord 4 (p ones, 0, q ones, 0, r ones, 0)
    def gap_word(a: int, gs: list[int]) -> list[bool]:
        if not gs:
            return [A] * a
        g, *rest = gs
        return [A] * a + [S] + gap_word(g, rest)

    gs = [1] * p + [0] + [1] * q + [0] + [1] * r + [0]
    return gap_word(4, gs)


def main() -> None:
    print("protocol=H-20260910-37 SS=2 P2 leading>=4 without NoSAAS")
    # Boundary: AAAASSS
    w0 = [A, A, A, A, S, S, S]
    print(f"AAAASSS mass={mass(w0)} moment={moment(w0)} ss={ss_count(w0)} p2={p2(w0)}")
    # SAAS example gapWord 4 [2,0] = AAAASAAS? gapWord 4 [2,0] = AAAA S AA S
    w_saas = [A, A, A, A, S, A, A, S]
    print(
        f"AAAASAAS mass={mass(w_saas)} moment={moment(w_saas)} "
        f"ss={ss_count(w_saas)} p2={p2(w_saas)}"
    )
    fam_p2 = 0
    for p in range(0, 21):
        for q in range(0, 21 - p):
            for r in range(0, 21 - p - q):
                w = a4_word(p, q, r)
                if p2(w):
                    fam_p2 += 1
                    print("FAMILY_HIT", p, q, r, w)
    print(f"a4_family_p2_hits_pqr<=20={fam_p2}")
    disc = enumerate_leading_ge4(15)
    print(f"discovery_len<=15_hits={len(disc)}")
    if disc:
        print("DISC_HIT", disc[0])
    hold = enumerate_leading_ge4(19)
    print(f"holdout_len<=19_hits={len(hold)}")
    if hold:
        print("HOLD_HIT", hold[0][0], "".join("A" if b else "S" for b in hold[0][1]))
    print("DONE")


if __name__ == "__main__":
    main()
