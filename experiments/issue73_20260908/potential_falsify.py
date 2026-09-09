#!/usr/bin/env python3
"""Falsify at most one closed-form F, with one permitted repair.

F is a function of the bit window only (newest = LSB), independent of L as a
rule. Validity is the edge inequality, not equality with the least potential.
"""
from __future__ import annotations

import gzip
import hashlib
import json
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SRC = ROOT / "docs/data/issue73_20260907"

LEAN7_P2 = {55, 63, 95, 111, 119, 127}
LEAN7_P1 = {
    7, 15, 23, 31, 39, 47, 59, 61, 62, 71, 79, 87, 91, 93, 94, 103, 110, 123, 125, 126
}


def lean7(mask7: int) -> int:
    m = mask7 & 127
    if m in LEAN7_P2:
        return 2
    if m in LEAN7_P1:
        return 1
    return 0


def load_potential(L: int) -> list[int]:
    gz = SRC / f"automaton_L{L}_potential.txt.gz"
    raw = gzip.decompress(gz.read_bytes()).decode()
    vals = [int(line) for line in raw.splitlines() if line != ""]
    assert len(vals) == 1 << L
    return vals


def is_supplied(mask: int, horizon: int) -> bool:
    for d in range(3, horizon + 1, 4):
        bits = mask & ((1 << d) - 1)
        if bits.bit_count() != (d + 1) // 2:
            continue
        moment = 0
        b = bits
        while b:
            low = b & -b
            moment += low.bit_length()
            b -= low
        if moment == d * (d + 1) // 4:
            return True
    return False


def p2_lags(mask: int, horizon: int) -> list[int]:
    hits = []
    for d in range(1, horizon + 1):
        s = m = 0
        for i in range(d):
            e = 1 if (mask >> i) & 1 else -1
            s += e
            m += (i + 1) * e
        if s == 1 and m == 0:
            hits.append(d)
    return hits


def bitstring(mask: int, L: int) -> str:
    return "".join("A" if (mask >> i) & 1 else "S" for i in range(L))


def newest(mask: int, n: int) -> int:
    return mask & ((1 << n) - 1)


def F_embed7(mask: int, L: int) -> int:
    """Proposal: Lean L=7 potential of the newest 7 bits, pad oldest with S."""
    if L >= 7:
        return lean7(newest(mask, 7))
    padded = mask  # oldest already 0 = S
    return lean7(padded)


def h_sparse(mask: int, L: int) -> int:
    """Max h such that newest (4h-1) bits have AAA prefix and S-set in the
    L=7 P=2 family on each 4-block, allowing a trailing old S-cluster.

    Precise: h=0 always allowed.
    h>=1 requires newest 3 bits A.
    For h>=2, newest 7 bits in Lean P=2 set.
    For h>=3, newest 11 bits match one of the empirically listed L=11 max
    shapes OR all-A-like: newest 3=A, newest 7 in P=2, and S-positions in
    8..11 are unconstrained except we require no S in 1..3.
    This second part is the repair attempt; first pass uses only h<=2 via embed7.
    """
    bits = [(mask >> i) & 1 for i in range(L)]
    if L < 3 or bits[0] + bits[1] + bits[2] < 3:
        # precursor / leading S handled separately
        return 0
    h = 1
    if L >= 7 and lean7(newest(mask, 7)) == 2:
        h = 2
    if L >= 11 and h == 2:
        # repair extra: +1 if newest 11 has no S in 1..3 and at most one S in 4..7
        # already implied by lean7==2, plus the older 4 bits arbitrary?
        # That would give F=3 on ALL extensions of P=2 7-bit windows — likely invalid.
        # Tighter: older 4 bits have all S's in a suffix cluster, or at most one live S.
        older = bits[7:11] if L >= 11 else []
        s_live = [i for i, b in enumerate(older, start=8) if b == 0]
        # allow any older 4 bits: we will see if inequalities survive
        h = 3
    if L >= 15 and h == 3:
        h = 4
    if L >= 19 and h == 4:
        h = 4  # plateau; do not add a 5th
    return h


def F_leadingS_h(mask: int, L: int) -> int:
    """F = max(0, h(z) - k) with k leading newest S and z the rest, h from
    AAA/Lean7 stacking. For k>=1, h is computed on the shifted window
    (newest bits dropped), using the same rule as if those bits were the window.
    """
    k = 0
    m = mask
    ell = L
    while ell > 0 and (m & 1) == 0:
        k += 1
        m >>= 1
        ell -= 1
    if ell == 0:
        return 0
    return max(0, h_sparse(m, ell) - k)


def check_formula(name, F, L, sample_limit=None):
    bound = (1 << L) - 1
    size = 1 << L
    sup = [is_supplied(m, L) for m in range(size)]
    vals = [F(m, L) for m in range(size)]
    n_fail_S = n_fail_A = 0
    examples = []
    P = load_potential(L) if L in (3, 7, 11, 15, 19) else None
    eq = 0
    for u in range(size):
        if P is not None and vals[u] == P[u]:
            eq += 1
        # S edge
        vS = (u << 1) & bound
        if vals[u] - 1 > vals[vS]:
            n_fail_S += 1
            if len(examples) < 12:
                examples.append(
                    {
                        "edge": "S",
                        "from": bitstring(u, L),
                        "to": bitstring(vS, L),
                        "Ffrom": vals[u],
                        "Fto": vals[vS],
                        "charge": -1,
                    }
                )
        # A edge
        vA = ((u << 1) | 1) & bound
        ch = 1 if sup[u] else 0
        if vals[u] + ch > vals[vA]:
            n_fail_A += 1
            if len(examples) < 12:
                examples.append(
                    {
                        "edge": "A",
                        "from": bitstring(u, L),
                        "to": bitstring(vA, L),
                        "Ffrom": vals[u],
                        "Fto": vals[vA],
                        "charge": ch,
                        "supplied": bool(sup[u]),
                        "lags": p2_lags(u, L) if sup[u] else [],
                    }
                )
    out = {
        "name": name,
        "L": L,
        "fail_S": n_fail_S,
        "fail_A": n_fail_A,
        "equal_least_P": eq if P is not None else None,
        "states": size,
        "F_counts": {str(i): vals.count(i) for i in range(min(vals), max(vals) + 1)},
        "examples": examples,
    }
    print("FALSIFY=" + json.dumps(out, sort_keys=True), flush=True)
    return n_fail_S + n_fail_A, examples


def F_embed7_plus_long(mask: int, L: int) -> int:
    """Repair: embed7 plus +1 if L>=11 and newest 11 bits have newest 3=A
    and newest 7 in the P=2 set. (Uniform rule: look at newest 11 when present.)
    """
    base = F_embed7(mask, L)
    if L < 11:
        return base
    m11 = newest(mask, 11)
    bits_ok = (m11 & 7) == 7 and lean7(newest(m11, 7)) == 2
    return base + (1 if bits_ok else 0)


def F_embed7_plus_long_leadS(mask: int, L: int) -> int:
    """Repair variant: allow one leading S to decrement the 11-bit boost."""
    if L < 11:
        return F_embed7(mask, L)
    k = 0
    m = mask
    ell = L
    # only strip at most 1 S for the boost; embed7 already handles 7-bit S
    base = F_embed7(mask, L)
    if (mask & 1) == 0:
        m11 = newest(mask >> 1, 11) if L >= 12 else newest(mask >> 1, L - 1)
        if L - 1 >= 11 and (m11 & 7) == 7 and lean7(newest(m11, 7)) == 2:
            return max(base, 3 - 1)
        return base
    m11 = newest(mask, 11)
    if (m11 & 7) == 7 and lean7(newest(m11, 7)) == 2:
        return max(base, 3)
    return base


def main() -> None:
    print("protocol=H-20260908-02 formula falsify", flush=True)
    print(
        "source_revision="
        + subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip(),
        flush=True,
    )
    print(
        "script_sha256="
        + hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        flush=True,
    )
    print("PROPOSAL=F_embed7 Lean7 potential of newest 7 bits, pad oldest S", flush=True)

    fails = {}
    for L in (3, 7, 11):
        n, _ = check_formula("F_embed7", F_embed7, L)
        fails[L] = n

    print("PROPOSAL_RESULT=" + json.dumps(fails), flush=True)

    # One repair, only if L=11 failed (expected)
    print("REPAIR=F_embed7_plus_long newest11 AAA and Lean7==2 adds +1", flush=True)
    fails2 = {}
    for L in (3, 7, 11):
        n, _ = check_formula("F_embed7_plus_long", F_embed7_plus_long, L)
        fails2[L] = n
    print("REPAIR_RESULT=" + json.dumps(fails2), flush=True)

    print("REPAIR_VARIANT=F_embed7_plus_long_leadS", flush=True)
    fails3 = {}
    for L in (3, 7, 11):
        n, _ = check_formula("F_embed7_plus_long_leadS", F_embed7_plus_long_leadS, L)
        fails3[L] = n
    print("REPAIR_VARIANT_RESULT=" + json.dumps(fails3), flush=True)

    # Sample L=11 high-P states vs F
    P11 = load_potential(11)
    print("SAMPLE_L11_maxP:")
    for m in range(1 << 11):
        if P11[m] == 3:
            print(
                bitstring(m, 11),
                "P",
                P11[m],
                "embed7",
                F_embed7(m, 11),
                "repair",
                F_embed7_plus_long(m, 11),
                "lags",
                p2_lags(m, 11),
            )


if __name__ == "__main__":
    main()
