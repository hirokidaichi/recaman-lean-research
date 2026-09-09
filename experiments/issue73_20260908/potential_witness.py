#!/usr/bin/env python3
"""Canonical witnesses and formula candidates for H-20260908-02.

Uses frozen L=3,7,11 (and max-F on 15,19). Does not touch L=23.
"""
from __future__ import annotations

import gzip
from collections import deque
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SRC = ROOT / "docs/data/issue73_20260907"


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


def s_pos(mask: int, L: int) -> tuple[int, ...]:
    return tuple(i + 1 for i in range(L) if ((mask >> i) & 1) == 0)


def future_allA(mask: int, L: int, steps: int | None = None) -> list[int]:
    if steps is None:
        steps = L
    bound = (1 << L) - 1
    hits = []
    s = mask
    for j in range(steps):
        if is_supplied(s, L):
            hits.append(j + 1)
        s = ((s << 1) | 1) & bound
    return hits


def relax_with_parent(L: int):
    size = 1 << L
    bound = size - 1
    sup = [is_supplied(m, L) for m in range(size)]
    P = [0] * size
    parent = [-1] * size
    via = [-1] * size
    q = deque(range(size))
    queued = bytearray([1]) * size
    while q:
        u = q.popleft()
        queued[u] = 0
        for bit in (0, 1):
            w = sup[u] if bit else -1
            v = ((u << 1) | bit) & bound
            cand = P[u] + w
            if cand <= P[v]:
                continue
            P[v] = cand
            parent[v] = u
            via[v] = bit
            if not queued[v]:
                queued[v] = 1
                q.append(v)
    return P, parent, via, sup


def trace(v, parent, via, L, max_steps=40):
    bits = []
    seen = set()
    x = v
    for _ in range(max_steps):
        if parent[x] < 0 or x in seen:
            break
        seen.add(x)
        bits.append(via[x])
        x = parent[x]
    bits.reverse()
    return x, "".join("A" if b else "S" for b in bits)


def replay(start, word, L, sup):
    bound = (1 << L) - 1
    s = start
    h = 0
    events = []
    for ch in word:
        bit = 1 if ch == "A" else 0
        w = sup[s] if bit else -1
        lags = p2_lags(s, L) if (bit and sup[s]) else []
        h += w
        s = ((s << 1) | bit) & bound
        events.append({"bit": ch, "w": w, "h": h, "to": bitstring(s, L), "lags": lags})
    return events


def candidate_F_seed_harvest(mask: int, L: int) -> int:
    """Proposed-but-not-yet-frozen: max all-A harvest from any left-rotation
    of the S-pattern with P-style clipping ignored; NOT used as F yet.
    """
    return len(future_allA(mask, L))


def try_formula_min_s_gap(mask: int, L: int) -> int:
    """F = number of S-positions in a chain with gap>=3 from newest AAA run.

    More precisely: if newest 3 bits are not AAA, drop to a suffix analysis.
    """
    # Walk newest to oldest, score completed SAAA-like harvests with clipping.
    # We'll instead compute a simple function and test exact match.
    r = 0
    while r < L and (mask >> r) & 1:
        r += 1
    # r = newest A-run. S at r+1 if r<L.
    # Count how many S's lie at positions >=4 and can be ordered with min gap 3
    spos = [i + 1 for i in range(L) if ((mask >> i) & 1) == 0]
    # greedy pack S's from the newest, requiring pos>=4 and gap>=3
    packed = 0
    last = -999
    for p in spos:
        if p < 4:
            continue
        if last < 0 or p - last >= 3:
            packed += 1
            last = p
    # newest AAA gives a base of 1 if r>=3, plus packed S's that each enable extra?
    base = 1 if r >= 3 else 0
    # if newest is S, potential may still be >0
    return base  # placeholder


def formula_completed_contacts(mask: int, L: int) -> int:
    """F1 (to be tested): height of the newest A-run measured in leftover
    loop-closing blocks of length 4, plus 1 if a lag-3 seed is present
    after accounting for S's inside the run.

    Explicitly:
      Let bits be newest-first.
      Scan from newest. Maintain 'credit' = 0.
      This is NOT the history charge; it is a local parse.
    Disabled: we test a precise parse below.
    """
    bits = [(mask >> i) & 1 for i in range(L)]
    # Parse from OLDEST to NEWEST using only lags that lie inside the
    # scanned prefix, starting from empty. Clip at 0. This equals replay
    # from zero and already failed.
    return 0


def formula_F1(mask: int, L: int) -> int:
    """F1: max k such that the newest (4k-1) bits (if 4k-1<=L) contain
    at most k-1 S-symbols, all at positions >=4, and the newest 3 bits
    are A, OR k=0.

    For k=1: newest 3 = AAA, 0 S in those 3.  (4*1-1=3)
    For k=2: newest 7 bits have ≤1 S, all S at >=4, newest 3=A.
             But AAASAAS has 2 S and P=2, so this already fails unless
             we allow 2 S when they are at 4 and 7.
    """
    bits = [(mask >> i) & 1 for i in range(L)]
    maxk = 0
    k = 0
    while True:
        k += 1
        need = 4 * k - 1
        if need > L:
            break
        w = bits[:need]
        if w[0] != 1 or (need >= 2 and w[1] != 1) or (need >= 3 and w[2] != 1):
            break
        spos = [i + 1 for i, b in enumerate(w) if b == 0]
        if any(p < 4 for p in spos):
            break
        if len(spos) > k:  # too many S
            # allow exactly the 'SAAS' extra at the block boundary?
            # not in F1
            break
        maxk = k
    return maxk


def formula_F1b(mask: int, L: int) -> int:
    """Repair-shaped: allow up to k S's in newest 4k-1, all positions >=4,
    and min gap between S's of 3 except S's in the oldest 3 bits of the
    window (a trailing S-cluster is free).
    """
    bits = [(mask >> i) & 1 for i in range(L)]
    maxk = 0
    k = 0
    while True:
        k += 1
        need = 4 * k - 1
        if need > L:
            break
        w = bits[:need]
        if len(w) < 3 or w[0] != 1 or w[1] != 1 or w[2] != 1:
            break
        spos = [i + 1 for i, b in enumerate(w) if b == 0]
        if any(p < 4 for p in spos):
            break
        # S's not in the oldest 3 of this prefix must have min gap 3
        cutoff = need - 3
        live = [p for p in spos if p <= cutoff]
        ok = True
        for a, b in zip(live, live[1:]):
            if b - a < 3:
                ok = False
                break
        if not ok:
            break
        maxk = k
    return maxk


def main() -> None:
    for L in (3, 7, 11):
        P, parent, via, sup = relax_with_parent(L)
        saved = load_potential(L)
        assert P == saved, (L, sum(i != j for i, j in zip(P, saved)))
        mx = max(P)
        print(f"===== L={L} maxP={mx} supplied={sum(sup)} =====")
        # max future harvest
        futs = [len(future_allA(m, L)) for m in range(1 << L)]
        print(f"maxF={max(futs)} P+F constant? {len({P[m]+futs[m] for m in range(1<<L)})} values {sorted({P[m]+futs[m] for m in range(1<<L)})[:8]}")
        # supplied table
        print("supplied states:")
        for m in range(1 << L):
            if not sup[m]:
                continue
            succA = ((m << 1) | 1) & ((1 << L) - 1)
            print(
                f"  {bitstring(m,L)} P={P[m]} lags={p2_lags(m,L)} S={s_pos(m,L)} "
                f"->A {bitstring(succA,L)} P={P[succA]} fut={len(future_allA(m,L))}"
            )
        print("canonical witnesses for maxP:")
        for m in range(1 << L):
            if P[m] != mx:
                continue
            start, word = trace(m, parent, via, L)
            ev = replay(start, word, L, sup)
            supplied_steps = [e for e in ev if e["w"] == 1]
            print(
                f"  {bitstring(m,L)} start={bitstring(start,L)} Pstart={P[start]} "
                f"word={word} n_sup={len(supplied_steps)} events={supplied_steps}"
            )
        # test F1 / F1b
        miss1 = miss1b = 0
        samples = []
        for m in range(1 << L):
            a = formula_F1(m, L)
            b = formula_F1b(m, L)
            if a != P[m]:
                miss1 += 1
                if len(samples) < 8:
                    samples.append(("F1", bitstring(m, L), P[m], a, s_pos(m, L)))
            if b != P[m]:
                miss1b += 1
        print(f"F1 mismatches={miss1}/{1<<L} F1b mismatches={miss1b}/{1<<L} samples={samples}")

        # P vs newest-A-run and first S
        print("P by (arun, firstS, #S):")
        from collections import Counter
        c = Counter()
        for m in range(1 << L):
            r = 0
            while r < L and (m >> r) & 1:
                r += 1
            firstS = r + 1 if r < L else None
            c[(P[m], r, firstS, bin(m).count("0") and s_pos(m, L).__len__())] += 1
        # too many, print only for L<=7
        if L <= 7:
            for key in sorted(c):
                print(f"  {key}: {c[key]}")

    for L in (15, 19):
        P = load_potential(L)
        fmax = 0
        arg = 0
        # computing F for all 2^19 is OK
        for m in range(1 << L):
            n = len(future_allA(m, L))
            if n > fmax:
                fmax = n
                arg = m
        print(f"L={L} maxP={max(P)} P_allA={P[(1<<L)-1]} maxF={fmax} argF={bitstring(arg,L)}")


if __name__ == "__main__":
    main()
