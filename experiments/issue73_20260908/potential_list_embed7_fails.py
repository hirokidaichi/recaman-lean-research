#!/usr/bin/env python3
"""List every L=11 F_embed7 A-edge failure (proposal counter-windows)."""
from pathlib import Path
import gzip

SRC = Path(__file__).resolve().parents[2] / "docs/data/issue73_20260907"
LEAN7_P2 = {55, 63, 95, 111, 119, 127}
LEAN7_P1 = {7, 15, 23, 31, 39, 47, 59, 61, 62, 71, 79, 87, 91, 93, 94, 103, 110, 123, 125, 126}


def lean7(m):
    m &= 127
    if m in LEAN7_P2:
        return 2
    if m in LEAN7_P1:
        return 1
    return 0


def bits(m, L):
    return "".join("A" if (m >> i) & 1 else "S" for i in range(L))


def supplied_lags(mask, L):
    hits = []
    for d in range(1, L + 1):
        s = mo = 0
        for i in range(d):
            e = 1 if (mask >> i) & 1 else -1
            s += e
            mo += (i + 1) * e
        if s == 1 and mo == 0:
            hits.append(d)
    return hits


P = [int(x) for x in gzip.decompress((SRC / "automaton_L11_potential.txt.gz").read_bytes()).decode().split() if x]
L = 11
bound = (1 << L) - 1
print("embed7_A_failures_L11")
n = 0
for u in range(1 << L):
    lags = supplied_lags(u, L)
    if not lags:
        continue
    v = ((u << 1) | 1) & bound
    Fu, Fv = lean7(u), lean7(v)
    if Fu + 1 > Fv:
        n += 1
        print(f"{n:2d} {bits(u,L)} --A--> {bits(v,L)} F {Fu}->{Fv} P {P[u]}->{P[v]} lags={lags} newest7={bits(u,7)}")
print("total", n)
