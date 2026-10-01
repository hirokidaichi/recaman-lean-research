#!/usr/bin/env python3
"""Bit-level probe: can two minimal P2 windows (line model, no periodicity) share their oldest S?
Convention: word w = [bit at offset 1 (newest), ..., offset L (oldest)], True=A, False=S.
Window of addition u: offsets k=1..L sit at clocks u-k.  oldestOffset(w) = max k with w[k-1]=S.
Two windows v (u_v, w_v) and v' (u_v', w_v') share oldest S iff u_v - oo(w_v) = u_v' - oo(w_v').
WLOG u_v < u_v'.  Consistency: every clock in both windows has the same bit, and clock u_v (an A) if inside v' window must be A."""
from itertools import product
from functools import lru_cache
def mass(w): return sum(1 if b else -1 for b in w)
def moment(w): return sum((i+1)*(1 if b else -1) for i,b in enumerate(w))
def p2(w): return mass(w)==1 and moment(w)==0
def minimal(w): return p2(w) and not any(p2(w[:d]) for d in range(1,len(w)))
@lru_cache(None)
def minimal_words(L): return [w for w in product([True,False],repeat=L) if minimal(w)]
def s(w): return ''.join('A' if b else 'S' for b in w)
def oo(w): return max(i for i,b in enumerate(w) if not b)+1
import sys
LMAX=int(sys.argv[1]) if len(sys.argv)>1 else 15
words=[w for L in range(3,LMAX+1,4) for w in minimal_words(L)]
print("words per lag:", {L:len(minimal_words(L)) for L in range(3,LMAX+1,4)})
def bits_of(u,w):
    d={u:True}
    for i,b in enumerate(w): d[u-(i+1)]=b
    return d
found=0; pairs=0
for wl in words:                # longer-or-equal window v' at clock 0
    s_ = -oo(wl)                # shared oldest S clock
    bl=bits_of(0,wl)
    for ws in words:
        uv = s_ + oo(ws)        # u_v so that oldest S of ws lands on s_
        if uv >= 0: continue    # WLOG u_v < u_v'
        bs=bits_of(uv,ws)
        ok=all(bl[c]==b for c,b in bs.items() if c in bl)
        pairs+=1
        if ok:
            found+=1
            print(f"CONSISTENT: long {s(wl)} (lag {len(wl)}, oo {oo(wl)}) at 0; short {s(ws)} (lag {len(ws)}, oo {oo(ws)}) at u={uv}")
print(f"pairs checked {pairs}, consistent {found}")
