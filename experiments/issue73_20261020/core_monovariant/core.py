"""Generic automaton core (same semantics as auto.py) with optional window marks.
window = (age, d, psi, owned, mark)."""
import sys
from functools import lru_cache
LMAX=11; KMAX=4
def setb(l,k):
    global LMAX,KMAX
    LMAX=l; KMAX=k; viable.cache_clear()
@lru_cache(None)
def addrange(d, r):
    if r == 0:
        return (0, 0) if d == 1 else None
    if abs(d - 1) > r or (r - abs(d - 1)) % 2:
        return None
    lo, hi = None, None
    for s in (1, -1):
        sub = addrange(d + s, r - 1)
        if sub is None: continue
        a, b = sub[0] + d + s, sub[1] + d + s
        lo = a if lo is None else min(lo, a)
        hi = b if hi is None else max(hi, b)
    return (lo, hi)
@lru_cache(None)
def viable(age,d,psi,owned):
    r_max = LMAX - age
    for r in range(0, r_max + 1):
        if age + r < 3: continue
        rg = addrange(d, r)
        if rg is None: continue
        if psi + rg[0] <= 0 <= psi + rg[1]:
            if r==0 and not owned: continue
            return True
    return False
def closable(w): return w[1]==1 and w[2]==0 and w[3]==1 and w[0]>=3
def step(state):
    """yields (next_state or 'END', info) ; info=(closed_window or None, k, sigma, owner_window or None)"""
    ws=list(state); out=[]
    copts=[None]+[i for i,w in enumerate(ws) if closable(w) and (i==0 or ws[i-1]!=w)]
    for c in copts:
        base=[w for j,w in enumerate(ws) if j!=c]
        cw = ws[c] if c is not None else None
        for k in range(0, KMAX-len(base)+1):
            cur=base+[(0,0,0,0,0)]*k
            if not cur:
                if c is not None: out.append(('END',(cw,0,'A',None)))
                continue
            for sg in (['A'] if c is not None else ['A','S']):
                if sg=='A': opts=[(tuple(cur),None)]; s=1
                else:
                    s=-1; opts=[]; seen=set()
                    for i,w in enumerate(cur):
                        if w[3]==0 and w not in seen:
                            seen.add(w); nw=list(cur); nw[i]=w[:3]+(1,)+w[4:]; opts.append((tuple(nw),w))
                for o,ow in opts:
                    nxt=[]; ok=True
                    for (age,d,psi,owned,mk) in o:
                        nd=d+s; nw=(age+1,nd,psi+nd,owned,mk)
                        if nw[0]>LMAX or not viable(*nw[:4]): ok=False; break
                        nxt.append(nw)
                    if ok: out.append((tuple(sorted(nxt)),(cw,k,sg,ow)))
    return out
def E(s): return sum(1 for w in s if w[3]==0)
