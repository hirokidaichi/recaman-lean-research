#!/usr/bin/env python3
"""Relaxed closure search: enumerate ALL closed configurations (own bijective onto covered S's)
rooted at a max-lag member v at clock 0, over a word set, and report the sink-free ones.
wordset: min = minimal P2 words; p2 = all P2 words (member may choose any P2 window).
usage: relax.py WORDSET Lmax memberCap [nodeCap]"""
import sys
from itertools import product
sys.setrecursionlimit(100000)
def mass(w): return sum(1 if b else -1 for b in w)
def moment(w): return sum((i+1)*(1 if b else -1) for i,b in enumerate(w))
def p2(w): return mass(w)==1 and moment(w)==0
def minimal(w): return p2(w) and not any(p2(w[:d]) for d in range(1,len(w)))
def s(w): return ''.join('A' if b else 'S' for b in w)
def soff(w): return [i+1 for i,b in enumerate(w) if not b]
WS=sys.argv[1]; Lmax=int(sys.argv[2]); cap=int(sys.argv[3]); nodeCap=int(sys.argv[4]) if len(sys.argv)>4 else 10**7
def ok(w):
    if all(w): return False
    if WS=='min': return minimal(w)
    if WS=='p2': return p2(w)
    if WS=='aneg': return mass(w)==1 and moment(w)<=0
    if WS=='apos': return mass(w)==1 and moment(w)>=0
    if WS=='aneg_min':  # mass1, moment<=0, no proper prefix with mass1 and moment<=0
        return mass(w)==1 and moment(w)<=0 and not any(mass(w[:d])==1 and moment(w[:d])<=0 for d in range(1,len(w)))
    if WS=='apos_min':
        return mass(w)==1 and moment(w)>=0 and not any(mass(w[:d])==1 and moment(w[:d])>=0 for d in range(1,len(w)))
STEP=4 if (WS in ('min','p2') or '--step4' in sys.argv) else 2
WORDS=[w for L in range(3,Lmax+1,STEP) for w in product([True,False],repeat=L) if ok(w)]
PL=[(w,k) for w in WORDS for k in soff(w)]
found=[]; nodes=0; capped=0; allc=[]
def rec(bits,members,owned,need):
    global nodes,capped
    nodes+=1
    if nodes>nodeCap: return
    if not need:
        # closed: compute multiplicities
        mult={}
        for u,w in members.items():
            for k in soff(w): mult[u-k]=mult.get(u-k,0)+1
        allc.append(dict(members))
        if all(m>=2 for m in mult.values()):
            found.append(dict(members))
        return
    if len(members)>=cap: capped+=1; return
    # MRV
    best=None
    for sc in need:
        opts=[]
        for w,k in PL:
            u=sc+k
            if u in members or bits.get(u,True) is not True: continue
            ok=True
            for i,b in enumerate(w):
                c=u-i-1
                if bits.get(c,b)!=b: ok=False; break
            if ok: opts.append((w,k))
        if best is None or len(opts)<len(best[1]): best=(sc,opts)
        if not opts: return
    sc,opts=best
    rest=[c for c in need if c!=sc]
    for w,k in opts:
        u=sc+k
        b2=dict(bits); b2[u]=True
        for i,b in enumerate(w): b2[u-i-1]=b
        m2=dict(members); m2[u]=w
        o2=dict(owned); o2[sc]=u
        nn=[u-kk for kk in soff(w) if (u-kk) not in o2 and (u-kk) not in rest]
        rec(b2,m2,o2,rest+nn)
Vs=[w for w in WORDS if len(w)==Lmax]
for v in Vs:
    for k0 in soff(v):
        bits={0:True}
        for i,b in enumerate(v): bits[-i-1]=b
        rec(bits,{0:v},{-k0:0},[-k for k in soff(v) if k!=k0])
print("wordset",WS,"Lmax",Lmax,"nodes",nodes,"capped",capped,"closures",len(allc),'sink-free closures found',len(found))
seen=set()
for f in (allc if "--all" in sys.argv else found):
    key=tuple(sorted((u-min(f),s(w)) for u,w in f.items()))
    if key in seen: continue
    seen.add(key)
    print(len(f), ' '.join(f'{u}:{w}' for u,w in key))
    if len(seen)>30: break
