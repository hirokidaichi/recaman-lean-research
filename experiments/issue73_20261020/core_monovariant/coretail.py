"""Minimal-counterexample search with NO bound on window lengths.
Structure (paper): in a minimal counterexample M (every proper sub-closure is a disjoint union of AAS / w1-triples),
E(x+1)>=1; let z* = first z>x with E(z)=0.  Core = clocks [x, z*-1] (E>=1 on (x,z*)), arbitrary.
Tail = clocks >= z*: by E-split + IH a sequential walk of free A / AAS block / triple block; old windows (open at z*,
all owned) must close at distinct non-member A clocks of the tail.
We enumerate all cores of length <= C (open windows <= K, starts per clock <= KS) and decide tail feasibility exactly
(lag-uniform: boundary G strictly increases by 1/2/4; a window with boundary G>=4 can never close)."""
import sys
from functools import lru_cache
C=int(sys.argv[1]); K=int(sys.argv[2]); KS=int(sys.argv[3]) if len(sys.argv)>3 else 2
BLOCKS={'AAS':('SAA',set()),'TRI':('SSAAAASAA',{4,7})}
@lru_cache(None)
def tail(ws):
    """ws: sorted tuple of (G,Psi) of open old windows at a macro boundary (before reading the clock). True if all can close."""
    if not ws: return True
    if max(g for g,p in ws)>=4: return False
    # option free A: subsets: at most one window with (1,0) closes here
    res=False
    for letters,mem,trail in [('A',set(),False)]+[(l,m,True) for l,m in BLOCKS.values()]:
        if walk(ws,letters,frozenset(mem),trail): return True
    return False
def walk(ws,letters,mem,trail):
    # explore letter by letter, branching on which window (if any) closes at an eligible A
    states={tuple(sorted(ws))}
    for i,ch in enumerate(letters):
        nxt=set()
        for st in states:
            opts=[st]
            if ch=='A' and i not in mem:
                for j,(g,p) in enumerate(st):
                    if g==1 and p==0: opts.append(st[:j]+st[j+1:])
            s=1 if ch=='A' else -1
            for o in opts:
                nxt.add(tuple(sorted((g+s,p+g+s) for g,p in o)))
        states=nxt
    if trail:  # member A of the block: no old window may close
        states={tuple(sorted((g+1,p+g+1) for g,p in st)) for st in states}
    return any(tail(st) for st in states)
def E(st): return sum(1 for w in st if w[3]==0)
def closable(w): return w[1]==1 and w[2]==0 and w[3]==1 and w[0]>=3
def core_steps(st):
    ws=list(st); out=[]
    copts=[None]+[i for i,w in enumerate(ws) if closable(w) and (i==0 or ws[i-1]!=w)]
    for c in copts:
        base=[w for j,w in enumerate(ws) if j!=c]
        for k in range(0, min(KS,K-len(base))+1):
            cur=base+[(0,0,0,0)]*k
            if not cur: continue
            for sg in (['A'] if c is not None else ['A','S']):
                if sg=='A': opts=[cur]; s=1
                else:
                    s=-1; opts=[]; seen=set()
                    for i,w in enumerate(cur):
                        if w[3]==0 and w not in seen:
                            seen.add(w); nw=list(cur); nw[i]=w[:3]+(1,); opts.append(nw)
                for o in opts:
                    out.append(tuple(sorted((a+1,d+s,p+d+s,ow) for a,d,p,ow in o)))
    return out
# start: clock x starts k>=1 windows
layer=set()
for t in core_steps(()):
    if E(t)>=1: layer.add(t)
found=[]; total=0
for depth in range(1,C+1):
    total+=len(layer)
    nl=set()
    for st in layer:
        for t in core_steps(st):
            if E(t)==0:
                ws=tuple(sorted((d,p) for a,d,p,o in t))
                if tail(ws): found.append((depth+1,t))
            else: nl.add(t)
    print('core length',depth+1,'E>=1 states',len(nl),'feasible tails so far',len(found),flush=True)
    layer=nl
for f in found[:20]: print('FOUND',f)
