#!/usr/bin/env python3
"""Lag-uniform search for the E>0 core of a minimal counterexample (all window lengths).
Structure (proved in report): minimal counterexample M = core windows (t_b < z*) + Suf_{z*} (a union of
AAS / w1-triples laid out as blocks, possibly empty, separated by free A's). Core [x, z*-1] has exactly k S's,
k core windows, E>0 on (x, z*), E(z*)=0. Core windows ending inside the core are exact P2; windows open at z*
must all close over the block sequence (joint macro search; boundary G>=4 => never closes).
usage: core.py KMAXS [REL]   REL in eq|le|ge (area relation used for closing)"""
import sys
from functools import lru_cache
K=int(sys.argv[1]); REL=sys.argv[2] if len(sys.argv)>2 else 'eq'
OK={'eq':lambda p:p==0,'le':lambda p:p<=0,'ge':lambda p:p>=0}[REL]
BLOCKS={'AAS':('SAA',set()),'TRI':('SSAAAASAA',{4,7})}

@lru_cache(None)
def joint(ws):
    """ws: sorted tuple of (G,Psi) at a block boundary (clock about to be read). True iff all can close."""
    if not ws: return True
    if any(g>=4 for g,p in ws): return False
    # option: next clock is a free A (possibly hosting one closing window)
    def adv(lst,s):
        return [(g+s,p+g+s) for g,p in lst]
    cands=[]
    # free A
    for c in [None]+[i for i,(g,p) in enumerate(ws) if g==1 and OK(p)]:
        rest=[w for i,w in enumerate(ws) if i!=c]
        cands.append(('A',tuple(sorted(adv(rest,1)))))
    for c in cands:
        if c[1]!=ws and joint(c[1]): return True
        if c[1]==ws and not ws: return True
    # blocks
    for name,(letters,mem) in BLOCKS.items():
        if block(ws,letters,frozenset(mem)): return True
    return False

def block(ws,letters,mem):
    # DFS through block letters with optional closes at non-member A's, then member A (no close), then boundary
    def rec(i,lst):
        if i==len(letters):
            nl=tuple(sorted((g+1,p+g+1) for g,p in lst))  # member clock: A, nobody of ours closes
            return joint(nl)
        ch=letters[i]
        opts=[None]
        if ch=='A' and i not in mem:
            opts+= [j for j,(g,p) in enumerate(lst) if g==1 and OK(p)]
        s=1 if ch=='A' else -1
        for c in opts:
            rest=[w for j,w in enumerate(lst) if j!=c]
            if rec(i+1,[(g+s,p+g+s) for g,p in rest]): return True
        return False
    return rec(0,list(ws))

found=[]; nodes=[0]
def dfs(z,sig,opn,nS,mem,started):
    """process clock z. opn: list of [t,d,psi,owned]. E(z)=#unowned (must be >0 for z>x)."""
    nodes[0]+=1
    r=K-nS
    closes=[None]+[i for i,w in enumerate(opn) if w[1]==1 and OK(w[2]) and w[3] and (z-w[0])>=3 and (z-w[0])%4==3]
    for c in closes:
        base=[list(w) for j,w in enumerate(opn) if j!=c]
        nm=mem+([(z,opn[c][0])] if c is not None else [])
        # new starts at z
        for k in range(0, (K - len(nm) - len(base)) + 1):
            if z==0 and k==0: continue
            cur=base+[[z,0,0,False] for _ in range(k)]
            if not cur:
                continue  # E would be 0 with nothing open: handled below at E==0 detection
            for sg in (['A'] if c is not None else ['A','S']):
                if sg=='S' and nS>=K: continue
                if sg=='A': opts=[cur]
                else:
                    opts=[];seen=set()
                    for i,w in enumerate(cur):
                        if not w[3] and w[0] not in seen:
                            seen.add(w[0]); nw=[list(v) for v in cur]; nw[i][3]=True; opts.append(nw)
                s=1 if sg=='A' else -1
                nS2=nS+(sg=='S'); r2=K-nS2
                for o in opts:
                    nxt=[[t,d+s,p+d+s,ow] for t,d,p,ow in o]
                    if any(d>3+r2 for t,d,p,ow in nxt): continue
                    E=sum(1 for w in nxt if not w[3])
                    sig2=sig+sg
                    if E==0 and z==0: continue
                    if E==0:
                        # core ends at z*=z+1 ; need #core windows == nS2 (automatic by matching) 
                        nwin=len(nm)+len(nxt)
                        if nwin!=nS2: continue
                        ws=tuple(sorted((d,p) for t,d,p,ow in nxt))
                        if joint(ws): found.append((sig2,nm,[(t,d,p) for t,d,p,ow in nxt]))
                        continue
                    dfs(z+1,sig2,nxt,nS2,nm,started+k)
dfs(0,'',[],0,[],0)
print('K',K,'REL',REL,'nodes',nodes[0],'cores found',len(found))
for f in found[:15]: print(f)
