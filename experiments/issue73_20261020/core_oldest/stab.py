#!/usr/bin/env python3
"""Generalized closures: windows with mass 1, L = 4m+3, moment in [-B,B]. Records (sumE, P=sum mom+, N=sum mom-).
usage: genc.py NMAX LMAX KMAX B"""
import sys
from functools import lru_cache
NMAX=int(sys.argv[1]); LMAX=int(sys.argv[2]); KMAX=int(sys.argv[3]); B=int(sys.argv[4])
@lru_cache(None)
def addrange(d,r):
    if r==0: return (0,0) if d==1 else None
    if abs(d-1)>r or (r-abs(d-1))%2: return None
    lo=hi=None
    for s in (1,-1):
        sub=addrange(d+s,r-1)
        if sub is None: continue
        a,b=sub[0]+d+s,sub[1]+d+s
        lo=a if lo is None else min(lo,a); hi=b if hi is None else max(hi,b)
    return (lo,hi)
@lru_cache(None)
def viable(age,d,psi):
    for r in range(0,LMAX-age+1):
        L=age+r
        if L<3 or L%4!=3: continue
        rg=addrange(d,r)
        if rg is None: continue
        if psi+rg[0]<=B and psi+rg[1]>=-B: return True
    return False

import collections
cnt=collections.Counter(); ex={}
def check(s_,m):
    st=collections.defaultdict(list)
    for b,t,o,mo in m: st[t].append(mo)
    V=0
    for z in range(len(s_)-1):
        j=len(st[z])-(1 if s_[z]=='S' else 0)
        if j>0: V+=j
    P=sum(mo for *_,mo in m if mo>0); N=-sum(mo for *_,mo in m if mo<0)
    ok=2*V<=P+N
    cnt[ok]+=1
    if 2*V==P+N and V>0: cnt['tight']+=1
    if not ok:
        print('FAIL',s_,sorted(m),flush=True)

def dfs(z,sig,opn,mem):
    closes=[None]+[i for i,w in enumerate(opn) if w[1]==1 and abs(w[2])<=B and w[3] is not None and (z-w[0])%4==3]
    for c in closes:
        base=[w for j,w in enumerate(opn) if j!=c]
        nm=mem+([(z,opn[c][0],opn[c][3],opn[c][2])] if c is not None else [])
        for k in range(0,KMAX-len(base)+1):
            cur=[list(w) for w in base]+[[z,0,0,None] for _ in range(k)]
            if not cur:
                if c is not None: check(sig+'A',nm)
                continue
            if z==NMAX: continue
            for sg in (['A'] if c is not None else ['A','S']):
                if sg=='A': opts=[cur]
                else:
                    opts=[];seen=set()
                    for i,w in enumerate(cur):
                        if w[3] is None and w[0] not in seen:
                            seen.add(w[0]); nw=[list(v) for v in cur]; nw[i][3]=z; opts.append(nw)
                s=1 if sg=='A' else -1
                for o in opts:
                    ok=True;nxt=[]
                    for (t,d,psi,ow) in o:
                        nd=d+s; age=z+1-t
                        if age>LMAX or not viable(age,nd,psi+nd): ok=False;break
                        nxt.append([t,nd,psi+nd,ow])
                    if ok: dfs(z+1,sig+sg,nxt,nm)
dfs(0,'',[],[])
print(sys.argv[1:],dict(cnt))
