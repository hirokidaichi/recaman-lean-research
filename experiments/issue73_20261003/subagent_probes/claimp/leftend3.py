#!/usr/bin/env python3
"""Left-end local search.  Clock 0 = oldest S of a component (all clocks < 0 are A, WLOG).
Members: words from WORDSET (min | p2) of lag <= Lmax, windows must have all clocks < 0 equal to A.
Require: mult(0) >= 2 (two member windows contain clock 0) and every S in [0,H] that lies in some
member window is owned (own injective, each member owns <= 1 S; members may own S > H later).
If no such partial configuration exists, 'the oldest S is a sink' holds with horizon H for lags <= Lmax.
usage: leftend.py WORDSET Lmax H [nodeCap] [--show]"""
import sys
from itertools import product
sys.setrecursionlimit(100000)
def mass(w): return sum(1 if b else -1 for b in w)
def moment(w): return sum((i+1)*(1 if b else -1) for i,b in enumerate(w))
def p2(w): return mass(w)==1 and moment(w)==0
def minimal(w): return p2(w) and not any(p2(w[:d]) for d in range(1,len(w)))
def s(w): return ''.join('A' if b else 'S' for b in w)
def soff(w): return [i+1 for i,b in enumerate(w) if not b]
def gen(L,WS):
    out=[]; w=[False]*L
    def rec(d,m,mu):
        r=L-d
        if r==0:
            if m==1 and mu==0: out.append(tuple(w))
            return
        if WS=='min' and d>0 and m==1 and mu==0: return
        # feasibility
        for b in (True,False):
            m2=m+(1 if b else -1); mu2=mu+(d+1)*(1 if b else -1)
            r2=r-1; twoa=1-m2+r2
            if twoa<0 or twoa%2 or twoa>2*r2: continue
            a=twoa//2; pos=list(range(d+2,L+1)); tot=sum(pos)
            mn=2*sum(pos[:a])-tot; mx=2*sum(pos[r2-a:])-tot
            if not (mn<=-mu2<=mx): continue
            w[d]=b; rec(d+1,m2,mu2)
    rec(0,0,0); return out
WS=sys.argv[1]; Lmax=int(sys.argv[2]); H=int(sys.argv[3])
nodeCap=int(sys.argv[4]) if len(sys.argv)>4 and not sys.argv[4].startswith('--') else 10**7
SHOW='--show' in sys.argv
import pickle,os
WORDS=[w for L in range(3,Lmax+1,4) for w in (pickle.load(open(f'mw_{L}.pkl','rb')) if WS=='min' and os.path.exists(f'mw_{L}.pkl') else gen(L,WS))]
PL=[(w,k) for w in WORDS for k in soff(w)]
WM=[(w,len(w),sum(1<<i for i,b in enumerate(w) if b)) for w in WORDS]
from collections import defaultdict
BYK=defaultdict(list)
for w,L,mk in WM:
    for k in soff(w): BYK[k].append((w,L,mk))
def fastopts(bits,members,sc):
    out=[]
    for k,lst in BYK.items():
        u=sc+k
        if u in members or bits.get(u,True) is not True or u<=0: continue
        km=0; kv=0
        for i in range(Lmax):
            c=u-i-1
            if c<0: b=True
            else:
                b=bits.get(c)
                if b is None: continue
            km|=1<<i
            if b: kv|=1<<i
        for w,L,mk in lst:
            m=km&((1<<L)-1)
            if (mk&m)==(kv&m): out.append((w,k))
    return out
nodes=0; sols=[]
def fits(bits,members,w,u):
    if u in members or bits.get(u,True) is not True or u<=0: return None
    new={u:True}
    for i,b in enumerate(w):
        c=u-i-1
        if c<0:
            if not b: return None
            continue
        if c in bits:
            if bits[c]!=b: return None
        else: new[c]=b
    return new
def covered_S(bits,members):
    out=set()
    for u,w in members.items():
        for k in soff(w):
            if u-k<=H: out.add(u-k)
    return out
def rec(bits,members,own,ownerOf):
    global nodes
    nodes+=1
    if nodes>nodeCap: return 'cap'
    need=sorted(c for c in covered_S(bits,members) if c not in ownerOf)
    if not need:
        sols.append((dict(members),dict(own))); return 'found'
    sc=need[0]
    # existing members without own covering sc
    for u,w in list(members.items()):
        if u in own: continue
        if sc in [u-k for k in soff(w)]:
            own2=dict(own); own2[u]=sc; of2=dict(ownerOf); of2[sc]=u
            r=rec(bits,members,own2,of2)
            if r in ('found','cap'): return r
    for w,k in fastopts(bits,members,sc):
        u=sc+k
        new=fits(bits,members,w,u)
        if new is None: continue
        b2=dict(bits); b2.update(new); m2=dict(members); m2[u]=w
        own2=dict(own); own2[u]=sc; of2=dict(ownerOf); of2[sc]=u
        r=rec(b2,m2,own2,of2)
        if r in ('found','cap'): return r
    return None
total={'found':0,'cap':0,None:0}
# choose two distinct members covering 0 (unordered: u1<u2), no own assigned yet; then close.
starts=[]
for w,k in PL:
    for kk in soff(w):
        pass
cands=[]
for w in WORDS:
    for u in range(1,len(w)+1):
        if not w[u-1]: # clock 0 = w_u must be S
            cands.append((u,w))
def cstr(u,w):
    return ''.join('A' if w[i] else 'S' for i in range(u-1,-1,-1))+'A'
cands=[(u,w) for u,w in cands if fits({0:False},{},w,u) is not None]
print('fitting candidates',len(cands),flush=True)
CC=sorted(((cstr(u,w),u,w) for u,w in cands))
pairs=[]
for i,(c,u,w) in enumerate(CC):
    for k in range(i+1,len(CC)):
        if not CC[k][0].startswith(c): break
        if len(CC[k][0])>len(c): pairs.append(((u,w),(CC[k][1],CC[k][2])))
print('candidate pairs',len(pairs),flush=True)
for (u1,w1),(u2,w2) in pairs:
    b1={0:False}
    n1=fits(b1,{},w1,u1)
    if n1 is None: continue
    b1.update(n1)
    n2=fits(b1,{u1:w1},w2,u2)
    if n2 is None: continue
    b2=dict(b1); b2.update(n2)
    r=rec(b2,{u1:w1,u2:w2},{},{})
    total[r]+=1
    if r=='found' and SHOW and len(sols)<=5:
        m,o=sols[-1]
        print('  partial:',' '.join(f'{u}:{s(w)}' for u,w in sorted(m.items())),' own',sorted(o.items()),flush=True)
print(f'{WS} Lmax={Lmax} H={H}: pairs found={total["found"]} cap={total["cap"]} excluded={total[None]} nodes={nodes}')
