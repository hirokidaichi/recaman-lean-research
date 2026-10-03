#!/usr/bin/env python3
"""R' test: member w at clock 0 (any position in the component, owners may be NEWER), window W_w = minimal P2
word, own(w) = s* (private), every other S s of W_w owned by a motif member of M' = M \\ {w}:
  type A: AAS at s+3 (bits s+1, s+2 A, s+3 A member, s+3 != 0);
  type W: triple w1 at s+7 owning s (bits s+1 S, s+2..s+5 A, s+6 S, s+7 A member != 0), whose siblings
          AAS@s+4 owns s+1 and AAS@s+9 owns s+6 (so s+1, s+6 if in W_w must be type A, and != s*).
Bits: W_w known, clock 0 = A (w), other clocks free but must be consistent across owners.
Owners distinct and != 0.  Which (w, s*) admit an assignment?"""
import sys
from itertools import product
sys.path.insert(0, __import__('os').path.dirname(__file__))
from walk import mins, s as ws
Lmax=int(sys.argv[1])
res={}
for L in range(3,Lmax+1,4):
    feas=[]
    for w in mins(L):
        bits0={0:True}
        for i,b in enumerate(w): bits0[-(i+1)]=b
        Ss=[-(i+1) for i,b in enumerate(w) if not b]
        for sstar in Ss:
            others=[x for x in Ss if x!=sstar]
            for types in product('AW',repeat=len(others)):
                bits=dict(bits0); owners={}; ok=True
                ty=dict(zip(others,types))
                def setb(c,v):
                    if c in bits and bits[c]!=v: return False
                    bits[c]=v; return True
                def addowner(u,s_):
                    if u==0 or u in owners: return False
                    owners[u]=s_; return setb(u,True)
                for s_,t_ in ty.items():
                    if t_=='A':
                        ok = ok and setb(s_+1,True) and setb(s_+2,True) and addowner(s_+3,s_)
                    else:
                        ok = ok and setb(s_+1,False) and all(setb(s_+d,True) for d in (2,3,4,5)) and setb(s_+6,False) and addowner(s_+7,s_)
                        # siblings: s+1 owned by AAS@s+4, s+6 owned by AAS@s+9
                        for sib_s in (s_+1,s_+6):
                            if sib_s==sstar: ok=False
                            if sib_s in ty and ty[sib_s]!='A': ok=False
                        if ok and (s_+6) not in ty:   # s+6 outside W_w (newer than w) or = sstar handled
                            ok = ok and setb(s_+7,True) and setb(s_+8,True) and addowner(s_+9,s_+6)
                    if not ok: break
                if ok:
                    feas.append((ws(w), -sstar, ''.join(types))); break
    res[L]=feas
    print(L, 'feasible (word, own offset, types):', len(feas), feas[:6])
