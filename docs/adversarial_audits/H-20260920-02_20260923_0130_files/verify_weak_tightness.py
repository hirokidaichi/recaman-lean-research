#!/usr/bin/env python3
"""Recheck every retained premise of a no-tightness countermodel."""

import json

cycle = 'AASAAASS'
p = 8
u0 = 1
B = [1]
lag = {1: 11}

def past(t,d):
    return ''.join(cycle[(t-k)%p] for k in range(1,d+1))

def p2(w):
    z = [1 if x=='A' else -1 for x in w]
    return sum(z)==1 and sum(k*x for k,x in enumerate(z,1))==0

def ss(w):
    return sum(w[i:i+2]=='SS' for i in range(len(w)-1))

N=sorted({(b-k)%p for b in B for k in range(1,lag[b]+1) if cycle[(b-k)%p]=='S'})
donor=past(u0,11)
old=max(k for k,x in enumerate(donor,1) if x=='S')
s=(u0-old)%p
out={'cycle':cycle,'p':p,'u0':u0,'B':B,'lag':lag,'B_window':past(1,11),
     'donor_window':donor,'B_current':cycle[1], 'B_P2':p2(past(1,11)),
     'B_proper_P2_prefixes':[d for d in range(1,11) if p2(past(1,d))],
     'donor_P2':p2(donor),'donor_SS':ss(donor),'N':N,
     'tight':len(N)==len(B),'oldest_offset':old,'oldest_phase':s,'covered':s in N}
print(json.dumps(out,sort_keys=True))
assert p>0 and len(B)==len(set(B)) and B[0]<p and cycle[B[0]]=='A'
assert lag[B[0]]==11 and out['B_P2'] and not out['B_proper_P2_prefixes']
assert out['donor_P2'] and out['donor_SS']==2 and not out['tight'] and out['covered']
