#!/usr/bin/env python3
"""AW lemma (lag-free): in a closed configuration all of whose members are AAS or w1=SAAAASS,
(1) every w1 member b owns b-7, and b-6 / b-1 are owned by AAS@b-3 / AAS@b+2;
(2) no AAS/w1 member other than the triple's three has a window containing b-7, b-6 or b-1;
(3) an AAS member whose S lies in another member's window is a triple's AAS.
Checked by enumerating, for w1 at 0, every owner (AAS or w1, any S offset) of each S consistent with the bits."""
WORDS={'AAS':(True,True,False),'SAAAASS':(False,True,True,True,True,False,False)}
def soff(w): return [i+1 for i,b in enumerate(w) if not b]
def fits(bits,u,w):
    if bits.get(u,True) is not True: return False
    return all(bits.get(u-(i+1),b)==b for i,b in enumerate(w))
w1=WORDS['SAAAASS']
bits={0:True}
for i,b in enumerate(w1): bits[-(i+1)]=b
print('owners of each S of w1@0 among AAS/w1 members (other than w1@0 itself):')
for k in soff(w1):
    sc=-k; opts=[(n,sc+kk) for n,w in WORDS.items() for kk in soff(w) if sc+kk!=0 and fits(bits,sc+kk,w)]
    print('  S at',sc,'->',opts)
# (2) intruders: triple bits, AAS/w1 member at clock x not in {-3,0,2} whose window meets {-7,-6,-1}
tb=dict(bits); tb.update({1:True,2:True})
intr=[]
for n,w in WORDS.items():
    for x in range(-6,10):
        if x in (-3,0,2): continue
        win=range(x-len(w),x)
        if not any(c in win for c in (-7,-6,-1)): continue
        if fits(tb,x,w): intr.append((n,x))
print('AAS/w1 intruders into triple S-set {-7,-6,-1}:',intr,'(an AAS intruder would own a triple S: injectivity)')
