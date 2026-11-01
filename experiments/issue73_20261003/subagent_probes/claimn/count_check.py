"""Numeric check of the Removal/Counting lemma: v minimal P2 of lag L at clock 0 (newest member), own(v)=s*.
Every other S s of W_v must be owned by a member u<=-1 of a block (isolated AAS or w1 triple):
  AAS-type : u=s+3, sigma(s+1..s+3)=A                       (all clocks <= -1, so inside W_v)
  w1-type  : u=s+7 is w1 owning its oldest S, triple AAS at u+2=s+9<=-1:
             sigma(s+1)=S, s+2..s+5=A, s+6=S, s+7,s+8,s+9=A
Report words/s* for which every S in S_v has a compatible type (should be only AAS)."""
from mwords import minimal_words
def ok_types(bits,s):
    t=[]
    g=lambda c: bits.get(c)
    if s+3<=-1 and g(s+1) and g(s+2) and g(s+3): t.append('AAS')
    if s+9<=-1 and g(s+1) is False and all(g(s+i) for i in (2,3,4,5)) and g(s+6) is False and all(g(s+i) for i in (7,8,9)): t.append('w1')
    return t
for L in (3,7,11,15,19,23):
    surv=[]; tot=0
    for v in minimal_words(L):
        bits={0:True}
        for i,b in enumerate(v): bits[-(i+1)]=b
        S=[-(i+1) for i,b in enumerate(v) if not b]
        for st in S:
            tot+=1
            if all(ok_types(bits,s) for s in S if s!=st): surv.append((''.join('A' if b else 'S' for b in v),st))
    print(f"lag {L}: (v, own(v)) pairs {tot}; pairs where every other S has a block-compatible owner type: {surv[:5]} ({len(surv)})")
