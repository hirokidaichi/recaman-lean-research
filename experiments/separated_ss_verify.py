#!/usr/bin/env python3
"""Direct periodic-clock verifier for the separated-SS witness family."""
from separated_ss_probe import no_saas
import json

C='AAASSASSASASAS'
X='AS'*14+'A'

def verify(n):
    w=(X+C)[::-1]+'A'*n
    p=len(w)
    def e(t):return w[t%p]
    def scan(t,d):
        b=[e(t-j) for j in range(1,d+1)]
        mass=sum(1 if c=='A' else -1 for c in b)
        moment=sum(j*(1 if c=='A' else -1) for j,c in enumerate(b,1))
        ss=sum(b[j]==b[j+1]=='S' for j in range(len(b)-1))
        return mass,moment,ss,''.join(b)
    donor=[]
    for t,expected in [(14,15),(43,43)]:
        hits=[d for d in range(1,expected+1) if scan(t,d)[:2]==(1,0)]
        m,q,ss,b=scan(t,expected)
        oldest=max(j for j,c in enumerate(b,1) if c=='S')
        donor.append(dict(t=t,current=e(t),lag=expected,hits=hits,ss=ss,
              word=b,oldest_phase=(t-oldest)%p,tail_A=expected-oldest))
    low=[]
    for t in range(p):
        if e(t)!='A':continue
        mass=moment=ss=0
        previous='A'
        for d in range(1,p*(p+1)+1):
            c=e(t-d)
            sign=1 if c=='A' else -1
            mass+=sign
            moment+=d*sign
            ss+=c==previous=='S'
            previous=c
            if (mass,moment)==(1,0) and ss<=1 and c=='S':
                low.append(dict(t=t,d=d,endpoint=(t-d)%p))
    E={v['endpoint'] for v in low}
    nb={j%p for t,d in [(14,15),(43,43)] for j in range(t-d,t) if e(j)=='S'}
    return dict(n=n,p=p,period=w,mass=w.count('A')-w.count('S'),noSAAS=no_saas(w),
                donor=donor,low=low,donor_neighborhood=sorted(nb),
                low_endpoints=sorted(E),free_donor_phases=sorted(nb-E))

for n in (2,3,7):
    print(json.dumps(verify(n)))
