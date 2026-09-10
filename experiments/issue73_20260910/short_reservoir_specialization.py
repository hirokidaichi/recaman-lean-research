#!/usr/bin/env python3
"""H-06: actual short map, all eligible Qs, and rank construction."""
import hashlib
import itertools
import json
from pathlib import Path
import subprocess
from bounded_excess_multiplicity import sharp
from reservoir_capacity import run_data, almost_sharp


CHARGE=dict(zip(((1,2,9,10,11),(1,3,8,10,11),(1,4,7,10,11),(1,4,8,9,11),
                (1,5,6,10,11),(1,5,7,9,11),(1,5,8,9,10),(2,3,7,10,11),
                (2,3,8,9,11),(2,4,6,10,11),(2,4,7,9,11),(2,4,8,9,10),
                (2,5,6,9,11),(2,6,7,8,10),(4,5,6,7,11),(4,5,6,8,10),(4,5,7,8,9)),
               (10,3,4,4,6,7,8,10,9,4,4,4,6,7,6,6,7)))


def phase_hits(e,t,limit):
    p=len(e)
    mass=moment=0
    hs=[]
    for d in range(1,limit+1):
        b=e[(t-d)%p]
        mass+=b
        moment+=d*b
        if mass==1 and moment==0:
            hs.append(d)
    return hs


def inspect(e,R,kind):
    p=len(e)
    U={}
    Q={}
    Qmin={}
    M=4*R+13
    data=run_data(e)
    for t,m,a,B,b in data:
        limit=max(11,4*m-1+4*R if m>=M else 11)
        hs=phase_hits(e,t,limit)
        short=[d for d in hs if d<=11]
        if short:
            d=min(short)
            if d==3:
                j=3
            elif d==7:
                pattern=tuple(k for k in range(1,8) if e[(t-k)%p]==-1)
                assert pattern in ((1,6,7),(2,5,7))
                j=7 if pattern==(1,6,7) else 5
            else:
                assert d==11
                j=CHARGE[tuple(k for k in range(1,12) if e[(t-k)%p]==-1)]
            U[t]=(t-j)%p
        if m>=M and hs:
            assert min(hs)>=4*m-1
            Q[t]=(m,a)
            Qmin[t]=min(hs)
    assert len(set(U.values()))==len(U)
    assert all(e[q]==-1 for q in U.values())
    old=set(U.values())
    new={}
    for t,(m,a) in Q.items():
        free=[(t-j)%p for j in range(m+1,2*m) if e[(t-j)%p]==-1 and (t-j)%p not in old]
        rank=m-M
        assert rank<len(free)
        new[t]=free[rank]
    assert len(set(new.values()))==len(new)
    assert not old&set(new.values())
    S=e.count(-1)
    assert len(U)+len(Q)<=S
    return {'kind':kind,'R':R,'period':p,'A':e.count(1),'S':S,'U11':len(U),'Q':len(Q),
            'nonsharp_Q':sum(Qmin[t]>4*m-1 for t,(m,a) in Q.items()),
            'Q_minimum_lags':sorted(set(Qmin.values())),
            'capacity_slack':S-len(U)-len(Q),'rank_injection_verified':True}


def main():
    print('protocol=H-20260910-06')
    print('source_revision='+subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
    for name in ('short_reservoir_specialization.py','reservoir_capacity.py','bounded_excess_multiplicity.py'):
        print(name+'_sha256='+hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest())
    # Frozen: R0..4 discovery,5..12 holdout; offsets0,3; one/three source blocks.
    for R,delta,runs in itertools.product(range(13),(0,3),(1,3)):
        M=4*R+13
        e=()
        for i in range(runs):
            m=M+delta+3*i
            w=sharp(m) if R==0 else almost_sharp(m)
            e+=tuple(reversed(w))+(1,)+((-1,)*13 if runs>1 else ())
        print(('DISCOVERY' if R<=4 else 'HOLDOUT')+'='+json.dumps(inspect(e,R,f'near_sharp_delta{delta}_runs{runs}')),flush=True)
    # Extremal middle-density family, R1..12; R1 is correctly ineligible.
    for R in range(1,13):
        m=6*R*R
        w=(1,)*m+(-1,)*(m-2*R-1)+(1,)*(2*R)+(-1,)*(m+4*R)+(1,)*m
        e=tuple(reversed(w))+(1,)
        print(('DENSITY_DISCOVERY' if R<=4 else 'DENSITY_HOLDOUT')+'='+json.dumps(inspect(e,R,'extremal_middle_density')),flush=True)
    print('PASS: concrete U11 plus every eligible bounded-excess Q has an injective S charge')


if __name__=='__main__':
    main()
