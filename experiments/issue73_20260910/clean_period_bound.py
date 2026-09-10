#!/usr/bin/env python3
"""H-14: all-sign clean period bounds and the sharp family."""
import hashlib
import itertools
import json
from pathlib import Path
import subprocess


def main():
    print('protocol=H-20260910-14')
    print('source_revision='+subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
    print('source_sha256='+hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    for p in range(1,17):
        hits=Ahits=wrap=0
        for e in itertools.product((-1,1),repeat=p):
            for t,current in enumerate(e):
                mass=moment=0
                for d in range(1,2*p+1):
                    b=e[(t-d)%p]
                    if d%2==0 and b==-1:break
                    mass+=b;moment+=d*b
                    if mass==1 and moment==0:
                        assert d%8==3
                        k=(d-3)//8
                        assert d<2*p
                        if p%2==0:assert p>=6*k+4
                        else:assert d<=p
                        if current==1:
                            assert 3*d+7<=4*p
                            if p%2:assert d+2<=p
                            Ahits+=1
                        hits+=1;wrap+=d>p
        print(('DISCOVERY' if p<=10 else 'HOLDOUT')+'='+json.dumps(
            {'period':p,'words':2**p,'clean_all_current_signs':hits,'clean_current_A':Ahits,'lag_over_period':wrap}),flush=True)
    for k in range(513):
        p=6*k+4;t=2*k+1;d=8*k+3
        def sign(x):return 1 if x%2 or x%p==0 else -1
        w=[sign(t-i) for i in range(1,d+1)]
        assert sign(t)==1 and all(sign(x+p)==sign(x) for x in range(-p,p))
        mass=moment=0;lags=[]
        for ell,b in enumerate(w,1):
            mass+=b;moment+=ell*b
            if mass==1 and moment==0:lags.append(ell)
        assert lags==[d] and all(w[i-1]==1 for i in range(2,d+1,2)) and 3*d+7==4*p
        print(('FAMILY_DISCOVERY' if k<=32 else 'FAMILY_HOLDOUT')+'='+json.dumps(
            {'k':k,'period':p,'lag':d,'slack':4*p-3*d-7}),flush=True)
    e=(-1,1,1);t=0;d=3
    w=[e[(t-i)%3] for i in range(1,d+1)]
    assert e[t]==-1 and sum(w)==1 and sum(i*b for i,b in enumerate(w,1))==0 and 3*d+7>12
    print('NEGATIVE_CONTROL='+json.dumps({'period':3,'word':'SAA','t':0,'lag':3,'current':'S','strong_bound_fails':True}))
    print('PASS: sharp bound with current-A qualification and unconditional d<2p')


if __name__=='__main__':
    main()
