#!/usr/bin/env python3
"""H-15: exact sign-word collision clocks and canonical blocker controls."""
import hashlib
import itertools
import json
from pathlib import Path
import subprocess


def main():
    print('protocol=H-20260910-15')
    print('source_revision='+subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
    print('source_sha256='+hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    for d in range(1,20):
        collisions=equality=0
        for w in itertools.product((-1,1),repeat=d):
            m=sum(w)
            if m==1:continue
            M=sum(i*b for i,b in enumerate(w,1))
            if M%(m-1):continue
            n=M//(m-1)
            if n<d+1:continue
            assert 4*n<=d*(d+4),(w,n)
            collisions+=1;equality+=4*n==d*(d+4)
        print(('DISCOVERY' if d<=13 else 'HOLDOUT')+'='+json.dumps(
            {'length':d,'words':2**d,'non_P2_collision_clocks':collisions,'equality':equality}),flush=True)
    for r in range(1,257):
        w=(-1,)*(r-1)+(1,)*(r+1)
        d=2*r;n=r*(r+2)
        assert sum(w)==2 and sum(i*b for i,b in enumerate(w,1))==n
        assert n>=d+1 and 4*n==d*(d+4)
        print(('FAMILY_DISCOVERY' if r<=32 else 'FAMILY_HOLDOUT')+'='+json.dumps(
            {'r':r,'lag':d,'clock':n,'slack':0}),flush=True)
    values=[0];signs=[];seen={0};count=nonp=rigid=0
    for t in range(2001):
        mass=moment=0
        for d in range(1,t+1):
            mass+=signs[t-d];moment+=d*signs[t-d]
            if values[t]==values[t-d]+t+1:
                count+=1
                assert moment==(t+1)*(mass-1)
                p2=mass==1 and moment==0
                if not p2:nonp+=1;assert 4*(t+1)<=d*(d+4)
                if d*(d+4)<4*(t+1):rigid+=1;assert p2
        v=values[t]
        bit=-1 if v>t+1 and v-(t+1) not in seen else 1
        signs.append(bit);values.append(v+bit*(t+1));seen.add(values[-1])
    print('CANONICAL='+json.dumps({'through':2000,'collision_pairs':count,'non_P2_pairs':nonp,'strict_rigid_pairs':rigid}))
    print('PASS: sharp word inequality and canonical short-blocker implication')


if __name__=='__main__':
    main()
