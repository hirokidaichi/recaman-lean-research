#!/usr/bin/env python3
"""H-12: independent direct lag check against actual height/value blockers."""
import hashlib
import json
from pathlib import Path
import subprocess


def main():
    print('protocol=H-20260910-12')
    print('source_revision='+subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
    print('source_sha256='+hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    values=[0];heights=[0];signs=[];seen={0}
    checked=hits=blockers_without_p2=0
    for t in range(2001):
        value=values[t]
        isS=value>t+1 and value-(t+1) not in seen
        mass=moment=0;has_p2=False
        for d in range(t+1):
            if d:
                mass+=signs[t-d]
                moment+=d*signs[t-d]
            p2=mass==1 and moment==0
            key=heights[t]-heights[t-d]==1 and values[t]==values[t-d]+t+1
            assert p2==key,(t,d,p2,key)
            assert not (p2 and isS),(t,d)
            checked+=1;hits+=p2;has_p2|=p2
        historical=value>t+1 and value-(t+1) in seen
        blockers_without_p2+=historical and not has_p2
        if t==5:
            assert historical and value-(t+1)==1 and not has_p2
            print('NEGATIVE='+json.dumps({'t':5,'value':value,'candidate':1,'old_time':1,'P2_lags':[]}))
        if t==6:
            assert has_p2 and values[6]==values[3]+7 and heights[6]-heights[3]==1
        if t in (500,2000):
            print(('DISCOVERY' if t==500 else 'HOLDOUT_CUMULATIVE')+'='+json.dumps(
                {'through_sign_time':t,'window_pairs':checked,'P2_witnesses':hits,
                 'positive_historical_blockers_without_P2':blockers_without_p2}),flush=True)
        bit=-1 if isS else 1
        signs.append(bit)
        values.append(value+bit*(t+1));heights.append(heights[-1]+bit);seen.add(values[-1])
    print('PASS: finite P2 iff height-one actual blocker; every P2 forces A')


if __name__=='__main__':
    main()
