#!/usr/bin/env python3
"""H-13 transfer: does the stopped centered map also fail canonically?"""
import hashlib
import json
from pathlib import Path
import subprocess
from short_reservoir_specialization import CHARGE


def main():
    print('protocol=H-20260910-13-canonical-transfer')
    print('source_revision='+subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
    for name in ('one_ss_canonical_counterexample.py','short_reservoir_specialization.py'):
        print(name+'_sha256='+hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest())
    values=[0];signs=[];ssPrefix=[0];seen={0};latest={(0,0):0};P=W=0;used={}
    for t in range(10000001):
        value=values[t]
        isS=value>t+1 and value-(t+1) not in seen
        hit=latest.get((P-1,W-t))
        if hit is not None:
            assert not isS
            d=t-hit
            ss=ssPrefix[t]-ssPrefix[hit+1] if d else 0
            category=None
            if d<=11:
                category='old_short'
                if d==3:off=3
                elif d==7:off=7 if signs[t-1]==-1 else 5
                else:off=CHARGE[tuple(i for i in range(1,12) if signs[t-i]==-1)]
            elif ss==0:
                category='old_clean';off=(d+3)//2
            elif ss==1:
                category='new_one_SS';off=(d+3)//2
                if signs[t-off]==1:off+=1 if signs[t-1]==-1 else -1
            if category:
                q=t-off
                row={'t':t,'next_step':t+1,'value':value,'lag':d,'category':category,'offset':off,'target':q}
                if signs[q]!=-1 or q in used:
                    previous=used.get(q)
                    if previous:assert 'new_one_SS' in (category,previous['category'])
                    for source in (row,previous):
                        if source is None:continue
                        s=source['t'];lags=[];mass=moment=0
                        for ell in range(1,s+1):
                            mass+=signs[s-ell];moment+=ell*signs[s-ell]
                            if mass==1 and moment==0:lags.append(ell)
                        assert lags and min(lags)==source['lag']
                        window=signs[s-source['lag']:s]
                        source['all_P2_lags']=lags
                        source['newest_first']=''.join('A' if b==1 else 'S' for b in reversed(window))
                        source['adjacent_SS']=sum(window[i]==window[i+1]==-1 for i in range(len(window)-1))
                        assert sum(window)==1
                        assert 'SAAS' not in source['newest_first']
                    print('CANONICAL_REFUTED='+json.dumps({'current':row,'previous':previous,
                        'target_sign':signs[q],'target_step':q+1,'target_value_before':values[q],
                        'target_value_after':values[q+1]}),flush=True)
                    print('STOP: the same unmodified centered map fails on the actual standard orbit')
                    return
                used[q]=row
        if t in (100000,1000000,10000000):
            print('CHECKPOINT='+json.dumps({'t':t,'checked_charges':len(used)}),flush=True)
        bit=-1 if isS else 1
        if len(signs)>=3:assert not (signs[-3:]==[-1,1,1] and bit==-1)
        ssPrefix.append(ssPrefix[-1]+int(bit==-1 and bool(signs) and signs[-1]==-1))
        signs.append(bit);values.append(value+bit*(t+1));seen.add(values[-1])
        P+=bit;W+=t*bit;latest[(P,W)]=t+1
    print('PASS: no canonical failure in the declared range; the periodic refutation remains')


if __name__=='__main__':
    main()
