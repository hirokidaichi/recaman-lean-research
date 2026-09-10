#!/usr/bin/env python3
"""H-10: freeze the short/clean map, then test full residual b=1 domains."""
import hashlib
import itertools
import json
from pathlib import Path
import subprocess
from short_reservoir_specialization import CHARGE


def maximum_matching(domains):
    target={}
    def augment(t,seen):
        for q in sorted(domains[t]):
            if q in seen:
                continue
            seen.add(q)
            if q not in target or augment(target[q],seen):
                target[q]=t
                return True
        return False
    for t in sorted(domains,key=lambda t:len(domains[t])):
        if not augment(t,set()):
            return None
    return target


def hall_witness(domains):
    keys=tuple(domains)
    for size in range(1,len(keys)+1):
        for subset in itertools.combinations(keys,size):
            union=set().union(*(domains[t] for t in subset))
            if len(union)<size:
                return {'sources':subset,'targets':sorted(union),'deficit':size-len(union)}
    raise AssertionError('augmenting-path and Hall audits disagree')


def analyze(e):
    p=len(e)
    old={}
    lags={}
    defects={}
    one={}
    for t,current in enumerate(e):
        if current==-1:
            continue
        mass=moment=b=0
        for d in range(1,max(11,4*p)+1):
            sign=e[(t-d)%p]
            mass+=sign
            moment+=d*sign
            b+=d%2==0 and sign==-1
            if mass==1 and moment==0:
                assert d%4==3 and b%2==((d-3)//4)%2
                lags[t]=d
                defects[t]=b
                if d<=11:
                    if d==3:
                        off=3
                    elif d==7:
                        off=7 if e[(t-1)%p]==-1 else 5
                    else:
                        off=CHARGE[tuple(i for i in range(1,12) if e[(t-i)%p]==-1)]
                    old[t]=(t-off)%p
                elif b==0:
                    old[t]=(t-(d+3)//2)%p
                elif b==1:
                    one[t]={q%p for q in range(t-d,t) if e[q%p]==-1}
                break
            if d>=11 and b>1:
                break
    assert all(e[q]==-1 for q in old.values())
    assert len(set(old.values()))==len(old)
    used=set(old.values())
    domains={t:qs-used for t,qs in one.items()}
    match=maximum_matching(domains)
    if match is None:
        witness=hall_witness(domains)
        # Independent direct moment audit, with every shorter lag tested.
        for t in lags:
            d=lags[t]
            exact=[s for s in range(1,d+1)
                   if sum(e[(t-i)%p] for i in range(1,s+1))==1
                   and sum(i*e[(t-i)%p] for i in range(1,s+1))==0]
            assert exact==[d]
        return {'word':''.join('A' if x==1 else 'S' for x in e),'period':p,
                'minimum_lags':lags,'even_S_counts':defects,'old_charge':old,
                'full_one_defect_domains':{t:sorted(qs) for t,qs in one.items()},
                'residual_domains':{t:sorted(qs) for t,qs in domains.items()},
                'hall_witness':witness}
    return len(old),len(one),max(lags.values(),default=0)


def b1_word(k,x,y):
    """Odd-A indices x<y; even-S index z=x+y-k, d=8k+7."""
    d=8*k+7
    z=x+y-k
    if not (0<=x<y<=(d-1)//2 and 1<=z<=(d-1)//2):
        return None
    w=tuple(1 if i%2==0 else -1 for i in range(1,d+1))
    w=list(w)
    w[2*x]=w[2*y]=1
    w[2*z-1]=-1
    assert sum(w)==1 and sum(i*b for i,b in enumerate(w,1))==0
    return tuple(w)


def main():
    print('protocol=H-20260910-10')
    print('source_revision='+subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
    for name in ('single_defect_matching.py','short_reservoir_specialization.py'):
        print(name+'_sha256='+hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest())
    for p in range(3,19):
        old=one=maxlag=0
        for e in itertools.product((-1,1),repeat=p):
            result=analyze(e)
            if isinstance(result,dict):
                print('REFUTED='+json.dumps(result),flush=True)
                print('STOP: frozen short/clean residual matching fails; no offset repair')
                return
            u,q,d=result
            old+=u;one+=q;maxlag=max(maxlag,d)
        print(('DISCOVERY' if p<=12 else 'HOLDOUT')+'='+json.dumps(
            {'period':p,'words':2**p,'old_phases':old,'one_defect_phases':one,'maximum_lag':maxlag}),flush=True)
    structured=0
    for k in range(1,65):
        for x,y in ((0,k+1),(k,k+1),(k+1,2*k+2),(2*k,2*k+3)):
            w=b1_word(k,x,y)
            if w is None:
                continue
            for buffer in ((-1,-1),(-1,-1,1,1,-1,1,-1,-1)):
                e=tuple(reversed(w))+(1,)+buffer
                result=analyze(e)
                structured+=1
                if isinstance(result,dict):
                    print('REFUTED_STRUCTURED='+json.dumps(result),flush=True)
                    print('STOP: frozen short/clean residual matching fails; no offset repair')
                    return
        print(('STRUCTURED_DISCOVERY' if k<=9 else 'STRUCTURED_HOLDOUT')+'='+json.dumps(
            {'k':k,'d':8*k+7,'cumulative_cases':structured}),flush=True)
    print('PASS: declared finite residual matching tests; general theorem remains unproved')


if __name__=='__main__':
    main()
