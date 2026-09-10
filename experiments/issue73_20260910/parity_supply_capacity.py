#!/usr/bin/env python3
"""H-08: all-lag signatures and the one-parity classification/charge."""
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
import subprocess

DEPENDENCY=Path('experiments/parallel20260907/periodic_search.py')
spec=importlib.util.spec_from_file_location('frozen_periodic_solver',DEPENDENCY)
solver=importlib.util.module_from_spec(spec)
spec.loader.exec_module(solver)


def predicted(f,n):
    p=len(f)
    result=[]
    if all(b==-1 for b in f):
        return result
    # A window of at least2p compressed signs contains at leasttwo A defects.
    # Thus k>=p cannot satisfy the one-defect classification.
    for k in range(p):
        center=n-k
        if f[center%p]!=1:
            continue
        if all(f[i%p]==(-1 if i!=center else 1) for i in range(n-4*k-1,n+1)):
            result.append(8*k+3)
    return result


def scan(p):
    words=supplied=long_lags=equal_capacity=0
    max_lag=0
    min_slack=None
    example=None
    for f in itertools.product((-1,1),repeat=p):
        words+=1
        e=tuple(b for a in f for b in (a,1))
        if all(b==-1 for b in f):
            sig={t:[] for t,b in enumerate(e) if b==1}
            assert solver.naive(e)==sig
        else:
            sig=solver.suppliers(e)
            if p<=6:
                assert sig==solver.naive(e)
        image={}
        for t,ds in sig.items():
            expected=[] if t%2==0 else predicted(f,t//2)
            assert ds==expected,(f,t,ds,expected)
            assert len(ds)<=1
            if ds:
                d=ds[0]
                supplied+=1
                max_lag=max(max_lag,d)
                long_lags+=int(d>len(e))
                q=(t-(d+3)//2)%len(e)
                assert e[q]==-1 and q not in image,(f,t,d,q,image)
                image[q]=t
                if d>11 and example is None:
                    example={'even_signs':''.join('A' if b==1 else 'S' for b in f),
                             'phase':t,'lag':d,'charge':q}
        slack=e.count(-1)-len(image)
        assert slack>=0
        equal_capacity+=int(slack==0)
        min_slack=slack if min_slack is None else min(min_slack,slack)
        # Shift origin by one: the classification parity and charge translate.
        shifted=e[1:]+e[:1]
        if sum(e)>0:
            sig2=solver.suppliers(shifted)
            assert sig2=={(t-1)%len(e):ds for t,ds in sig.items()}
    return {'compressed_period':p,'words':words,'supplied_phases':supplied,
            'lags_longer_than_original_period':long_lags,'maximum_lag':max_lag,
            'equality_words':equal_capacity,'minimum_slack':min_slack,
            'first_lag_above_11':example,'violations':0}


def negative_control():
    for p in range(3,13):
        for e in itertools.product((-1,1),repeat=p):
            if sum(e)<=0:
                continue
            sig=solver.suppliers(e)
            for t,ds in sig.items():
                for d in ds:
                    q=(t-(d+3)//2)%p
                    if d%8!=3 or e[q]!=-1:
                        return {'word':''.join('A' if b==1 else 'S' for b in e),
                                'phase':t,'lag':d,'putative_charge':q,
                                'putative_charge_sign':'A' if e[q]==1 else 'S'}
    raise AssertionError('missing negative control')


def main():
    print('protocol=H-20260910-08')
    print('source_revision='+subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
    print('script_sha256='+hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    print('solver_sha256='+hashlib.sha256(DEPENDENCY.read_bytes()).hexdigest())
    for p in range(1,15):
        print(('DISCOVERY' if p<=10 else 'HOLDOUT')+'='+json.dumps(scan(p)),flush=True)
    print('DROP_PARITY_CONTROL='+json.dumps(negative_control()))
    print('PASS: all-lag classification and injective S charge survived; parity premise is essential')


if __name__=='__main__':
    main()
