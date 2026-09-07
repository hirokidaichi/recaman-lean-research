#!/usr/bin/env python3
"""Frozen G1 / G2 escape-phase selectors; exact finite falsification only."""
from itertools import product
from pathlib import Path
import hashlib
import json
import subprocess


def supplier(word,t):
    p=len(word)
    s=w=0
    for d in range(1,p*(p+1)+1):
        e=word[(t-d)%p]
        s+=e
        w+=d*e
        if s==1 and w==0:
            return d
    return None


def escapes(word,t):
    p=len(word)
    partial=0
    for d in range(p):
        partial+=word[(t+d)%p]
        if partial<1:
            return False
    return True


def main():
    print('protocol=issue73 geometry G1/G2 selectors; finite discovery only; no holdout')
    print('source_base_revision=b4b5afaaac126acaa0c4fc0042bdaa4fafd289a1')
    print('current_revision='+subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
    print('source_sha256='+hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    first_g1=None
    for p in range(1,13):
        checked=0
        for word in product((-1,1),repeat=p):
            if sum(word)<=0: continue
            checked+=1
            escape=[t for t in range(p) if escapes(word,t)]
            assert escape
            supply={t:supplier(word,t) for t in escape}
            if first_g1 is None and any(d is not None for d in supply.values()):
                first_g1={"word":''.join('A' if e==1 else 'S' for e in word),'p':p,
                          'S':sum(word),'escape_phases':escape,'supplier_lags':supply}
                print('G1_COUNTEREXAMPLE='+json.dumps(first_g1,sort_keys=True),flush=True)
            if all(d is not None for d in supply.values()):
                print('G2_COUNTEREXAMPLE='+json.dumps({"word":''.join('A' if e==1 else 'S' for e in word),'p':p,
                          'S':sum(word),'escape_phases':escape,'supplier_lags':supply},sort_keys=True),flush=True)
                return
        print('period='+str(p)+' words='+str(checked)+' G2_counterexamples=0',flush=True)
    print('END: finite selector scan only; no all-period theorem')


if __name__=='__main__':
    main()
