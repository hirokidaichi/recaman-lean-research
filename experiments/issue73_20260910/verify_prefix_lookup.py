#!/usr/bin/env python3
"""Independent finite falsifier for the all-history P2 prefix lookup."""
import hashlib
import itertools
import json
from pathlib import Path
import subprocess


def fast(word):
    P=W=0
    latest={(0,0):0}
    result=[]
    for t,b in enumerate(word):
        old=latest.get((P-1,W-t))
        result.append(None if old is None else t-old)
        P+=b
        W+=t*b
        latest[P,W]=t+1
    return result


def naive(word):
    result=[]
    for t in range(len(word)):
        S=M=0
        best=None
        for d in range(1,t+1):
            S+=word[t-d]
            M+=d*word[t-d]
            if S==1 and M==0:
                best=d
                break
        result.append(best)
    return result


def main():
    print('protocol=H-20260910-07-lookup')
    print('source_revision='+subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
    print('script_sha256='+hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    for n in range(1,14):
        count=0
        for w in itertools.product((-1,1),repeat=n):
            assert fast(w)==naive(w),(w,fast(w),naive(w))
            count+=1
        print(('DISCOVERY' if n<=8 else 'HOLDOUT')+'='+json.dumps({'length':n,'words':count,'mismatches':0}),flush=True)
    seen={0}
    a=0
    signs=[]
    values=[]
    for n in range(1,5001):
        b=-1 if a>n and a-n not in seen else 1
        a+=b*n
        seen.add(a)
        signs.append(b)
        values.append(a)
    assert values[:15]==[1,3,6,2,7,13,20,12,21,11,22,10,23,9,24]
    assert fast(signs)==naive(signs)
    print('STANDARD_PREFIX='+json.dumps({'steps':5000,'last_value':a,'lookup_mismatches':0}))
    print('PASS: exact all-available-history minimum P2 lookup agrees with direct sums')


if __name__=='__main__':
    main()
