#!/usr/bin/env python3
"""H-11: exact no-SS mass-one language via the two extra A gaps."""
import hashlib
import itertools
import json
from pathlib import Path
import subprocess


def words(n):
    for i in range(n+1):
        for j in range(i,n+1):
            gaps=[0]+[1]*(n-1)+[0]
            gaps[i]+=1
            gaps[j]+=1
            yield 'S'.join('A'*g for g in gaps)


def p2(w):
    signs=[1 if c=='A' else -1 for c in w]
    return sum(signs)==1 and sum(i*b for i,b in enumerate(signs,1))==0


def main():
    print('protocol=H-20260910-11')
    print('source_revision='+subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
    print('source_sha256='+hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    for n in range(1,8):
        direct={''.join(w) for w in itertools.product('AS',repeat=2*n+1)
                if w.count('A')-w.count('S')==1 and 'SS' not in ''.join(w)}
        assert direct==set(words(n))
    print('INDEPENDENT=all binary words through length15 agree with the gap generator')
    negative='ASAASAS'
    assert p2(negative) and 'SS' not in negative and 'SAAS' in negative and negative[1::2]!='A'*3
    print('NEGATIVE_CONTROL='+json.dumps({'newest_first':negative,'lag':7,'P2':True,'no_SS':True,'clean':False}))
    total=hits=0
    for n in range(1,257):
        count=good=bad=0
        for w in words(n):
            count+=1
            assert len(w)==2*n+1 and w.count('A')==n+1 and w.count('S')==n and 'SS' not in w
            if p2(w):
                if 'SAAS' not in w:
                    good+=1
                    assert w[1::2]=='A'*n
                else:
                    bad+=1
        total+=count;hits+=good
        print(('DISCOVERY' if n<=32 else 'HOLDOUT')+'='+json.dumps(
            {'S_count':n,'length':2*n+1,'words':count,'P2_no_SAAS':good,
             'P2_with_SAAS':bad,'violations':0}),flush=True)
    print('PASS='+json.dumps({'total_words':total,'P2_no_SS_no_SAAS':hits}))


if __name__=='__main__':
    main()
