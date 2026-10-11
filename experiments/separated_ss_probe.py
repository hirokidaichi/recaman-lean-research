#!/usr/bin/env python3
"""Independent bounded exact search for separated SS donor collisions."""
from itertools import combinations
import json
import sys

def p2(w):
    mass = mom = 0
    hits = []
    for j, c in enumerate(w, 1):
        s = 1 if c == 'A' else -1
        mass += s
        mom += j*s
        if mass == 1 and mom == 0:
            hits.append(j)
    return hits

def no_saas(s):
    return all(''.join(s[(i+j)%len(s)] for j in range(4))!='SAAS' for i in range(len(s)))

def analyze(d):
    n = d-1
    xs = [('pure', 'AS'*(d-1)+'A')]
    if (d-1)%3 == 0:
        j=(d-1)//3
        xs.insert(0,('startS', 'SA'*j+'A'))
    counts = dict(all_c=0,moment=0,ss2separate=0,minimal_CA=0,pair_minimal=0,period_nosaas=0)
    for ss in combinations(range(n),n//2):
        counts['all_c'] += 1
        # Sum (j+1)*sign_j == -d and mass == 0.
        if sum(i+1 for i in ss) * 2 != n*(n+1)//2 + d:
            continue
        counts['moment'] += 1
        S=set(ss)
        edges=[i for i in range(n-1) if i in S and i+1 in S]
        if len(edges)!=2 or abs(edges[1]-edges[0])<2: continue
        counts['ss2separate'] += 1
        C=''.join('S' if i in S else 'A' for i in range(n))
        if p2(C+'A') != [d]: continue
        counts['minimal_CA'] += 1
        for kind,X in xs:
            XC=X+C
            if p2(XC) != [len(XC)]: continue
            counts['pair_minimal'] += 1
            for padding in (2,3,4):
                word=(XC[::-1]+'A'*padding)
                if not no_saas(word): continue
                counts['period_nosaas'] += 1
                return counts, dict(d=d, kind=kind,C=C,X=X,period=word,p=len(word),padding=padding,
                     ss_edges=edges, mass=sum(1 if c=='A' else -1 for c in word),
                     tA=len(C),tS=len(XC),lagA=d,lagS=len(XC),
                     p2A=p2(C+'A'),p2S=p2(XC))
    return counts, None

if __name__ == '__main__':
    for d in map(int, sys.argv[1:] or ('11','15','19','23')):
        counts,witness=analyze(d)
        print(json.dumps({'d':d,'counts':counts,'witness':witness}))
        sys.stdout.flush()
