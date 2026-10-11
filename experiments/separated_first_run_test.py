#!/usr/bin/env python3
"""Falsify exclusion of the first chronological SS-run start."""
from itertools import combinations
from separated_ss_probe import p2, no_saas
import json

def sign(c): return 1 if c=='A' else -1

def endpoint_witness(P,q):
    p=len(P)
    # t=q+lag, checking all current-A lowSS P2 lags up to p(p+1).
    mass=moment=ss=0
    prev='A'
    # For each lag d, the current t=q+d; the past, newest first, is P[q+d-1],...,P[q].
    # Moment must be recomputed as window length changes.
    for d in range(1,p*(p+1)+1):
        c=P[(q+d-1)%p]
        moment+=mass+sign(c)
        mass+=sign(c)
        ss+= c==prev=='S'
        prev=c
        if mass==1 and ss<=1 and P[(q+d)%p]=='A':
            if moment==0:
                return d,(q+d)%p
        if ss>1:break
    return None

def check(d):
    n=d-1
    xs=[('pure','AS'*(d-1)+'A')]
    if (d-1)%3==0:xs.append(('startS','SA'*((d-1)//3)+'A'))
    count={'moment':0,'split':0,'minimal_CA':0,'minimal_pair':0,'NoSAAS':0,'q1_endpoint':0,
           'nonminimal_CA_NoSAAS_q1_endpoint':0,
           'minimal_pair_nonNoSAAS_q1_endpoint':0,'minimal_CA_nonminimal_pair_NoSAAS_q1_endpoint':0}
    examples=[]
    for ss_indices in combinations(range(n),n//2):
        if 2*sum(i+1 for i in ss_indices)!=n*(n+1)//2+d:continue
        count['moment']+=1
        S=set(ss_indices)
        edge=[i for i in range(n-1) if i in S and i+1 in S]
        if len(edge)!=2 or edge[1]-edge[0]<2:continue
        count['split']+=1
        C=''.join('S' if i in S else 'A' for i in range(n))
        minCA=p2(C+'A')==[d]
        if not minCA:
            for kind,X in xs:
                P=(X+C)[::-1]+'AA'
                if not no_saas(P):continue
                q=n-2-edge[1]
                hit=endpoint_witness(P,q)
                if hit:
                    count['nonminimal_CA_NoSAAS_q1_endpoint']+=1
                    if len(examples)<10:examples.append({'d':d,'C':C,'X_kind':kind,'p':len(P),'period':P,
                            'first_run_start':q,'second_run_start':n-2-edge[0],
                            'q1_endpoint':hit,'CA_prefix_hits':p2(C+'A'),'XC_prefix_hits':p2(X+C),
                            'pair_minimal':False,'NoSAAS':True})
            continue
        count['minimal_CA']+=1
        for kind,X in xs:
            pair_minimal=p2(X+C)==[len(X+C)]
            if pair_minimal:count['minimal_pair']+=1
            P=(X+C)[::-1]+'AA'
            ns=no_saas(P)
            q=n-2-edge[1]  # first SS pair in chronological C
            hit=endpoint_witness(P,q)
            if pair_minimal and ns:
                count['NoSAAS']+=1
                if hit:count['q1_endpoint']+=1
            elif hit and pair_minimal:
                count['minimal_pair_nonNoSAAS_q1_endpoint']+=1
            elif hit and ns:
                count['minimal_CA_nonminimal_pair_NoSAAS_q1_endpoint']+=1
            if hit or (pair_minimal and ns and len(examples)<3):
                examples.append({'d':d,'C':C,'X_kind':kind,'p':len(P),
                  'period':P,'first_run_start':q,'second_run_start':n-2-edge[0],
                  'q1_endpoint':hit,'pair_minimal':pair_minimal,'NoSAAS':ns})
    return count,examples

if __name__=='__main__':
    for d in (11,15,19,23):
        c,e=check(d)
        print(json.dumps({'d':d,'counts':c,'examples':e[:10]}),flush=True)
