#!/usr/bin/env python3
"""Exact regression of the paper family refuting the escape-phase selector.
No held-out Recaman range or all-period finite enumeration is asserted.
"""
from pathlib import Path
from fractions import Fraction
import hashlib
import json
import subprocess


def verify(r):
    k=5*r
    m=4*r*(5*r-3)
    word=[1]*k+[-1]*(k-1)+[1,-1]*m
    p=len(word)
    remainder=2*m+3
    d=4*p+remainder
    assert p==40*r*r-14*r-1
    assert d==200*r*r-80*r-1
    assert 0<remainder<p and sum(word)==1
    escape=[]
    for t in range(p):
        h=0
        for j in range(p):
            h+=word[(t+j)%p]
            if h<1: break
        else: escape.append(t)
    assert escape==[0]
    backward=[word[-i%p] for i in range(1,d+1)]
    u=sum(backward)
    v=sum(i*e for i,e in enumerate(backward,1))
    vp=sum(i*word[-i%p] for i in range(1,p+1))
    vr=sum(i*word[-i%p] for i in range(1,remainder+1))
    assert vp==3*m+k*k and vr==-5*m-6
    assert u==1 and v==4*k*(k-3)-5*m==0
    out={'r':r,'k':k,'m':m,'period':p,'sign_sum':sum(word),'unique_escape':0,
         'P2_lag':d,'P2_sum':u,'P2_first_moment':v,'backward_period_moment':vp,
         'partial_moment':vr,'complete_periods':4,'remainder':remainder}
    if r==1:
        out['word']=''.join('A' if e>0 else 'S' for e in word)
        unsupported=[]
        for t,e in enumerate(word):
            if e<0: continue
            su=mo=0
            for lag in range(1,p*(p+1)+1):
                sign=word[(t-lag)%p]
                su+=sign
                mo+=lag*sign
                if su==1 and mo==0: break
            else: unsupported.append(t)
        assert unsupported==[1,3,4,9,11,13,15,17,19,21,23]
        out['unsupported_A_phases']=unsupported
    print(json.dumps(out,separators=(',',':'),sort_keys=True),flush=True)


def phase_invariants(word):
    p=len(word); S=sum(word)
    A=Fraction(p*S,2)
    B=sum((r+1)*e for r,e in enumerate(word))-A
    C=0; us=[]; ks=[]
    for r,e in enumerate(word):
        us.append(B/S-r)
        ks.append(C-B*B/(4*A))
        B+=p*e
        C+=(r+1)*e
    return us,ks


def geometric_controls():
    word=[-1,-1,1,-1,1,1,1]
    us,ks=phase_invariants(word)
    assert us==[Fraction(v,2) for v in (21,5,-11,1,-15,-3,9)]
    assert ks==[Fraction(v,8) for v in (-63,-15,-31,-7,-39,1,-7)]
    assert us[0]==max(us) and ks[0]==min(ks) and word[0]<0
    print('support_control=SSASAAA; unique_min_kappa=unique_max_u=phase0; next=S')
    for word,t,d in ((word,6,3),([1]*5+[-1]*4+[1,-1]*8,0,119)):
        us,ks=phase_invariants(word)
        p=len(word); R=Fraction(p,sum(word)); j=(t-d)%p; a=(t+1)%p
        assert us[a]-us[t]==R-1
        assert us[j]-us[t]==d-R
        assert ks[a]+ks[j]-2*ks[t]==-R
        print('phase_identity_control=period'+str(p)+' source'+str(t)+' lag'+str(d)+' PASS')


print('protocol=issue73 geometry escape-family fixed regression; paper proof covers all r>=1')
print('source_base_revision=b4b5afaaac126acaa0c4fc0042bdaa4fafd289a1')
print('current_revision='+subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
print('source_sha256='+hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
for r in (1,2,3,4): verify(r)
geometric_controls()
print('PASS: unique escape phase is supplied in every checked member; P2 main lemma not refuted')
