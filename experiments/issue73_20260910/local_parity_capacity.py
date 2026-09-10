#!/usr/bin/env python3
"""H-09: local-clean all-lag charge and the concrete complete short image."""
import hashlib
import itertools
import json
from pathlib import Path
import subprocess
from short_reservoir_specialization import CHARGE


def analyze(e):
    p=len(e)
    U={}
    clean={}
    lags={}
    for t,current in enumerate(e):
        if current==-1:
            continue
        S=M=0
        even_A=True
        short=[]
        local=[]
        for d in range(1,max(11,2*p)+1):
            b=e[(t-d)%p]
            S+=b
            M+=d*b
            if d%2==0 and b==-1:
                even_A=False
            if S==1 and M==0:
                if d<=11:
                    short.append(d)
                if even_A:
                    assert d<2*p and d%8==3
                    local.append(d)
            if d>=11 and not even_A:
                break
        if short:
            d=min(short)
            if d==3:
                j=3
            elif d==7:
                pat=tuple(i for i in range(1,8) if e[(t-i)%p]==-1)
                assert pat in ((1,6,7),(2,5,7))
                j=7 if pat==(1,6,7) else 5
            else:
                assert d==11
                j=CHARGE[tuple(i for i in range(1,12) if e[(t-i)%p]==-1)]
            U[t]=(t-j)%p
        assert len(local)<=1,(e,t,local)
        if local:
            d=local[0]
            q=(t-(d+3)//2)%p
            assert e[q]==-1
            clean[t]=q
            lags[t]=d
            if d<=11:
                assert U[t]==q
    assert len(set(U.values()))==len(U)
    assert len(set(clean.values()))==len(clean),(e,clean,lags)
    Q={t:q for t,q in clean.items() if lags[t]>=19}
    assert not set(U)&set(Q),(e,U,Q)
    assert not set(U.values())&set(Q.values()),(e,U,Q,lags)
    assert len(U)+len(Q)<=e.count(-1)
    return len(U),len(clean),len(Q),max(lags.values(),default=0)


def scan(p):
    counts=[0,0,0]
    words_with_long=wrap=0
    maxlag=0
    for e in itertools.product((-1,1),repeat=p):
        u,c,q,d=analyze(e)
        counts=[a+b for a,b in zip(counts,(u,c,q))]
        words_with_long+=int(q>0)
        wrap+=int(d>p)
        maxlag=max(maxlag,d)
    return {'period':p,'words':2**p,'U11_phases':counts[0],'clean_phases':counts[1],
            'long_clean_phases':counts[2],'words_with_long_clean':words_with_long,
            'words_with_lag_over_period':wrap,'maximum_clean_lag':maxlag,'violations':0}


def local_word(k):
    compressed=(-1,)*k+(1,)+(-1,)*(3*k+1)
    w=tuple(b for v in compressed for b in (v,1))[:-1]
    assert len(w)==8*k+3 and sum(w)==1 and sum(i*b for i,b in enumerate(w,1))==0
    return w


def main():
    print('protocol=H-20260910-09')
    print('source_revision='+subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
    for name in ('local_parity_capacity.py','short_reservoir_specialization.py'):
        print(name+'_sha256='+hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest())
    for p in range(3,19):
        print(('DISCOVERY' if p<=12 else 'HOLDOUT')+'='+json.dumps(scan(p)),flush=True)
    for k,runs,shift in itertools.product(range(2,65),(1,3),(0,1)):
        e=()
        for i in range(runs):
            # Dirty short-pattern buffer plus two Ss breaks global parity.
            e+=tuple(reversed(local_word(k+i)))+(1,)+(-1,-1,1,1,-1,1,-1,-1)
        if shift:
            e=e[1:]+e[:1]
        u,c,q,d=analyze(e)
        print(('STRUCTURED_DISCOVERY' if k<=8 else 'STRUCTURED_HOLDOUT')+'='+json.dumps(
            {'k':k,'runs':runs,'shift':shift,'period':len(e),'U11':u,'clean':c,'long_clean':q,'max_lag':d}),flush=True)
    print('PASS: local half-lag charge is injective and compatible with the complete short map')


if __name__=='__main__':
    main()
