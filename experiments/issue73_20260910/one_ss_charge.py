#!/usr/bin/env python3
"""H-13: no-SAAS one-SS midpoint charge, with the proved old map frozen."""
import hashlib
import itertools
import json
from pathlib import Path
import subprocess
from short_reservoir_specialization import CHARGE


def no_saas(e):
    p=len(e)
    return all(tuple(e[(i+j)%p] for j in range(4))!=(-1,1,1,-1) for i in range(p))


def analyze(e):
    if not no_saas(e):
        return None
    p=len(e)
    old={};new={};lags={};witnesses={}
    for t,current in enumerate(e):
        if current==-1:
            continue
        mass=moment=ss=0;last=None
        for d in range(1,max(11,2*p+2)+1):
            sign=e[(t-d)%p]
            ss+=last==sign==-1
            last=sign
            mass+=sign;moment+=d*sign
            if mass==1 and moment==0:
                lags[t]=d
                if d<=11:
                    if d==3:off=3
                    elif d==7:off=7 if e[(t-1)%p]==-1 else 5
                    else:off=CHARGE[tuple(i for i in range(1,12) if e[(t-i)%p]==-1)]
                    old[t]=(t-off)%p
                elif ss==0:
                    old[t]=(t-(d+3)//2)%p
                elif ss==1:
                    off=(d+3)//2
                    if e[(t-off)%p]==1:
                        off+=1 if e[(t-1)%p]==-1 else -1
                    new[t]=(t-off)%p
                    witnesses[t]={'lag':d,'offset':off,'newest_first':''.join(
                        'A' if e[(t-i)%p]==1 else 'S' for i in range(1,d+1))}
                break
            if d>=11 and ss>1:
                break
    assert len(set(old.values()))==len(old) and all(e[q]==-1 for q in old.values())
    failure=None
    for t,q in new.items():
        if e[q]!=-1:failure=('non_S',t,q);break
        collision=[u for u,r in old.items() if r==q]
        if collision:failure=('old_collision',t,collision[0],q);break
        collision=[u for u,r in new.items() if u<t and r==q]
        if collision:failure=('new_collision',t,collision[0],q);break
    if failure:
        for t,d in lags.items():
            direct=[]
            for s in range(1,d+1):
                v=[e[(t-i)%p] for i in range(1,s+1)]
                if sum(v)==1 and sum(i*b for i,b in enumerate(v,1))==0:direct.append(s)
            assert direct==[d]
        return {'failure':failure,'word':''.join('A' if b==1 else 'S' for b in e),
                'period':p,'old_map':old,'new_map':new,'minimum_lags':lags,'one_SS_windows':witnesses}
    return len(old),len(new)


def gap_windows(n):
    for z in range(1,n):
        for j in range(1,n):
            if j==z:continue
            for extra,left,right in ((3,0,0),(2,1,0),(2,0,1)):
                gaps=[left]+[1]*(n-1)+[right]
                gaps[z]=0;gaps[j]+=extra
                yield gaps,('internal',j,z,extra,left,right)
        for left in range(4):
            gaps=[left]+[1]*(n-1)+[3-left]
            gaps[z]=0
            yield gaps,('ends',z,left)


def main():
    print('protocol=H-20260910-13')
    print('source_revision='+subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
    for name in ('one_ss_charge.py','short_reservoir_specialization.py'):
        print(name+'_sha256='+hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest())
    for p in range(3,19):
        eligible=old=new=0
        for e in itertools.product((-1,1),repeat=p):
            r=analyze(e)
            if r is None:continue
            if isinstance(r,dict):
                print('REFUTED='+json.dumps(r),flush=True)
                print('STOP: centered one-SS map failed; no offset repair')
                return
            eligible+=1;old+=r[0];new+=r[1]
        print(('DISCOVERY' if p<=12 else 'HOLDOUT')+'='+json.dumps(
            {'period':p,'eligible_words':eligible,'old_phases':old,'one_SS_phases':new}),flush=True)
    saved=[];windowcount=0
    for n in range(1,129):
        count=minimum=0
        for gaps,params in gap_windows(n):
            w='S'.join('A'*g for g in gaps)
            assert w.count('SS')==1 and 'SAAS' not in w
            v=tuple(1 if c=='A' else -1 for c in w)
            assert sum(v)==1 and len(v)==2*n+1
            if sum(i*b for i,b in enumerate(v,1))!=0:continue
            count+=1;windowcount+=1
            shorter=any(sum(v[:d])==1 and sum(i*b for i,b in enumerate(v[:d],1))==0 for d in range(1,len(v)))
            if not shorter:
                minimum+=1
                assert params[0]=='internal' and params[-1]==0,(n,params,w)
                _,j,z,extra,left,right=params
                assert (extra==3 and n==6*j-2*z+1) or (extra==2 and n==4*j-2*z+1)
            for buffer in ((-1,-1,-1),(1,-1,-1,-1),(1,1,-1,-1,-1)):
                e=tuple(reversed(v))+(1,)+buffer
                r=analyze(e)
                if isinstance(r,dict):
                    print('REFUTED_STRUCTURED='+json.dumps({'n':n,'parameters':params,**r}),flush=True)
                    print('STOP: centered one-SS map failed; no offset repair')
                    return
            if not shorter and len(saved)<32:saved.append(v)
        print(('GAP_DISCOVERY' if n<=32 else 'GAP_HOLDOUT')+'='+json.dumps(
            {'S_count':n,'P2_windows':count,'minimum_windows':minimum}),flush=True)
    for v,w in itertools.product(saved,saved):
        e=tuple(reversed(v))+(1,-1,-1,-1)+tuple(reversed(w))+(1,-1,-1,-1)
        r=analyze(e)
        if isinstance(r,dict):
            print('REFUTED_PAIR='+json.dumps(r),flush=True)
            print('STOP: centered one-SS map failed; no offset repair')
            return
    print('PASS: finite centered map tests; general injection remains unproved')


if __name__=='__main__':
    main()
