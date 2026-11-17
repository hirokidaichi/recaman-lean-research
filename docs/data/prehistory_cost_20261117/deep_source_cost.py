"""Distinct deep-valley correction, replacing unit loops with signed squares."""
import hashlib,json,math,sys,time
from pathlib import Path
from source_cost import profile,orders,evaluate
BASE=Path(__file__).resolve().parent
START=time.process_time();LIMIT=12000

def correction(delta,c):
    out=[];left=abs(delta)
    while left:
        k=math.isqrt(left)
        if delta>0:k=min(k,-c)
        assert k>=1
        out.append(('A'*k+'S'*k) if delta>0 else ('S'*k+'A'*k))
        left-=k*k
    w=''.join(out)
    assert profile(w)[0][-1]==0 and profile(w)[1][-1]==delta
    return w

def build(M,order):
    x='AAAA';c0=-3
    for j,off in order:
        c=-3 if off==5 else -2
        goal=-24*j-15 if off==5 else -16*j-11
        y=('A'*(c0-c) if c<c0 else 'S'*(c-c0))+x
        corr=correction(goal-profile(y)[1][-1],c)
        if len(corr)+len(y)>LIMIT:return None
        x=corr+y;c0=c
        assert profile(x)[1][-1]==goal
        if time.process_time()-START>1.6:raise RuntimeError('deep worker1.6CPU cooperative stop')
    x='A'*(c0+3)+x
    H,B=profile(x);D=3*len(x)-B[-1]
    assert H[-1]==4 and D>=2
    m=max(2,math.isqrt(D+7))
    while True:
        E=m*m-7-D
        if E>=0:
            b=(3*E)%5;a=(E-7*b)//5
            if a>=0:break
        m+=1
    padding=m+1
    p='S'+'A'*(m+1)+'S'*(m+3)+'AS'*a+'SA'*b+x
    assert (profile(p)[0][-1],profile(p)[1][-1])==(1,0)
    w='S'*padding+p+'ASSSSAAA'*M+'A';T=padding+len(p)
    if len(w)>LIMIT:return None
    return w,padding+1,T,{'D':D,'hill':m,'seed_length':len(x),'signed_square_correction':True}

mode=sys.argv[1]
values,count,seed=([4,5],32,174511) if mode=='discovery' else ([6,8],16,178611)
rows=[]
for M in values:
    best=None;valid=skipped=0
    for order in orders(M,count,seed):
        built=build(M,order)
        if built is None:skipped+=1;continue
        w,h,T,meta=built;r=evaluate(w,h,T,M);valid+=1;r.update(order=order,construction=meta)
        if best is None or (r['low_free'],r['length'])<(best['low_free'],best['length']):best=r
        if r['low_free']<M:break
    filename='deep-'+mode+'-best-M'+str(M)+'.json'
    if best:
        (BASE/filename).write_text(json.dumps(best,indent=2)+'\n')
        row={k:best[k] for k in ['M','h','T','length','low_free','prehistory_free','min_height','word_sha256']}
        row.update(certificate=filename,accepted=valid,skipped=skipped,extra_depth=-best['min_height']-best['h'],counterexample=best['low_free']<M)
    else:row={'M':M,'accepted':valid,'skipped':skipped,'certificate':None,'counterexample':False}
    rows.append(row);print(json.dumps(row),flush=True)
    if row['counterexample']:break
summary={'mode':mode,'M':values,'orders':count,'seed':seed,'length_cap':LIMIT,'rows':rows,'cpu_seconds':time.process_time()-START}
(BASE/('deep-'+mode+'-summary.json')).write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary),flush=True)
