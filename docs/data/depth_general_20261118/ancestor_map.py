"""Frozen new-map falsifier. Historical words are discovery controls only."""
from pathlib import Path
import ast, hashlib, itertools, json, sys, time

ROOT=Path(__file__).resolve().parents[3]
OUT=Path(__file__).resolve().parent
START=time.process_time()

def profile(w,h):
    H=[0];B=[0];bank={};sources=[];free=[];positive=True;S=E=0
    for q,ch in enumerate(w):
        ss=list(bank.get((H[q]-1,B[q]-q*(H[q]-1)),[])) if ch=='A' else []
        sources.append(ss)
        if ch=='A':
            E+=bool(ss)
            if not ss:free.append(q)
        else:S+=1
        positive=positive and E+1<=S
        bank.setdefault((H[q],B[q]-q*H[q]),[]).append(q)
        H.append(H[-1]+(1 if ch=='A' else -1));B.append(B[-1]+H[-1])
    if not positive:return None
    low=[q for q in free if H[q]<=H[h]+1]
    targets=[q for q,ch in enumerate(w) if q>=h and ch=='A' and sources[q]
             and all(u<h for u in sources[q]) and H[q]==H[h]+2]
    rows=[]
    for t in targets:
        a=max(q for q in range(h,t) if w[q]=='A' and H[q]==H[h])
        b=max(q for q in range(h,t) if w[q]=='A' and H[q]==H[h]+1)
        short=lambda q:q>=h+3 and w[q-3:q]=='SAA' and w[q]=='A'
        psi=b if short(a) else a
        assert not short(psi)
        u=None
        if not sources[psi]:rho=psi;branch='free-image'
        else:
            assert all(u>=h for u in sources[psi])
            u=max(sources[psi]);old=[q for q in low if q<=u]
            fallback=[q for q in low if q<psi]
            if old:rho=max(old);branch='latest-before-source'
            elif fallback:rho=min(fallback);branch='earliest-fallback'
            else:rho=None;branch='undefined-fallback'
        rows.append(dict(target=t,target_sources=sources[t],a=a,b=b,psi=psi,
                         psi_sources=sources[psi],latest_source=u,rho=rho,branch=branch))
    if any(r['rho'] is None for r in rows):kind='undefined'
    elif len({r['rho'] for r in rows})<len(rows):kind='collision'
    else:kind='no-counter'
    result=dict(kind=kind,word=w,h=h,length=len(w),positive=positive,D=len(targets),
                F_low=len(low),low_free=low,rows=rows)
    if kind!='no-counter':result.update(H=H,B=B,all_free=free,all_sources={q:ss for q,ss in enumerate(sources) if ss})
    return result

def old_two_target():
    P='S'+'A'*11+'S'*16+'A'*3+'S'*3+'A'*4+'SA'+'S'*4+'A'*7
    return 'S'*11+P+'A'+'S'*4+'A'*4,12

def bounded_control(N):
    # Import only the frozen mathematical constructor definitions, never its jobs.
    p=ROOT/'docs/data/depth_general_20261115/two_free_plateau_certificate.py'
    tree=ast.parse(p.read_text())
    keep=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in {'profile','mass_area','construct'}]
    env={'guard':lambda:None,'math':__import__('math')}
    exec(compile(ast.Module(body=keep,type_ignores=[]),str(p),'exec'),env)
    w,_,cut,_,_,_=env['construct'](N)
    return w,cut

def main():
    mode=sys.argv[1];checked=targets=0;best=0;counter=None
    controls=[old_two_target(),bounded_control(2)] if mode=='discovery' else [bounded_control(3)]
    for w,h in controls:
        r=profile(w,h);checked+=1
        assert r is not None
        targets+=r['D'];best=max(best,r['D'])
        if r['kind']!='no-counter':counter=r;break
    if counter is None:
        hs=(1,2,3) if mode=='discovery' else (4,7,12)
        maxlen=12 if mode=='discovery' else 10
        for h in hs:
            for length in range(maxlen+1):
                for signs in itertools.product('SA',repeat=length):
                    r=profile('S'*h+''.join(signs),h);checked+=1
                    if r is None:continue
                    targets+=r['D'];best=max(best,r['D'])
                    if r['kind']!='no-counter':counter=r;break
                if counter:break
            if counter:break
    result={'mode':mode,'checked':checked,'target_occurrences':targets,'max_D':best,
            'counter':counter,'worker_algorithm_cpu_seconds':time.process_time()-START,
            'scope':'new fixed-map falsification only; no D<=F/C1 counter claimed'}
    (OUT/('ancestor-'+mode+'-summary.json')).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='counter'},indent=2))
    if counter:print(json.dumps({k:counter[k] for k in ['kind','h','length','D','F_low','rows']},indent=2))

if __name__=='__main__':main()
