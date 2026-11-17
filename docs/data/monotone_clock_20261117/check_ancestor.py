"""Attack the already-frozen H-20261117-01 map on existing certificates only."""
from pathlib import Path
from collections import defaultdict
import hashlib,json,time

started=time.process_time()
prior=Path('docs/data/depth_general_20261115/two_free_plateau_certificate.py')
ns={}
# Reuse only the recorded constructor, with its existing cooperative guard.
exec(compile(prior.read_text().split('\nfor D in [')[0],str(prior),'exec'),ns)

def check(label,w,h):
    H=[0];B=[0]
    for c in w:
        H.append(H[-1]+(1 if c=='A' else -1));B.append(B[-1]+H[-1])
    idx=defaultdict(list);src={};free=[];S=E=0
    for t,c in enumerate(w):
        if c=='S':S+=1
        else:
            src[t]=idx[(H[t]-1,B[t]-t*(H[t]-1))].copy()
            if src[t]:E+=1
            else:free.append(t)
        assert E+1<=S
        idx[(H[t],B[t]-t*H[t])].append(t)
    assert w[:h]=='S'*h
    low=[q for q in free if H[q]<=H[h]+1]
    T=[t for t in range(h,len(w)) if w[t]=='A' and src[t] and all(s<h for s in src[t]) and H[t]==H[h]+2]
    rows=[]
    for t in T:
        a=max(q for q in range(t) if w[q]=='A' and H[q]==H[h])
        b=max(q for q in range(t) if w[q]=='A' and H[q]==H[h]+1)
        short=lambda q: h+3<=q and w[q-3:q+1]=='SAAA'
        psi=b if short(a) else a
        assert not short(psi) and a<b<t
        if not src[psi]:u=None;rho=psi
        else:
            assert all(s>=h for s in src[psi])
            u=max(src[psi]);available=[q for q in low if q<=u]
            rho=max(available) if available else min(q for q in low if q<psi)
        # Independent literal full-source scan for the target and selected low image.
        for q in (t,psi):
            literal=[]
            for s in range(q):
                mass=sum(1 if c=='A' else -1 for c in w[s:q])
                area=sum((q-i)*(1 if w[i]=='A' else -1) for i in range(s,q))
                if mass==1 and area==0:literal.append(s)
            assert literal==src[q]
        rows.append({'target':t,'sources':src[t],'a':a,'b':b,'psi':psi,'psi_sources':src[psi],'latest_source':u,'rho':rho})
    collisions=[(r['target'],s['target'],r['rho']) for i,r in enumerate(rows) for s in rows[i+1:] if r['rho']==s['rho']]
    result={'label':label,'word':w,'h':h,'length':len(w),'word_sha256':hashlib.sha256(w.encode()).hexdigest(),'E':E,'S':S,'free':free,'low_free':low,'targets':rows,'collisions':collisions}
    print(json.dumps(result),flush=True)
    return bool(collisions)

P='S'+'A'*11+'S'*13+'S'*3+'A'*3+'S'*3+'A'*4+'S'+'A'+'S'*4+'A'*7
collision=check('E711','S'*11+P+'A'+'S'*4+'A'*3+'A',12)
for N in [1,2,3]:
    if collision:break
    w,source,cut,T,seeds,meta=ns['construct'](N)
    collision=check('E715-N'+str(N),w,cut)
print(json.dumps({'collision_found':collision,'cpu_seconds':time.process_time()-started,'scope':'fixed known certificates, no expanded search or holdout claim'}))
