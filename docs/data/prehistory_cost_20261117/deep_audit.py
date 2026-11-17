"""Reuse only the independent verifier functions, never the constructor."""
from pathlib import Path
import json,time,hashlib
P=Path(__file__).resolve().parent
ns={}
exec(compile((P/'audit.py').read_text().split('\nchecked=[]')[0],str(P/'audit.py'),'exec'),ns)
started=time.process_time()
for name in ['deep-discovery-best-M4.json','deep-discovery-best-M5.json','deep-holdout-best-M6.json','deep-holdout-best-M8.json']:
    r=json.loads((P/name).read_text());w=r['word'];h,T,M=r['h'],r['T'],r['M']
    H,src,free,low=ns['domain'](w,h,T,M)
    assert low==r['low_free_clocks'] and len(free)==r['total_free']
    assert all(src[row['q']]==row['sources'] for row in r['external'])
    assert min(H[:T+1])<=-h-4 # the earlier floor theorem genuinely does not apply
    selected=sorted(src[T+8*j+5][0] for j in range(M))
    assert all(v-u>=12 and (v-u)%4==0 for u,v in zip(selected,selected[1:]))
    assert T>=h+12*M-6
    print(json.dumps({'certificate':name,'M':M,'low_free':len(low),'extra_depth':-min(H[:T+1])-h,'all_sources_reverse_checked':True,'counterexample':len(low)<M}),flush=True)

# New consequence of the floor lemma on already-audited shallow certificates.
for name in ['discovery-best-M3.json','discovery-best-M4.json','holdout-best-M5.json','holdout-best-M7.json']:
    r=json.loads((P/name).read_text());w=r['word'];h=r['h'];M=r['M']
    assert r['min_height']>=-h-3
    selected=[row['sources'][0] for row in r['external'][::2]]
    image=[u if w[u]=='A' else u+1 for u in selected]
    assert len(set(image))==M and set(image)<=set(r['low_free_clocks'])
    print(json.dumps({'floor_certificate':name,'M':M,'explicit_distinct_free_image':image}),flush=True)
print(json.dumps({'status':'pass','cpu_seconds':time.process_time()-started,'scope':'exact selected certificates, no general finite-absence claim'}))
