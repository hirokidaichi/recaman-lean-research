import gzip,json,time
from pathlib import Path
P=Path(__file__).resolve().parent;start=time.process_time();checks=[]
for m in (6,8):
 with gzip.open(P/f'g0-m{m}-full.json.gz','rt') as fp:r=json.load(fp)
 w=r['word'];s=r['summary'];H=[0];A=0
 for x in w:H.append(H[-1]+(1 if x=='A' else -1));A+=(x=='A')
 assert H==r['H'] and A<s['h'] and w.startswith('S'*s['h'])
 assert s['R']==next(i for i in range(s['v']+1,len(H)) if H[i]==s['d'])
 assert min(H)==H[s['v']] and all(x>H[s['v']] for x in H[s['v']+1:])
 for q in range(s['R']+m,s['T']):
  mass=area=0;ss=[]
  for u in range(q-1,-1,-1):
   z=1 if w[u]=='A' else -1;mass+=z;area+=(q-u)*z
   if mass==1 and area==0:ss.append(u)
  assert sorted(ss)==r['all_sources'][str(q)] and ss
 for e in (3,4):
  u=s['R']+e;c=H[u];area=sum(x-c for x in H[u+1:s['T']+1])
  assert -area==next(x['offset'] for x in s['keys'] if x['e']==e)
 # The first five A precede any visit below their starting height.
 first=[i for i,x in enumerate(w) if x=='A'][:5]
 assert all(H[i]==min(H[:i+1]) and H[i]<s['d'] for i in first)
 checks.append(dict(m=m,tail_A_all_sources_checked=m,low4_explicitly_false=True))
 if time.process_time()-start>2.5:raise RuntimeError('cooperative2.5CPU cap')
out=dict(result='PASS',cases=checks,cpu_seconds=time.process_time()-start,evidence='COMPUTED independent literal all-source tail audit')
(P/'g0-explicit-audit-summary.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
