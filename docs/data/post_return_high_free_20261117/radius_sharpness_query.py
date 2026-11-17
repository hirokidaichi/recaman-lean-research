import json,sys,time
from pathlib import Path
P=Path(__file__).resolve().parent;split=sys.argv[1];start=time.process_time()
pairs=[(0,1),(1,0),(3,5),(4,2),(7,3)] if split=='discovery' else [(2,7),(8,4),(11,6)]
assert split in ('discovery','holdout');rows=[]
for p,b in pairs:
 N=p+b
 variants=[('general','S'*N+'A'*N+'AS'*(N*N-1)+'A')]
 if b>=2:
  C=p*p-b*b+1;D=2*b-3;k=max(0,(C+D-1)//D);l=k*D-C
  variants.append(('last_minimum','A'*p+'S'*(p+b)+'A'+'AS'*k+'A'*(b-1)+'AS'*l+'A'))
 for name,w0 in variants:
  h=(w0+'A').count('A')+1;w='S'*h+w0+'A';u=h;v=h+2*p+b;q=h+len(w0)
  H=[0];B=[0];A=E=S=0;sources={}
  for t,x in enumerate(w):
   if x=='A':
    A+=1;ss=[z for z in range(t) if H[t]==H[z]+1 and B[t]-B[z]==(t-z)*H[z]]
    sources[str(t)]=ss;E+=bool(ss)
   else:S+=1
   assert E+1<=S
   H.append(H[-1]+(1 if x=='A' else -1));B.append(B[-1]+H[-1])
  assert u in sources[str(q)] and v-u==2*p+b and w[:v].count('A')==p
  assert H[q]==H[v]+b+1
  if name=='last_minimum':assert H[v]==min(H) and all(z>H[v] for z in H[v+1:])
  rows.append(dict(p=p,b=b,variant=name,word=w,u=u,v=v,q=q,all_target_sources=sources[str(q)],prefix_positive=True))
  if time.process_time()-start>2.5:raise RuntimeError('cooperative2.5CPU cap')
out=dict(split=split,cases=len(rows),result='PASS',cpu_seconds=time.process_time()-start,evidence='COMPUTED illustrations of paper sharpness family')
(P/f'radius-sharpness-{split}-cases.json').write_text(json.dumps(rows,indent=2)+'\n')
(P/f'radius-sharpness-{split}-summary.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
