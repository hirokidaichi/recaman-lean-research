"""New full S-chronology/seed predicate on OLD E758 parameters; no fresh orbit claim."""
import json,sys
from pathlib import Path
cfg=json.loads(Path(sys.argv[1]).read_text());W='SSAAASSSSAAAASAS'
def verify(w):
 H=[0];B=[0];states={(0,0):[0]};Akeys={};free=[];collisions=[]
 for q,c in enumerate(w):
  h=H[-1];a=B[-1]
  if c=='A':
   key=(h-1,a-q*(h-1))
   if key not in states:free.append(q)
   Akeys.setdefault(key,[]).append(q)
  nh=h+(1 if c=='A'else -1);nb=a+nh;v=q+1;key=(nh,nb-v*nh)
  if c=='S':
   collisions += [('I',u,v)for u in states.get(key,[])]+[('II',u,v)for u in Akeys.get(key,[])]
  states.setdefault(key,[]).append(v);H.append(nh);B.append(nb)
 assert not collisions,(w,collisions[:4])
 n=len(w)+1;b=100*n*n;x=100*(b+n)*n
 seed={0,x}|{x+(b+q+1)*(H[q]-1)-B[q]for q in free}
 assert min(seed)>=0
 cur=x;seen=set(seed)
 for q,c in enumerate(w):
  nclock=b+q+1;cand=cur-nclock;A=cand<=0 or cand in seen
  assert A==(c=='A'),(q,c,cand)
  cur=cur+nclock if A else cand;seen.add(cur);assert cur>0
 return dict(length=len(w),original_free=len(free),coherent=True,all_I_II_collisions=[],actual_seed_replay_steps=len(w),seed_count=len(seed),base=b,current=x,seed=sorted(seed))
rows=[]
for label,params in [('old_discovery_parameters',cfg['old_discovery_parameters']),('old_parameter_controls_NEW_predicate',cfg['old_parameter_controls'])]:
 for N,z,U in params:
  assert U*U==z*z+N*(16*z-10)
  f='SS'+'A'*(U+z)+W*N+'S'*(z-1)+'A';g='S'*(U-2)+f
  rows.append(dict(label=label,N=N,z=z,U=U,r=U-2,f=verify(f),g=verify(g)))
prefix=[]
for N in cfg['period_counts']:
 r=verify(W*N);r['N']=N;prefix.append(r)
 # Independent direct numerical identity at the deepest S of every copy.
 for b,x in cfg['numeric_identity_parameters']:
  cur=x
  for q,c in enumerate(W*N):
   cur+=(1 if c=='A'else -1)*(b+q+1)
   if q%16==8:assert cur==x-3*b-38*(q//16)-21
H=[0];B=[0]
for c in W:H.append(H[-1]+(1 if c=='A'else -1));B.append(B[-1]+H[-1])
cert=[]
for h in [0,-1,-2,-3,-4]:
 cert.append(dict(h=h,per_copy_delta=-10-16*h,S_landings=[dict(phase=v,key=B[v]-v*h)for v in range(1,17)if W[v-1]=='S'and H[v]==h],prior_states=[dict(phase=u,key=B[u]-u*h)for u in range(16)if H[u]==h],prior_A_candidates=[dict(phase=q,key=B[q]-q*h)for q in range(16)if W[q]=='A'and H[q]-1==h]))
out=dict(PASS=True,rows=rows,period_controls=prefix,phase_key_certificate=cert,scope='NEW all-S chronology/actual finite seed predicate on OLD histories. No canonical reachability or common infinite State.')
Path(sys.argv[2]).write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(PASS=True,family_pairs=len(rows),total_actual_replay_steps=sum(r['f']['length']+r['g']['length']for r in rows)+sum(r['length']for r in prefix),period_controls=cfg['period_counts'],phase_keys=cert)))
