"""New RAW class-singleton predicate on the proof's critical recovery grammar."""
from itertools import product
import json,time
t0=time.process_time();rows=[];counts={'discovery':0,'parameter_controls':0};eligible={'discovery':0,'parameter_controls':0};witness=None

def inspect(w,h):
 H=[0];B=[0];out={(0,0)};free=[];pairs=[];allc=[]
 for q,e in enumerate(w):
  c=(H[q]-1,(q+1)*(H[q]-1)-B[q])
  if e==1:
   allc.append((q,c))
   if c not in out:
    free.append(q)
    if H[q]<=1-h:pairs.append((q,c))
  H.append(H[-1]+e);B.append(B[-1]+H[-1]);out.add((H[-1],(q+2)*H[-1]-B[-1]))
 ell=min(H);bottom=[(q,c) for q,c in allc if H[q]<=ell+1]
 assert all(q in free for q,c in bottom)
 assert len({c for q,c in bottom})==len(bottom)
 K=len({c for q,c in pairs});F=len(pairs);D=max(0,-h-ell)
 return {'h':h,'K':K,'F':F,'D':D,'word':''.join('A' if e==1 else 'S' for e in w),'low_pairs':pairs,'return':H[-1]}

def highs(n):
 for w in product([1,-1],repeat=2*n):
  hs=[sum(w[:j]) for j in range(1,len(w)+1)]
  if hs[-1]==0 and min(hs[:-1])>0:
   area=sum(hs)
   assert (len(w)==2 and area==1) or (len(w)>=4 and area>=4)
   yield list(w)

for label,heads,ns,ds,ls,js in [('discovery',[2,7],range(1,4),range(5),range(2),range(3)),('parameter_controls',[11,15],range(1,6),range(7),range(3),range(4))]:
 for h in heads:
  for n in ns:
   for high in highs(n):
    for d in ds:
     for lower in ls:
      if d<2 and lower:continue
      for j in js:
       recovery=([1]*d if d<2 else [1,1]+[1,-1]*lower+[1]*(d-2))
       w=[-1]*h+high+[-1]*d+recovery+[1,-1]*j+[1,1]
       r=inspect(w,h);counts[label]+=1
       assert r['return']==2-h
       if r['K']<=3:
        eligible[label]+=1
        if not (r['D']<=1 and r['F']==r['K']):witness=r;break
       if time.process_time()-t0>.65:raise TimeoutError('frozen proof-grammar budget, no extension')
      if witness:break
     if witness:break
    if witness:break
   if witness:break
  if witness:break
 if witness:break
negative=inspect([-1]*3+[1]*4,1)
assert negative['K']==3 and negative['F']==3 and negative['D']==2
print(json.dumps({'counts':counts,'nonvacuous_K_le_3':eligible,'counter':witness,'nonmaximal_head_negative':negative,'worker_internal_cpu_seconds':time.process_time()-t0},indent=2))
