"""New all-level class-load/visit/clock predicates on arbitrary raw sign words."""
from itertools import product
from collections import Counter,defaultdict
import json,time
start=time.process_time();counts=Counter();example=None
for L in range(12):
 for w in product([-1,1],repeat=L):
  H=[0];B=[0];O={(0,0)};a=Counter();f=Counter();classes=defaultdict(set);uses=Counter();allclasses=defaultdict(set)
  for q,e in enumerate(w):
   r=H[-1];c=(r-1,(q+1)*(r-1)-B[-1])
   if e==1:
    a[r]+=1;uses[(r,c)]+=1;allclasses[r].add(c)
    if c not in O:f[r]+=1;classes[r].add(c)
   H.append(r+e);B.append(B[-1]+H[-1]);O.add((H[-1],(q+2)*H[-1]-B[-1]))
  for (r,c),load in uses.items():
   assert load<=1+a[r-2];counts['pair_load_checks']+=1
  visits=Counter(H)
  for r in range(min(H),min(0,H[-1])+1):
   k=len(classes[r]);N=visits[r-1]
   assert N==a[r-1]+a[r-2]
   assert len(allclasses[r])<=k+N
   assert a[r]<=(k+a[r-1]+a[r-2])*(1+a[r-2])
   assert f[r]<=k*(1+a[r-2])
   counts['source_visit_capacity_checks']+=1
  ell=min(H)
  for r in [ell,ell+1]:
   assert a[r]==f[r]==len(classes[r]);counts['bottom_singleton_checks']+=1
  h=2-H[-1]
  if h>=1 and L>=h and all(e==-1 for e in w[:h]):
   D=-h-ell;R=1-h;K=sum(len(classes[r]) for r in range(ell,R+1));F=sum(f[r] for r in range(ell,R+1))
   assert D>=0 and K>=2
   b=[K,K]
   for j in range(2,D+2):b.append((K+b[-1]+b[-2])*(1+b[-2]))
   for j in range(D+2):assert a[ell+j]<=b[j]
   assert F==K if D==0 else F<=K*(1+b[D-1])
   counts['full_main_domain_words']+=1
   if D>=2:example={'word':''.join('A' if e==1 else 'S' for e in w),'h':h,'D':D,'K':K,'F':F,'bound':K*(1+b[D-1])}
  counts['raw_words']+=1
  counts['discovery_words' if L<=8 else 'parameter_control_words']+=1
  if counts['raw_words']%128==0 and time.process_time()-start>.65:raise TimeoutError('partial fixed resource, no extension')
print(json.dumps({'all_pass':True,'counts':dict(counts),'last_nontrivial_example':example,'worker_internal_cpu_seconds':time.process_time()-start},indent=2))
