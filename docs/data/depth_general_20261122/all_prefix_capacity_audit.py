"""Independent direct-window audit of endpoint/initial-side boundary and capacity."""
from collections import Counter,defaultdict
from itertools import product
import json,time
t0=time.process_time();counts=Counter()
for L in range(10):
 for w in product([-1,1],repeat=L):
  H=[sum(w[:i]) for i in range(L+1)];B=[sum(H[1:i+1]) for i in range(L+1)]
  a=Counter(H[q] for q in range(L) if w[q]==1);free=[];keys=defaultdict(set);visits=Counter(H)
  for q,e in enumerate(w):
   if e!=1:continue
   actual=False
   for u in range(q):
    seg=w[u:q]
    if sum(seg)==1 and sum(sum(seg[:i]) for i in range(1,len(seg)+1))==0:actual=True
   if not actual:
    free.append(q);keys[H[q]].add((H[q]-1,(q+1)*(H[q]-1)-B[q]))
  for v in range(min(H)-1,max(H)+2):
   expected=a[v]+a[v-1]+int(H[-1]<=v)-int(v>0)
   assert visits[v]==expected;counts['full_boundary_identity_checks']+=1
  for margin in [0,1]:
   ell=min(H)-margin
   for R in range(ell,max(H)+2):
    W=R-ell;K=sum(len(keys[r]) for r in range(ell,R+1));F=sum(H[q]<=R for q in free)
    b=[K,K]
    for j in range(2,W+1):b.append((K+1+b[-1]+b[-2])*(1+b[-2]))
    assert all(a[ell+j]<=b[j] for j in range(W+1))
    assert F==K if W<=1 else F<=K*(1+b[W-2])
    A=sum(a[r] for r in range(ell,R+1));V=sum(visits[r] for r in range(ell,R+1))
    assert A<=sum(b[:W+1]) and V<=2*sum(b[:W+1])+W+1
    counts['arbitrary_endpoint_floor_cut_capacity_checks']+=1
  counts['words']+=1;counts['discovery' if L<=6 else 'parameter_controls']+=1
  if counts['words']%128==0 and time.process_time()-t0>.65:raise TimeoutError('independent boundary audit cap, no extension')
negative={'word':'AA','level_v':1,'actual_visits':1,'uncorrected_a_v_plus_a_vminus1_plus_end':2,'initial_side_correction':-1}
print(json.dumps({'all_pass':True,'counts':dict(counts),'positive_level_exact_equality_negative':negative,'worker_internal_cpu_seconds':time.process_time()-t0},indent=2))
