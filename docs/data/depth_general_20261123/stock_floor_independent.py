"""Independent signed-word construction, minimal required stock, direct greedy replay."""
from itertools import product
from collections import Counter
import json,time
t0=time.process_time();counts=Counter()
for label,params,lengths in [('discovery',[(0,1),(1,2),(3,5)],range(1,8)),('parameter_holdout',[(2,4),(7,9)],range(8,10))]:
 for b,x in params:
  for L in lengths:
   for w in product([-1,1],repeat=L):
    hs=[sum(w[:i]) for i in range(L+1)]
    if min(hs)<0 or hs[-1]<1:continue
    vals=[x+sum(e*(b+j+1) for j,e in enumerate(w[:i])) for i in range(L+1)]
    if min(vals)<1:continue
    stock={0,x};past={x}
    for q,e in enumerate(w):
     cand=vals[q]-(b+q+1)
     if e==1 and cand>0 and cand not in past:stock.add(cand)
     past.add(vals[q+1])
    seen=set(stock);actual=True;snapshots=[set(seen)]
    for q,e in enumerate(w):
     n=b+q+1;candidate=vals[q]-n;got=-1 if candidate>0 and candidate not in seen else 1
     if got!=e:actual=False;break
     seen.add(vals[q+1]);snapshots.append(set(seen))
    if not actual:continue
    K=sum(0<y<x for y in stock);v=max(i for i,h in enumerate(hs) if h==0);cp=v+1;z=vals[v]
    N=sum(z<=y<x for y in stock);visits=[i for i in range(v+1) if hs[i]==0];m=len(visits)-1
    area=sum(vals[p]-vals[q] for p,q in zip(visits,visits[1:]));assert area==x-z
    assert m<=x-z-N and 3*v+6*z+4*N<=6*x
    P=b+2*x;P1=b+cp+2*vals[cp]
    assert P1<=3*P-1-4*K and cp<=2*x-1-(4*K+2)//3
    counts[label+'_actual_words']+=1;counts['nonempty_floor_returns']+=v>0;counts['noncontiguous_old_stock']+=any(y not in stock for y in range(1,x)) and K>0
    if hs[-1]>=2:
     c2=max(i for i,h in enumerate(hs) if i>=cp and h==1)+1;K1=sum(0<y<vals[cp] for y in snapshots[cp]);P2=b+c2+2*vals[c2]
     assert K1>=1 and P2<=3*P1-1-4*K1 and P2<=9*P-8-12*K
     counts['two_floor_checks']+=1
    if counts[label+'_actual_words']%128==0 and time.process_time()-t0>.65:
     print(json.dumps({'all_completed_checks_pass':True,'range_complete':False,'stop':'SOFT_CPU_NO_EXTENSION','counts':dict(counts),'worker_internal_cpu_seconds':time.process_time()-t0},indent=2));raise SystemExit(0)
# Old-state snapshot, freshness, distinct cardinality and value-window are essential.
negative={'without_S_freshness':{'x':5,'b':0,'stock':list(range(6)),'raw_word':'ASA','actual_nextP':17,'claimed_bound':13,'bad_S_lands_on_old4':True},'duplicates_not_distinct':{'x':2,'b':0,'seen_list':[0,1,1,1,2],'word':'A','nextP':7,'valid_K':1,'invalid_K':3},'above_current_not_paid':{'x':1,'b':0,'stock':[0,1,100,101],'word':'A','nextP':5,'valid_K':0,'invalid_all_positive_stock':3}}
for b in [4,7,19]:
 w=[1,1,-1,-1,1];x=5;stock={0,2,3,4,5};value=x;seen=set(stock);vals=[x]
 for q,e in enumerate(w):
  n=b+q+1;c=value-n;assert (-1 if c>0 and c not in seen else 1)==e
  value+=e*n;seen.add(value);vals.append(value)
 assert vals[-1]==b+6 and b+5+2*value==3*(b+10)-1-12
 assert len(w)==2*x-1-(4*3+2)//3;counts['sparse_stock_time_equalities']+=1
print(json.dumps({'all_pass':True,'range_complete':True,'counts':dict(counts),'scope_negatives':negative,'scope':'new inequality on independently constructed actual finite words; no new canonical or LOWfree proof','worker_internal_cpu_seconds':time.process_time()-t0},indent=2))
