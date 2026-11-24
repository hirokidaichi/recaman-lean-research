"""NEW packing inequality and old-S/positive sharp-family lift; one frozen worker."""
from itertools import product
from collections import Counter
import json,time
t0=time.process_time();stats=Counter();lift_records=[]
def dyck(n,h=0,word=()):
 if n==0:
  if h==0:yield word
  return
 if h<n:yield from dyck(n-1,h+1,word+(1,))
 if h>0:yield from dyck(n-1,h-1,word+(-1,))
for l in range(1,10):
 for inner in dyck(2*l-2):
  w=(1,)+inner+(-1,);H=[sum(w[:i]) for i in range(len(w)+1)];A=sum(H[1:]);assert A>=3*l-2 and A<=l*l and A%2==l%2
  assert A not in [2,3,5,6,8,11]
  block=A-1;p=(block+2)//3 if block else 0
  assert 5*block>=13*p;stats['primitive_Dyck_packing_checks']+=1
def actual(x,b,stock,Q):
 X=[x];H=[0];seen=set(stock)
 for q in range(Q):
  n=b+q+1;c=X[-1]-n;e=-1 if c>0 and c not in seen else 1
  y=X[-1]+e*n;seen.add(y);X.append(y);H.append(H[-1]+e)
 return X,H
for label,xs,bs in [('discovery',range(1,9),[0,1,4]),('parameter_holdout',[11,16,23],[3,9])]:
 for x in xs:
  masks=range(2**(x-1)) if x<=8 else [0,1,2**(x-1)-1,sum(1<<i for i in range(2,x-1,3))]
  for b in bs:
   for mask in masks:
    V={0,x,*[y for y in range(1,x) if mask>>(y-1)&1]};X,H=actual(x,b,V,22);chosen=[]
    for y in sorted(v for v in V if 3<=v<x):
     if not chosen or y-chosen[-1]>=3:chosen.append(y)
    p=len(chosen);K=sum(0<y<x for y in V);d=max(K,(13*p+4)//5)
    for Q in range(1,23):
     if H[Q]<=0 or min(H[:Q+1])<0:continue
     v=max(i for i,h in enumerate(H[:Q+1]) if h==0);cp=v+1;P=b+2*x;Pn=b+cp+2*X[cp]
     assert Pn<=3*P-1-4*d and cp<=2*x-1-(4*d+2)//3
     returns=sum(h==0 for h in H[1:v+1]);assert returns<=x-1-d
     stats[label+'_stock_checks']+=1;stats['packing_strictly_stronger']+=d>K;stats['nonempty_return_packing_gain']+=v>0 and d>K
for label,cases in [('discovery',[(1,2,5),(3,2,7),(7,3,9),(5,5,11)]),('parameter_holdout',[(2,4,17),(11,7,29),(19,9,43)])]:
 for x,h,b in cases:
  base=b-h;I=x+h*b-h*(h-1)//2;stock={0,I,*range(1,x)};w=[-1]*h+[1]*3+[-1]*2+[z for j in range(b-4) for z in [1,-1]]+[1]
  X=[I];H=[0];B=[0];seen=set(stock);sources={};free=[];keys=set();S=E=0;mindef=10**9
  for q,e in enumerate(w):
   n=base+q+1;c=X[-1]-n;got=-1 if c>0 and c not in seen else 1;assert got==e,(x,h,b,q,c)
   if e==1:
    us=[u for u in range(q) if H[q]==H[u]+1 and B[q]-B[u]==(q-u)*H[u]];sources[q]=us
    if us:E+=1
    else:free.append(q);keys.add((H[q]-1,(q+1)*(H[q]-1)-B[q]))
   else:S+=1
   mindef=min(mindef,S-E);y=X[-1]+e*n;assert y>0
   seen.add(y);X.append(y);H.append(H[-1]+e);B.append(B[-1]+H[-1])
  assert mindef>=1 and H[-1]==2-h and min(H)==-h
  assert {q:us for q,us in sources.items() if us}=={h+2:[h-1]}
  assert len(free)==len(keys)==b-1 and all(H[q]<=1-h for q in free)
  q0=h;c1=h+1;c2=h+2*b-2;Ps=[b+2*x,base+c1+2*X[c1],base+c2+2*X[c2]]
  assert X[q0]==x and Ps==[b+2*x,3*b+2*x+3,9*b+2*x-4]
  lift_records.append({'label':label,'x':x,'h':h,'b_at_retained_cut':b,'initial_base':base,'complete_initial_stock':sorted(stock),'initial_current':I,'original_actual':{str(q):us for q,us in sources.items() if us},'LOW_free_classes':len(keys),'original_positive_min':mindef,'D':0,'P0_P1_P2':Ps,'original_floor_cuts':[q0,c1,c2]})
print(json.dumps({'all_pass':True,'counts':dict(stats),'full_old_S_lift':lift_records,'scope':'new packing and complete old-history numerical sharpness predicates, finite COMPUTED only; paper all-parameter proof separate','worker_internal_cpu_seconds':time.process_time()-t0},indent=2))
