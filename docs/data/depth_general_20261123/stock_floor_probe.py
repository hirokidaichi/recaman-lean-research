"""NEW old-stock discount, arbitrary original cuts, primitive area and all-depth audit."""
import json,time
from collections import Counter
t0=time.process_time();counts=Counter();equalities=[]
def run(x,b,stock,Q):
 X=[x];H=[0];V=[set(stock)];word=[]
 for q in range(Q):
  n=b+q+1;c=X[-1]-n;e=-1 if c>0 and c not in V[-1] else 1
  y=X[-1]+e*n;assert y>0
  word.append(e);X.append(y);H.append(H[-1]+e);V.append(V[-1]|{y})
 return X,H,V,word
profiles=[]
for x in range(1,6):
 for b in [0,1,3,7]:
  for mask in range(2**(x-1)):
   for extras in [[],[x+2,x+5],list(range(x+1,x+5))]:
    stock={0,x,*extras,*[y for y in range(1,x) if mask>>(y-1)&1]}
    profiles.append(('discovery',x,b,stock,18))
for x in [6,9]:
 for b in [2,5]:
  for mask in [0,1,sum(1<<i for i in range(0,x-1,2)),2**(x-1)-1]:
   for extras in [[],[x+2,x+5],list(range(x+1,x+5))]:
    profiles.append(('parameter_holdout',x,b,{0,x,*extras,*[y for y in range(1,x) if mask>>(y-1)&1]},22))
for label,x,b,stock,Q in profiles:
 X,H,V,word=run(x,b,stock,Q);counts[label+'_states']+=1
 for T in range(1,Q+1):
  for c in range(T):
   floor=H[c]
   if H[T]<=floor or min(H[c:T+1])<floor:continue
   visits=[i for i in range(c,T+1) if H[i]==floor];v=visits[-1];cp=v+1
   y=X[c];z=X[v];K=sum(0<s<y for s in V[c]);N=sum(z<=s<y for s in V[c]);t=v-c
   area=0
   for p,q in zip(visits,visits[1:]):
    L=q-p;A=sum(h-floor for h in H[p+1:q+1]);assert L%2==0 and A>=3*(L//2)-2
    assert X[p]-X[q]==A and X[q] not in V[c]
    area+=A;counts['primitive_excursions']+=1
   m=len(visits)-1;assert area==y-z and m<=y-z-N
   assert 3*t+6*z+4*N<=6*y
   P=b+c+2*y;Pn=b+cp+2*X[cp]
   assert Pn<=3*P-1-4*K
   assert cp<=c+2*y-1-(4*K+2)//3
   counts['all_cut_stock_step_checks']+=1;counts['K_positive']+=K>0;counts['nonempty_return']+=t>0
   if K>0 and Pn==3*P-1-4*K and len(equalities)<6:equalities.append({'x':x,'b':b,'stock':sorted(stock),'cut':c,'end':T,'next_cut':cp,'K':K,'P':P,'nextP':Pn})
   cuts=[c];Ps=[P];Ks=[];weighted=0
   for level in range(floor+1,H[T]+1):
    vi=max(i for i in range(cuts[-1],T+1) if H[i]==level-1);ci=vi+1
    ki=sum(0<s<X[cuts[-1]] for s in V[cuts[-1]])
    if len(cuts)>1:assert ki>=1
    pi=b+ci+2*X[ci];assert pi<=3*Ps[-1]-1-4*ki
    weighted=3*weighted+ki;cuts.append(ci);Ps.append(pi);Ks.append(ki);j=len(Ks)
    assert pi<=3**j*P-(3**j-1)//2-4*weighted
    if j==2:assert pi<=9*P-8-12*Ks[0]
    counts['iterated_stock_checks']+=1
 if counts[label+'_states']%16==0 and time.process_time()-t0>.65:
  print(json.dumps({'all_completed_checks_pass':True,'range_complete':False,'stop':'SOFT_CPU_NO_EXTENSION','counts':dict(counts),'equalities':equalities,'worker_internal_cpu_seconds':time.process_time()-t0},indent=2));raise SystemExit(0)
# Critical negative: future learned stock cannot be charged at the old cut.
X,H,V,w=run(1,7,{0,1},16);c=1;v=15;cp=16;Kold=sum(0<s<X[c] for s in V[c]);Kfuture=sum(0<s<X[c] for s in V[v]);P=7+c+2*X[c];Pn=7+cp+2*X[cp]
assert (Kold,Kfuture,P,Pn)==(1,8,26,73) and Pn>3*P-1-4*Kfuture
print(json.dumps({'all_pass':True,'range_complete':True,'counts':dict(counts),'equalities':equalities,'future_stock_negative':{'oldK':Kold,'illegal_futureK':Kfuture,'P':P,'actual_nextP':Pn,'invalid_bound':3*P-1-4*Kfuture},'scope':'new exact inequality controls, arbitrary original cuts/full past; finite not proof','worker_internal_cpu_seconds':time.process_time()-t0},indent=2))
