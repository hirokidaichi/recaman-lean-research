"""NEW original-positive/return LOW4 numerical clipping family."""
import json,time
t0=time.process_time();out=[]
for label,Ls in [('discovery',[5,7,9]),('unused_parameters',[11,19,31])]:
 for l in Ls:
  b=l*(l-4);x=10*l*l;base=b-2;I=x+2*b-1
  C=lambda k:x+(k-2)*b+k*(k-3)//2
  V0={0,I,*[C(k) for k in range(1,l+1) if k!=3],x-l*l-b-2*l-1,x-l*l-1}
  assert min(v for v in V0 if v)>0
  w='SS'+'A'*l+'S'*l+'AA';X=[I];H=[0];B=[0];stock=set(V0);snapshots=[set(stock)];sources={};free=[];keys=set();S=E=0;mindef=10**9
  for q,e in enumerate(w):
   step=base+q+1;cand=X[-1]-step;got='S' if cand>0 and cand not in stock else 'A';assert got==e,(l,q,e,cand)
   if e=='S':S+=1
   else:
    us=[u for u in range(q) if H[q]==H[u]+1 and B[q]-B[u]==(q-u)*H[u]];sources[q]=us
    if us:E+=1
    elif H[q]<=-1:free.append(q);keys.add((H[q]-1,(q+1)*(H[q]-1)-B[q]))
   mindef=min(mindef,S-E);y=X[-1]+(step if e=='A' else -step);assert y>0
   X.append(y);H.append(H[-1]+(1 if e=='A' else -1));B.append(B[-1]+H[-1]);stock.add(y);snapshots.append(set(stock))
  c0=2;cn=2*l+3;lastfloor=max(q for q,h in enumerate(H) if h==-2)
  assert lastfloor==2+2*l and cn==lastfloor+1 and X[c0]==x and X[cn]==x-2*l+1
  assert {q:us for q,us in sources.items() if us}=={4:[1]}
  assert min(H)==-2 and H[-1]==0 and mindef==1 and len(free)==len(keys)==4
  K=sum(0<y<x for y in snapshots[c0]);Kn=sum(0<y<X[cn] for y in snapshots[cn]);assert K==4
  if l>=7:assert Kn==5
  assert Kn<K+2
  out.append({'label':label,'l':l,'absolute_initial_base':base,'initial_current':I,'full_initial_stock':sorted(V0),'original_actual':{str(q):us for q,us in sources.items() if us},'LOW_free':free,'LOW_keys':sorted(keys),'D':0,'positive_deficit_min':mindef,'original_cut':c0,'next_floor_cut':cn,'x':x,'y':X[cn],'clipping_loss':x-X[cn],'K_Knext':[K,Kn]})
print(json.dumps({'all_pass':True,'range_complete':True,'cases':out,'finite_only':True,'scope':'full original mass/area sources and complete initial/future stock; no canonical/C1 counter; other stock and high-free grow','worker_internal_cpu_seconds':time.process_time()-t0},indent=2))
