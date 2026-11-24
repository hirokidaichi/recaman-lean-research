"""NEW all-free-linear stock-loss counter, full seed recipe and literal sources."""
import json,time,hashlib
t0=time.process_time();records=[]
for label,ks in [('discovery',[5,25]),('unused_parameters',[45,65,85])]:
 for k in ks:
  l=3*k;b=4*k*k-k-2;x=10*l*l;gap=5*k*k-5*k+1;y=x-gap;base=b-2;I=x+2*b-1
  C=lambda j:x+(j-2)*b+j*(j-3)//2
  minimal={0,I,*[C(j) for j in range(1,l+1) if j!=3],x-l*l-b-2*l-1,x-l*l-1}
  Ys={x+d*b-d*(d-1)//2+l*(2*d-l) for d in range(l)};holes=Ys&set(range(y,x));V=minimal|(set(range(y,x))-Ys)
  assert not minimal&Ys
  w='SS'+'A'*l+'S'*l+'AA';seen=set(V);X=[I];H=[0];B=[0];sources={};free=[];keys=set();low=[];lowkeys=set();S=E=0;md=10**9;K=Kn=None
  for q,e in enumerate(w):
   n=base+q+1;candidate=X[-1]-n;actual='S' if candidate>0 and candidate not in seen else 'A';assert actual==e,(k,q,candidate)
   if e=='S':S+=1
   else:
    us=[u for u in range(q) if H[q]==H[u]+1 and B[q]-B[u]==(q-u)*H[u]];sources[q]=us
    if us:E+=1
    else:
     key=(H[q]-1,(q+1)*(H[q]-1)-B[q]);free.append(q);keys.add(key)
     if H[q]<=-1:low.append(q);lowkeys.add(key)
   md=min(md,S-E);v=X[-1]+(n if e=='A' else -n);seen.add(v);X.append(v);H.append(H[-1]+(1 if e=='A' else -1));B.append(B[-1]+H[-1])
   if q+1==2:K=sum(0<v<x for v in seen)
   if q+1==2*l+3:Kn=sum(0<v<y for v in seen);assert X[-1]==y
  assert {q:us for q,us in sources.items() if us}=={4:[1]}
  assert md==1 and min(H)==-2 and H[-1]==0 and len(free)==len(keys)==3*k+1 and len(low)==len(lowkeys)==4
  assert Kn==4 and K==gap+2-len(holes)
  if k==5:assert not holes
  else:assert len(holes)==1 and holes=={x-k*k+10*k-5} and K-Kn==5*k*k-5*k-2
  T=13*b+20*x-15*K;Tn=13*(b+2*l+1)+20*y-15*Kn;assert 20*Tn<=51*T-260
  records.append({'label':label,'k':k,'l':l,'base':base,'initial_current':I,'full_seed_recipe':{'minimal':sorted(minimal),'add_interval_inclusive':[y,x-1],'exclude_exact_S_holes':sorted(holes)},'FULL_seed_distinct_count':len(V),'FULL_sorted_seed_sha256':hashlib.sha256(json.dumps(sorted(V),separators=(',',':')).encode()).hexdigest(),'original_actual':{str(q):us for q,us in sources.items() if us},'ALLfree_ALLclasses':[len(free),len(keys)],'LOWfree_LOWclasses':[len(low),len(lowkeys)],'D':0,'original_positive_min':md,'K_old':K,'K_next':Kn,'net_loss':K-Kn,'gap':gap,'T_change':Tn-T})
print(json.dumps({'all_pass':True,'range_complete':True,'cases':records,'finite_only':True,'scope':'new quadratic stock-loss / linear ALL original free-class family, full seed/holes retained; no C1/canonical claim','worker_internal_cpu_seconds':time.process_time()-t0},indent=2))
