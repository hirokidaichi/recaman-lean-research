"""NEW canonical-necessary-budget compatible loss family; no canonical claim."""
import time,json,hashlib
t0=time.process_time();out=[]
for label,ks in [('discovery',[15,35]),('unused_parameters',[55,75,95])]:
 for k in ks:
  l=3*k;b=5*k*k-k-2;x=10*l*l;a=b-2;I=x+2*b-1;gap=4*k*k-5*k+1;y=x-gap
  C=lambda j:x+(j-2)*b+j*(j-3)//2
  minimal={0,I,*[C(j) for j in range(1,l+1) if j!=3],x-l*l-b-2*l-1,x-l*l-1};V=minimal|set(range(y,x));N=len(V)
  assert N==4*k*k-2*k+3 and N<=a+1 and (I-a*(a+1)//2)%2==0 and max(V)<=a*(a+1)//2
  s=N-1;assert a*(a+1)//2<=I+s*(2*a-s+1)
  seen=set(V);X=[I];H=[0];B=[0];src={};F=[];FK=set();low=[];LK=set();S=E=0;md=10**9;K=Kn=None
  for q,e in enumerate('SS'+'A'*l+'S'*l+'AA'):
   n=a+q+1;c=X[-1]-n;got='S' if c>0 and c not in seen else 'A';assert got==e,(k,q,c)
   if e=='S':S+=1;assert not y<=c<x
   else:
    us=[u for u in range(q) if H[q]==H[u]+1 and B[q]-B[u]==(q-u)*H[u]];src[q]=us
    if us:E+=1
    else:
     key=(H[q]-1,(q+1)*(H[q]-1)-B[q]);F.append(q);FK.add(key)
     if H[q]<=-1:low.append(q);LK.add(key)
   md=min(md,S-E);v=X[-1]+(n if e=='A' else -n);seen.add(v);X.append(v);H.append(H[-1]+(1 if e=='A' else -1));B.append(B[-1]+H[-1])
   if q+1==2:K=sum(0<v<x for v in seen)
   if q+1==2*l+3:Kn=sum(0<v<y for v in seen);assert X[-1]==y
  assert {q:us for q,us in src.items() if us}=={4:[1]}
  assert md==1 and min(H)==-2 and H[-1]==0 and len(F)==len(FK)==3*k+1 and len(low)==len(LK)==4
  assert K==gap+3 and Kn==5 and K-Kn==4*k*k-5*k-1
  T=13*b+20*x-15*K;Tn=13*(b+2*l+1)+20*y-15*Kn;assert 20*Tn<=51*T-260
  out.append({'label':label,'k':k,'l':l,'initial_clock':a,'initial_current':I,'FULL_seed_recipe':{'minimal':sorted(minimal),'add_interval_inclusive':[y,x-1]},'FULL_seed_count':N,'FULL_sorted_seed_sha256':hashlib.sha256(json.dumps(sorted(V),separators=(',',':')).encode()).hexdigest(),'necessary_filters':{'cardinality':N<=a+1,'current_parity':(I-a*(a+1)//2)%2==0,'ALL_seed_triangular_range':max(V)<=a*(a+1)//2,'sorted_clock_cover':a*(a+1)//2<=I+s*(2*a-s+1)},'ALLfree_ALLclasses':[len(F),len(FK)],'LOWfree_LOWclasses':[len(low),len(LK)],'D':0,'positive_min':md,'original_actual':{str(q):us for q,us in src.items() if us},'Kold':K,'Knext':Kn,'loss':K-Kn})
print(json.dumps({'all_pass':True,'range_complete':True,'cases':out,'finite_only':True,'scope':'NEW actual family passing four specified necessary canonical filters, NOT canonical reachability/C1','worker_internal_cpu_seconds':time.process_time()-t0},indent=2))
