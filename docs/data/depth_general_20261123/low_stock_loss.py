"""NEW added FULL old interval, exact original LOW4 stock-loss counter."""
import json,time
t0=time.process_time();out=[]
for label,ls in [('discovery',[7,9]),('unused_parameters',[13,23,41])]:
 for l in ls:
  b=l*(l-4);x=10*l*l;y=x-2*l+1;base=b-2;I=x+2*b-1
  C=lambda k:x+(k-2)*b+k*(k-3)//2
  minimal={0,I,*[C(k) for k in range(1,l+1) if k!=3],x-l*l-b-2*l-1,x-l*l-1}
  V=minimal|set(range(y,x));stock=set(V);w='SS'+'A'*l+'S'*l+'AA';X=[I];H=[0];B=[0];states=[set(stock)];free=[];keys=set();sources={};S=E=0;md=10**9
  for q,e in enumerate(w):
   n=base+q+1;c=X[-1]-n;got='S' if c>0 and c not in stock else 'A';assert got==e,(l,q,c)
   if e=='S':S+=1;assert not y<=c<x
   else:
    us=[u for u in range(q) if H[q]==H[u]+1 and B[q]-B[u]==(q-u)*H[u]];sources[q]=us
    if us:E+=1
    elif H[q]<=-1:free.append(q);keys.add((H[q]-1,(q+1)*(H[q]-1)-B[q]))
   md=min(md,S-E);v=X[-1]+(n if e=='A' else -n);X.append(v);H.append(H[-1]+(1 if e=='A' else -1));B.append(B[-1]+H[-1]);stock.add(v);states.append(set(stock))
  c0=2;cn=2*l+3;K=sum(0<v<X[c0] for v in states[c0]);Kn=sum(0<v<X[cn] for v in states[cn]);subset={v for v in states[c0] if 0<v<=x}|{x-l*l};lost={v for v in subset if v>=y}
  assert X[c0]==x and X[cn]==y and K==2*l+2 and Kn==5 and len(lost)==2*l
  assert {q:us for q,us in sources.items() if us}=={4:[1]} and md==1 and min(H)==-2 and H[-1]==0 and len(free)==len(keys)==4
  T=13*b+20*x-15*K;Tn=13*(base+cn)+20*y-15*Kn;assert Tn-T==16*l-12 and 20*Tn<=51*T-260
  out.append({'label':label,'l':l,'initial_current':I,'base':base,'FULL_initial_stock':sorted(V),'original_actual':{str(q):us for q,us in sources.items() if us},'LOW_free_classes':[len(free),len(keys)],'D':0,'original_positive_min':md,'old_K':K,'new_K':Kn,'net_cardinality_loss':K-Kn,'transported_subset_lost':len(lost),'full_clipping_interval_length':x-y+1,'T_change':Tn-T})
print(json.dumps({'all_pass':True,'range_complete':True,'cases':out,'finite_only':True,'scope':'new full-old-stock loss counter, entire growing added interval retained, unchanged original ledger; no C1/canonical claim','worker_internal_cpu_seconds':time.process_time()-t0},indent=2))
