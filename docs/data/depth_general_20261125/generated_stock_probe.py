"""NEW generated-versus-initial stock loss with original all-source free accounting."""
import sys,json,time,random
from collections import Counter
mode=sys.argv[1];t0=time.process_time();C=Counter();counter=None;largest=None
if mode=='discovery':xs=[12,24,48,96,192];bs=[0,3,11,29];dens=[0,.125,.375];seeds=[101,509];Qmax=64
else:xs=[17,39,83,167];bs=[2,7,23];dens=[0,.2,.6];seeds=[1103,1901];Qmax=80
planned=len(xs)*len(bs)*len(dens)*len(seeds)
for x0 in xs:
 for b in bs:
  for density in dens:
   for seed in seeds:
    rng=random.Random(seed+1000003*x0+10007*b);V0={0,x0}
    for v in range(1,2*x0+1):
     if v!=x0-b-1 and rng.random()<density:V0.add(v)
    seen=set(V0);generated=set();X=[x0];H=[0];B=[0];F=[0];G=[set()];sources={};word=[];S=E=0;valid=[True]
    for q in range(Qmax):
     n=b+q+1;c=X[-1]-n;e='S'if c>0 and c not in seen else'A';word.append(e)
     if e=='A':
      us=[u for u in range(q)if H[q]==H[u]+1 and B[q]-B[u]==(q-u)*H[u]];sources[q]=us
      if us:E+=1
      F.append(F[-1]+(not us))
     else:S+=1;F.append(F[-1])
     out=X[-1]+(n if e=='A'else -n);assert out>0
     if out not in V0:generated.add(out)
     seen.add(out);X.append(out);H.append(H[-1]+(1 if e=='A'else -1));B.append(B[-1]+H[-1]);G.append(set(generated));valid.append(valid[-1]and S-E>=1)
    h=next((q for q,e in enumerate(word)if e=='A'),Qmax);C['states']+=1
    if h>0:C['positive_head_states']+=1
    for Q in range(h+1,Qmax+1):
     if h<1 or not valid[Q]or H[Q]!=2-h:continue
     C['original_positive_return_endpoints']+=1
     for cut in range(Q):
      if H[Q]<=H[cut]or min(H[cut:Q+1])<H[cut]:continue
      v=max(q for q in range(cut,Q+1)if H[q]==H[cut]);cp=v+1;x=X[cut];y=X[cp];loss=sorted(z for z in G[cut]if y<=z<x);lhs=len(loss);rhs=h+2*F[cut]
      C['cut_checks']+=1;C['decreasing_current']+=y<x;C['nonempty_generated_loss']+=lhs>0;C['seed_only_loss']+=lhs==0 and any(y<=z<x for z in V0)
      if lhs and(largest is None or lhs-rhs>largest['margin']):largest={'x0':x0,'b':b,'density':density,'seed':seed,'Q':Q,'cut':cut,'nextcut':cp,'h':h,'F_before':F[cut],'Lgen':lhs,'x':x,'y':y,'margin':lhs-rhs}
      if lhs>rhs:
       counter={'x0':x0,'b':b,'V0':sorted(V0),'word':''.join(word[:Q]),'Q':Q,'cut':cut,'nextcut':cp,'h':h,'F_before':F[cut],'Lgen':lhs,'generated_lost':loss,'seed_loss':sorted(z for z in V0 if y<=z<x),'X':X[:Q+1],'H':H[:Q+1],'B':B[:Q+1],'ALL_original_sources':{str(q):us for q,us in sources.items()if q<Q},'scope':'exact original actual coherent positive/head/return candidate counter, not C1/canonical'};break
     if counter:break
    if counter:break
    if time.process_time()-t0>.6:
     print(json.dumps({'mode':mode,'range_complete':False,'stop':'SOFT_CPU_NO_EXTENSION','counts':dict(C),'planned_states':planned,'largest':largest,'counter':None,'worker_internal_cpu_seconds':time.process_time()-t0},indent=2));raise SystemExit(0)
   if counter:break
  if counter:break
 if counter:break
print(json.dumps({'mode':mode,'range_complete':not counter and C['states']==planned,'stop':'EXACT_COUNTER'if counter else'FROZEN_RANGE_COMPLETE','counts':dict(C),'planned_states':planned,'largest':largest,'counter':counter,'worker_internal_cpu_seconds':time.process_time()-t0,'finite_only':True,'scope':'NEW original provenance loss predicate; parameter holdout, not fresh canonical data'},indent=2))
