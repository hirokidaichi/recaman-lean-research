"""One frozen run-profile attack on adjacent missing LOW class levels."""
from itertools import product
from collections import defaultdict,Counter
import json,time
t0=time.process_time();stats=Counter();first_raw=None;primary=None;stop=None

def inspect(w,h):
 H=[0];B=[0];O={(0,0)};ac=set();free=[];k=defaultdict(set);actual={};bad=[];S=E=0;positive=True
 for q,e in enumerate(w):
  c=(H[-1]-1,(q+1)*(H[-1]-1)-B[-1])
  if e==1:
   supplied=c in O;E+=int(supplied);ac.add(c)
   if not supplied:
    free.append(q)
    if H[-1]<=1-h:k[H[-1]].add(c)
  else:S+=1
  if S-E<1:positive=False
  H.append(H[-1]+e);B.append(B[-1]+H[-1]);o=(H[-1],(q+2)*H[-1]-B[-1])
  if e==-1 and (o in O or o in ac):bad.append(q+1)
  O.add(o)
 ell=min(H);R=1-h
 gaps=[r for r in range(ell+2,R) if not k[r] and not k[r+1]]
 if not gaps:return None
 sources={q:[u for u in range(q) if H[q]==H[u]+1 and B[q]-B[u]==(q-u)*H[u]] for q,e in enumerate(w) if e==1}
 r={'word':''.join('A' if e==1 else 'S' for e in w),'h':h,'D':-h-ell,'F_LOW':sum(H[q]<=R for q in free),'K_LOW':sum(len(v) for v in k.values()),'class_heights':{r:len(v) for r,v in sorted(k.items()) if v},'empty_adjacent_pair_starts':gaps,'positive':positive,'chronology_bad_S':bad,'all_original_suppliers':sources}
 if positive and not bad:
  Q=len(w);n=Q+1;base=100*n*n;x=100*(base+n)*n
  values=[x+(base+t+1)*H[t]-B[t] for t in range(Q+1)]
  seed={0,x,*(values[q]-(base+q+1) for q in free)};seen=set(seed)
  for q,e in enumerate(w):
   c=values[q]-(base+q+1);got=-1 if c>0 and c not in seen else 1
   assert got==e;seen.add(values[q+1])
  r['coherent_replay']={'base':base,'current':x,'complete_stock':sorted(seed),'outputs':values,'all_signs_pass':True}
 return r

try:
 for label,h,runses,gapmax,corecap in [('discovery',7,range(2,5),6,32),('parameter_controls',13,[5],4,40)]:
  for runs in runses:
   for As in product(range(1,4),repeat=runs-1):
    for Ss in product(range(1,gapmax+1),repeat=runs-1):
     final=2+sum(Ss)-sum(As)
     if final<1 or 2*sum(Ss)+2>corecap:continue
     w=[-1]*h
     for a,s in zip(As,Ss):w += [1]*a+[-1]*s
     w += [1]*final
     stats[label+'_profiles']+=1;r=inspect(w,h)
     if r:
      stats['raw_gap_counters']+=1
      if first_raw is None:first_raw=r
      if r['positive'] and not r['chronology_bad_S']:primary=r;raise ValueError('admissible counter found')
     if time.process_time()-t0>.65:raise TimeoutError('partial frozen profile audit, no extension')
except (ValueError,TimeoutError) as e:stop=str(e)
print(json.dumps({'counts':dict(stats),'first_RAW_gap_counter':first_raw,'admissible_counter':primary,'stop':stop,'worker_internal_cpu_seconds':time.process_time()-t0},indent=2))
