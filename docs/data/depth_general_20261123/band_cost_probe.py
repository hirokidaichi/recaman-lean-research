"""NEW single empty-band lower-class excess predicate; no old census extension."""
import json,time,sys
from collections import Counter,defaultdict
t0=time.process_time();stats=Counter();examples=[];mode=sys.argv[1]
limit=14000 if mode=='discovery' else 8000
state=23061123 if mode=='discovery' else 23161123
def analyze(core,tag,forced_h=None):
 A=core.count(1);h=forced_h if forced_h is not None else A+1;w=[-1]*h+core
 H=[0];B=[0];outputs=defaultdict(list);outputs[(0,0)].append(0);prior_candidates=set();free=[];C={};sources={};bad=[];actual=0;S=0;mindef=10**9
 for q,e in enumerate(w):
  r=H[-1];c=(r-1,(q+1)*(r-1)-B[-1])
  if e==1:
   u=list(outputs.get(c,[]));sources[q]=u
   if u:actual+=1
   else:free.append(q);C[q]=c
   prior_candidates.add(c)
  else:S+=1
  hn=r+e;bn=B[-1]+hn;o=(hn,(q+2)*hn-bn)
  if e==-1 and (o in outputs or o in prior_candidates):bad.append(q)
  outputs[o].append(q+1);H.append(hn);B.append(bn)
  mindef=min(mindef,S-actual)
 ell=min(H);R=1-h;keys=defaultdict(set)
 for q in free:
  if H[q]<=R:keys[H[q]].add(C[q])
 stats['profiles']+=1;stats['chronology_pass']+=not bad
 bands=[];r=ell+2
 while r<=-h-1:
  if keys[r]:r+=1;continue
  s=r
  while s+1<=-h-1 and not keys[s+1]:s+=1
  # Maximal in the FULL low-height class support, not an arbitrary subinterval.
  if keys[r-1] and keys[s+1]:
   excess=sum(max(len(keys[t])-1,0) for t in range(ell,r));g=s-r+1
   bands.append([r,s,g,excess]);stats['eligible_bands']+=1
   if g>=2:stats['nontrivial_bands']+=1
   if excess<g-1:
    result={'tag':tag,'word':''.join('A' if e==1 else 'S' for e in w),'h':h,'length':len(w),'ell':ell,'return':H[-1],'D':-h-ell,'F_LOW':sum(H[q]<=R for q in free),'K_LOW':sum(len(v) for v in keys.values()),'band':[r,s],'g':g,'lower_excess':excess,'k_by_height':{str(t):len(keys[t]) for t in range(ell,R+1)},'all_original_suppliers':sources,'LOW_free_pairs':{str(q):C[q] for q in free if H[q]<=R},'H':H,'B':B,'chronology_failures':bad,'original_positive':mindef>0,'minimum_original_deficit':mindef}
    stats['raw_violations']+=1
    if not examples:examples.append(result)
    if not bad:
     assert H[-1]==2-h and mindef>0
     print(json.dumps({'stop':'FIRST_ADMISSIBLE_COUNTER','mode':mode,'counts':dict(stats),'counter':result,'first_raw_counter':examples[0],'worker_internal_cpu_seconds':time.process_time()-t0},indent=2));raise SystemExit(0)
  r=s+1
 return bands
# OLD E771 as a named regression control for the NEW cost, not fresh discovery.
old=[1]+[-1]*4+[1]+[-1]+[1]+[-1]*3+[1]*3+[-1]+[1]*5
assert [-15,-14,2,2] in analyze(old,'OLD_E771_control',13)
stats.clear();examples.clear()
for index in range(limit):
 state=(1664525*state+1013904223)%2**32;z=state
 k=(3+index%3) if mode=='discovery' else (6+index%3)
 cap=4 if mode=='discovery' else 5;aa=[];ss=[]
 for j in range(k):
  z=(1103515245*z+12345)%2**31;aa.append(1+(z>>16)%cap)
  z=(1103515245*z+12345)%2**31;ss.append(1+(z>>16)%cap)
 tail=2+sum(ss)-sum(aa)
 if tail<=0 or tail>24:continue
 core=[]
 for a,s in zip(aa,ss):core.extend([1]*a+[-1]*s)
 core.extend([1]*tail)
 if len(core)>76:continue
 analyze(core,{'index':index,'a':aa,'s':ss,'tail':tail})
 if stats['profiles']%128==0 and time.process_time()-t0>.65:
  print(json.dumps({'stop':'SOFT_CPU_GATE_NO_EXTENSION','mode':mode,'range_complete':False,'last_index':index,'counts':dict(stats),'first_raw_counter':examples[0] if examples else None,'worker_internal_cpu_seconds':time.process_time()-t0},indent=2));raise SystemExit(0)
print(json.dumps({'stop':'DECLARED_RANGE_COMPLETE','mode':mode,'range_complete':True,'counts':dict(stats),'first_raw_counter':examples[0] if examples else None,'worker_internal_cpu_seconds':time.process_time()-t0},indent=2))
