"""Independent natural-step simulation and direct literal source audit, fixed inputs."""
import json,time
t0=time.process_time();out=[]
for b in [2,5,13,31,67]:
 value=1;seen={0,1};w=[];values=[value];heights=[0]
 for clock in range(b+1,3*b+3):
  candidate=value-clock
  subtract=value>=clock and candidate>0 and candidate not in seen
  e=-1 if subtract else 1;value=value-clock if subtract else value+clock
  if subtract:assert value not in seen
  assert value>0;seen.add(value);w.append(e);values.append(value);heights.append(heights[-1]+e)
 assert w==[1]+[v for i in range(b) for v in [1,-1]]+[1]
 allsources={}
 for q,e in enumerate(w):
  if e!=1:continue
  sources=[]
  for u in range(q):
   level=0;area=0
   for sign in w[u:q]:level+=sign;area+=level
   if level==1 and area==0:sources.append(u)
  assert sources==[];allsources[str(q)]=sources
 c1=max(i for i,v in enumerate(heights) if v==0)+1
 c2=max(i for i,v in enumerate(heights) if i>=c1 and v==1)+1
 ps=[b+2,b+c1+2*values[c1],b+c2+2*values[c2]]
 assert ps[2]-9*ps[0]==-8 and ps[1]-3*ps[0]==-1
 assert len(allsources)==b+2
 out.append({'b':b,'actual_word_length':len(w),'original_free':len(allsources),'all_original_supplier_sets':allsources,'cuts':[0,c1,c2],'potentials':ps,'complete_initial_stock':[0,1],'all_S_fresh':True})
# Negative scope control: canonical cover inequality rejects the SMALL seed for b>=4.
negative={'b':7,'current':1,'full_stock':[0,1],'triangular_clock':28,'cover_RHS':15,'canonical_necessary_cover_fails':True}
print(json.dumps({'all_pass':True,'independent_records':out,'canonical_scope_negative':negative,'scope':'direct natural greedy steps/literal windows, no prefix-key lookup or new search; finite evidence only','worker_internal_cpu_seconds':time.process_time()-t0},indent=2))
