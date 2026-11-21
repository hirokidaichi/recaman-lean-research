"""Independent natural-state replay with explicit paper seed; direct window sums."""
import json,time
t0=time.process_time();rows=[]
for m in [14,22,26,10]:
 h=m+6;u=h+5;B=m*m-1;x=m*m+1;b=B-u;n=m*m+2*m
 J=lambda l:x+B*l+7-l*(l+3)//2
 C=lambda j:x+(j-1)*B+(j*j-j-2)//2
 seed={0,J(h+3),C(0),C(1),*(C(j) for j in range(3,m+1)),x+n-1}
 expected=[-1]*h+[1]+[-1]*4+[1]*(m+1)+[-1]*(m-1)+[1]*3
 X=J(h+3);seen=set(seed);values=[X];observed=[];bad=None
 for i,e in enumerate(expected):
  clock=b+i+1;c=X-clock
  got=-1 if X>clock and c not in seen else 1
  if got!=e:bad={'q':i,'candidate':c,'prior_sources':[j for j,v in enumerate(values) if v==c]};break
  X=X-clock if got==-1 else X+clock
  observed.append(got);values.append(X);seen.add(X)
 if m==10:
  assert bad=={'q':33,'candidate':1033,'prior_sources':[9]}
  rows.append({'m':m,'negative_control':bad});continue
 assert bad is None
 H=[sum(observed[:i]) for i in range(len(observed)+1)]
 supplied={};free=[];low=[];deficits=[]
 for q,e in enumerate(observed):
  if e==1:
   suppliers=[]
   for a in range(q):
    segment=observed[a:q]
    mass=sum(segment);area=sum(sum(segment[:j]) for j in range(1,len(segment)+1))
    if mass==1 and area==0:suppliers.append(a)
   supplied[q]=suppliers
   if not suppliers:
    free.append(q)
    if H[q]<=1-h:low.append(q)
  deficits.append(observed[:q+1].count(-1)-sum(bool(v) for v in supplied.values()))
 expected_low=[h,u,u+1,u+3,u+4,u+2*m,u+2*m+1]
 assert low==expected_low
 keys=[(H[q]-1,(q+1)*(H[q]-1)-sum(H[1:q+1])) for q in low]
 assert len(set(keys))==6 and keys[0]==keys[3]
 assert H[-1]==2-h and min(H)==-h-3 and min(deficits)>=1
 q=u+2*m
 assert values[q]-n==values[u]==x and not supplied[q]
 assert 4*n==(2*m)*(2*m+4)
 rows.append({'m':m,'length':len(observed),'h':h,'base':b,'initial_current':J(h+3),'initial_stock':sorted(seed),'LOW_free_positions':low,'LOW_candidate_pairs':keys,'K_LOW':6,'F_LOW':7,'D':3,'minimum_deficit':min(deficits),'target':q,'source':u,'step_clock':n,'age':2*m,'full_suppliers':supplied})
 if time.process_time()-t0>.65:raise TimeoutError('verification cap')
print(json.dumps({'all_pass':True,'rows':rows,'worker_internal_cpu_seconds':time.process_time()-t0},indent=2))
