"""Frozen LOW equality attack: all original and numerical source histories retained."""
import json,time
start=time.process_time();rows=[]
for m in [4,6,8,10,18,30]:
 h=m+6;u=h+5;b=m*m-m-12;x=m*m+1
 w='S'*h+'ASSSS'+'A'*(m+1)+'S'*(m-1)+'AAA'
 H=[0];B=[0];delta=[0]
 for q,s in enumerate(w):
  e=1 if s=='A' else -1
  H.append(H[-1]+e);B.append(B[-1]+H[-1]);delta.append(delta[-1]+(b+q+1)*e)
 initial=x-delta[u];values=[initial+d for d in delta]
 seed={0,initial};numeric={};sources={};free=[];low=[];min_deficit=10**9
 for q,s in enumerate(w):
  if s=='A':
   c=values[q]-(b+q+1);old=[i for i in range(q) if values[i]==c]
   numeric[q]=old
   if c>0 and not old:seed.add(c)
   sup=[i for i in range(q) if H[q]==H[i]+1 and B[q]-B[i]==(q-i)*H[i]]
   sources[q]=sup
   if not sup:
    free.append(q)
    if H[q]<=1-h:low.append(q)
  min_deficit=min(min_deficit,sum(z=='S' for z in w[:q+1])-sum(bool(v) for v in sources.values()))
 seen=set(seed);actual=[];bad=None
 for q,expected in enumerate(w):
  c=values[q]-(b+q+1);got='S' if c>0 and c not in seen else 'A'
  if got!=expected:
   bad={'q':q,'expected':expected,'got':got,'candidate':c,'all_prior_numeric_sources':[i for i in range(q+1) if values[i]==c],'initial_seed_match':c in seed};break
  actual.append(got);seen.add(values[q+1])
 q=u+2*m;n=b+q+1;K={(H[i]-1,(i+1)*(H[i]-1)-B[i]) for i in low}
 r={'m':m,'h':h,'base':b,'initial_current':initial,'initial_stock':sorted(seed),'word':w,'prescribed_outputs':values,'first_mismatch':bad,'minimum_original_deficit':min_deficit,'return_height':H[-1],'depth':-h-min(H),'target':q,'source':u,'numeric_sources':numeric[q],'original_P2_sources':sources[q],'target_LOW':q in low,'target_is_original_free':q in free,'age':q-u,'step_clock':n,'age_equality':4*n==(q-u)**2+4*(q-u),'K_LOW':len(K),'F_LOW':len(low),'all_original_suppliers':sources}
 if bad is None:
  assert min_deficit>=1 and H[-1]==2-h and q in low and not sources[q]
  assert values[q]-n==values[u] and r['age_equality']
 rows.append(r)
print(json.dumps({'rows':rows,'worker_internal_cpu_seconds':time.process_time()-start},indent=2))
