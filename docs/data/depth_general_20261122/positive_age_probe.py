"""Frozen full-original-history lift of numerical blocker age equality."""
import json,time
start=time.process_time();rows=[]
for m in [4,6,10,18,3,5]:
 h=m+3;b=m*m-m-4;local=m*m-1;x=m*m+1
 V=lambda j:x+j*local-j*(j-1)//2
 C=lambda j:x+(j-1)*local+(j*j-j-2)//2
 seed={0,V(h),*(C(j) for j in range(m+1) if j!=2)}
 w='S'*h+'A'*(m+1)+'S'*(m-1)+'AS'
 X=V(h);seen=set(seed);values=[X];H=[0];B=[0];actual={};free=[];bad=None
 for q,s in enumerate(w):
  candidate=X-(b+q+1);got='S' if candidate>0 and candidate not in seen else 'A'
  if got!=s:bad={'q':q,'expected':s,'got':got,'candidate':candidate,'prior_numeric_sources':[u for u,v in enumerate(values) if v==candidate]};break
  sup=[u for u in range(q) if H[-1]==H[u]+1 and B[-1]-B[u]==(q-u)*H[u]] if s=='A' else []
  if s=='A':actual[q]=sup
  if s=='A' and not sup:free.append(q)
  X=candidate if got=='S' else X+b+q+1;seen.add(X);values.append(X)
  H.append(H[-1]+(1 if s=='A' else -1));B.append(B[-1]+H[-1])
  assert sum(z=='S' for z in w[:q+1])-sum(bool(v) for v in actual.values())>=1
 if m%2==0:
  assert bad is None and H[-1]==2-h and min(H)==-h
  q=h+2*m;n=b+q+1
  assert values[q]-n==values[h] and not actual[q]
  assert 4*n==(q-h)**2+4*(q-h)
  assert H[q]==2-h and H[q]>1-h
 else:
  assert bad is not None and bad['prior_numeric_sources']
 rows.append({'m':m,'h':h,'global_base':b,'initial_current':V(h),'initial_stock':sorted(seed),'word':w,'outputs':values,'first_mismatch':bad,'final_height_if_complete':H[-1],'final_target_sources':actual.get(h+2*m),'original_free':free,'original_actual_sources':actual,'target_is_LOW':False})
print(json.dumps({'rows':rows,'worker_internal_cpu_seconds':time.process_time()-start},indent=2))
