"""Exact independent certificate check; no search, full explicit stock retained."""
from pathlib import Path
import json,time,hashlib
t0=time.process_time();p=Path(__file__).resolve().parent
data=(p/'adjacent-class.log').read_bytes();r=json.loads(data)['admissible_counter']
w=[1 if s=='A' else -1 for s in r['word']];h=r['h'];replay=r['coherent_replay'];base=replay['base'];X=replay['current'];stock=replay['complete_stock'];seen=set(stock)
assert X in seen and 0 in seen and w[:h]==[-1]*h and w[h]==1
H=[0];B=[0];values=[X];actual={};free=[];pairs={};positive=[]
for q,expected in enumerate(w):
 n=base+q+1;c=X-n;got=-1 if X>n and c not in seen else 1
 assert got==expected
 X=X-n if got==-1 else X+n;seen.add(X);values.append(X)
 if got==1:
  sups=[]
  for u in range(q):
   segment=w[u:q];mass=sum(segment);area=sum(sum(segment[:j]) for j in range(1,len(segment)+1))
   if mass==1 and area==0:sups.append(u)
  actual[q]=sups
  if not sups:
   free.append(q)
   if H[q]<=1-h:pairs[q]=(H[q]-1,(q+1)*(H[q]-1)-B[q])
 H.append(H[-1]+got);B.append(B[-1]+H[-1]);positive.append(w[:q+1].count(-1)-sum(bool(s) for s in actual.values()))
assert values==replay['outputs'] and actual=={int(q):s for q,s in r['all_original_suppliers'].items()}
assert min(positive)>=1 and H[-1]==2-h and min(H)==-h-5
assert len(pairs)==8 and len(set(pairs.values()))==8
band=[]
for q in actual:
 if H[q] in [-15,-14]:
  assert actual[q] and q not in pairs
  band.append({'target':q,'height':H[q],'all_suppliers':[{'u':u,'height':H[u],'length':q-u,'literal_window':r['word'][u:q],'mass':sum(w[u:q]),'relative_area':sum(sum(w[u:u+j]) for j in range(1,q-u+1))} for u in actual[q]]})
assert {b['height'] for b in band}=={-15,-14}
chronology=[]
for v in range(1,len(H)):
 if w[v-1]!=-1:continue
 for u in range(v):
  assert not(H[u]==H[v] and B[v]-B[u]==(v-u)*H[v])
 for q in range(v):
  if w[q]==1:assert not(H[q]-1==H[v] and B[v]-B[q]==(v-q)*H[v])
out={'all_pass':True,'input_sha256':hashlib.sha256(data).hexdigest(),'word':r['word'],'h':h,'length':len(w),'return':H[-1],'minimum':min(H),'D':5,'F_LOW':8,'K_LOW':8,'minimum_original_deficit':min(positive),'missing_levels':[-15,-14],'band_all_sources':band,'all_original_suppliers':actual,'LOW_free_candidate_pairs':pairs,'H':H,'B':B,'actual_greedy_replay':replay,'scope':'explicit arbitrary coherent State; no canonical prehistory, no C1 counter','worker_internal_cpu_seconds':time.process_time()-t0}
print(json.dumps(out,indent=2))
