import json
from pathlib import Path
P=Path(__file__).resolve().parent

def evaluate(w):
 H=[0];sources={};free=[];S=N=0;positive=True
 for x in w:H.append(H[-1]+(1 if x=='A' else -1))
 for q,x in enumerate(w):
  if x=='A':
   mass=area=0;ss=[]
   for u in range(q-1,-1,-1):
    z=1 if w[u]=='A' else -1;mass+=z;area+=(q-u)*z
    if mass==1 and area==0:ss.append(u)
   sources[str(q)]=sorted(ss)
   if ss:N+=1
   else:free.append(q)
  else:S+=1
  positive=positive and N+1<=S
 return {'word':w,'H':H,'sources':sources,'free':free,'positive':positive,'A':w.count('A')}

r=json.loads((P/'original-four-summary.json').read_text());counter=evaluate(r['counter']['word'])
assert counter['positive'] and counter['A']==8 and len(counter['free'])==4
records={'counter':counter};compared=0
words=[('sharp-known','S'*6+'A'*4+'S'+'A'*3)]
words += [(f'peak-{h}', 'S'*h+'A'*4+'S'+'A'*3) for h in [2,4,6,11,29]]
words += [(f'ray-{h}-{a}','S'*h+'A'*a) for h in [3,7,23] for a in range(1,10)]
words += [(f'padded-{h}','S'*h+'ASAAA'+'S'*5+'A'*3+'S'*4+'A'*4+'S'+'A'*3) for h in [2,10,31]]
for name,w in words:
 row=evaluate(w);records[name]=row
 for q,ss in row['sources'].items():
  q=int(q)
  if w[:q].count('A')>7:continue
  start=max(0,q-13);tail=evaluate(w[start:q]+'A')['sources'][str(q-start)]
  assert [start+u for u in tail]==ss,(name,q)
  compared+=1
assert records['sharp-known']['A']==7 and len(records['sharp-known']['free'])==4 and records['sharp-known']['positive']
(P/'original-four-audit-certificates.json').write_text(json.dumps(records,indent=2)+'\n')
summary={'result':'PASS','cases':len(records),'exact_source_set_comparisons':compared,'candidate_A_le_7':'REFUTED by original positive A8/free4 word','no_claim_of_PC5_counter':True}
(P/'original-four-audit-summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary))
