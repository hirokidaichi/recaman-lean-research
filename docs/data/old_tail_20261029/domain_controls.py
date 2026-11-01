"""Frozen fixed nonvacuity cases, not a search or new general theorem."""
import json
from pathlib import Path
cases=[{'name':'initialS_q_less_than_h','old':[],'n':0,'h':39,'q':5,'M':5,'m':1,'L':2,'s':1,'T':5,'j':4},
{'name':'joint_old_third_activates_first_bound','old':[False]+[True]*6,'n':7,'h':9,'q':4,'M':5,'m':2,'L':1,'s':3,'T':8,'j':4,'old_start':0,'old_third_clock':4}]
def E(w):
 F=[0];A=[0]
 for x in w:F.append(F[-1]+(1 if x else -1));A.append(A[-1]+F[-1])
 return [x and any(F[k]==F[t]+1 and A[k]-A[t]-(k-t)*F[t]==0 for t in range(k)) for k,x in enumerate(w)]
def p2(w):return sum(1 if b else -1 for b in w)==1 and sum((len(w)-i)*(1 if b else -1) for i,b in enumerate(w))==0
rows=[]
for c in cases:
 n,h,q,M,m,L,s,T,j=[c[k] for k in ['n','h','q','M','m','L','s','T','j']]
 w=c['old']+[False]*h+[True]*M+[False]*m+[True]*L+[False]*s+[True]*T+[False]*j+[True]
 es=E(w);last=n+h+M+m+L+s;target=last+T+j;source=n+h-q
 zero=sum(es[:n])==sum(not b for b in w[:n]);pos=all(sum(es[:u])+1<=sum(not b for b in w[:u]) for u in range(n+1,target+1))
 assert zero and pos and es[target] and p2(w[source:target]) and q<h
 row=dict(c,word=''.join('A' if b else 'S' for b in w),target=target,target_source=source,old_zero=zero,all_positive=pos,target_window=p2(w[source:target]),EndN_clocks=[k for k,e in enumerate(es) if e],first_supplied=sum(es[n+h:n+h+M]))
 if 'old_third_clock' in c:
  i=c['old_third_clock'];z=c['old_start']
  assert p2(w[z:last+i]) and es[last+i] and T<=i+j and q<j+1 and M<=q+2
  assert row['first_supplied']==1
  row.update(old_third_endpoint=last+i,old_third_window=True,joint_antecedent=True)
 rows.append(row)
out={'label':'COMPUTED','scope':'fixed actual-sign/EndN nonvacuity controls, not standard Recaman orbit and not new theorem','rows':rows}
(Path(__file__).parent/'DOMAIN_CONTROLS.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
