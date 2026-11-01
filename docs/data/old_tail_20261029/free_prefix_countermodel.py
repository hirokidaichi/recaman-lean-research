"""Freeze before running. Auxiliary free-before-source strengthening only.
Discovery R3..5 suffix mass/area; reserved R8..12 holdout forward walk/area.
"""
import sys,json
from pathlib import Path
mode=sys.argv[1];assert mode in ('discovery','holdout')
Rs=range(3,6) if mode=='discovery' else range(8,13)
def endable_suffix(w):
 out=[]
 for k,c in enumerate(w):
  good=False
  if c:
   for t in range(k):
    v=w[t:k];mass=sum(1 if b else -1 for b in v)
    area=sum((len(v)-a)*(1 if b else -1) for a,b in enumerate(v))
    if mass==1 and area==0:good=True;break
  out.append(good)
 return out
def endable_walk(w):
 F=[0];C=[0]
 for c in w:F.append(F[-1]+(1 if c else -1));C.append(C[-1]+F[-1])
 return [c and any(F[k]==F[t]+1 and C[k]-C[t]-(k-t)*F[t]==0 for t in range(k)) for k,c in enumerate(w)]
def P2(v):return sum(1 if b else -1 for b in v)==1 and sum((len(v)-a)*(1 if b else -1) for a,b in enumerate(v))==0
rows=[]
for R in Rs:
 w=[True]+[False]*(R+1)+[True]*(R+1)+[False]*2+[True]+[False]+[True]*(R+1)+[False]*(R-1)+[True]
 n=1;z=2*R+2;last=2*R+7;i=2;T=R+1;j=R-1;target=4*R+7
 E=(endable_suffix if mode=='discovery' else endable_walk)(w)
 prefix_A=sum(w[n:z]);prefix_free=sum(w[k] and not E[k] for k in range(n,z))
 zero=sum(E[:n])==sum(not x for x in w[:n])
 positive=all(sum(E[:u])+1<=sum(not x for x in w[:u]) for u in range(n+1,target+1))
 assert P2(w[:target]) and P2(w[z:last+i]) and E[target] and E[last+i]
 assert zero and positive and prefix_A==R and prefix_free==R-1 and i+j==T
 rows.append({'R':R,'word':''.join('A' if b else 'S' for b in w),'n':n,'z':z,'last_ray_start':last,'i':i,'T':T,'j':j,'target':target,'prefix_A':prefix_A,'prefix_actual_free':prefix_free,'zero':zero,'all_positive_through_target':positive,'EndN_clocks':[k for k,e in enumerate(E) if e],'old_target_window':''.join('A' if b else 'S' for b in w[:target]),'local_window':''.join('A' if b else 'S' for b in w[z:last+i]),'claim':'REFUTED auxiliary free-prefix strengthening; not parent C1'} )
out={'mode':mode,'implementation':'literal suffix mass/area' if mode=='discovery' else 'independent forward Fw and cumulative Ar','range':[min(Rs),max(Rs)],'rows':rows,'counterexamples':len(rows),'label':'COMPUTED finite actual replay; family allR still requires proof'}
(Path(__file__).parent/(mode+'-free-prefix.json')).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
