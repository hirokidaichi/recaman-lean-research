"""Finite attack on H04; direct weighted values independent of H/B identity."""
import json, sys
from pathlib import Path
cfg=json.loads(Path(sys.argv[1]).read_text())
totals={k:0 for k in ['positive_prefixes','floor_edge_targets','recurrence_targets','literal_source_hits','source_cutoff_checks']}
rows=[]
def check(w,x,b):
 H=[0];B=[0];X=[x]
 for q,c in enumerate(w):
  z=1 if c=='A' else -1
  H.append(H[-1]+z);B.append(B[-1]+H[-1]);X.append(X[-1]+z*(b+q+1))
 assert all(v>0 for v in X[1:])
 assert all(X[t]==x+(b+t+1)*H[t]-B[t]for t in range(len(X)))
 Q=len(w);L=x//(b+1)
 assert min(H)>=-L
 for s in range(Q+1):
  m=min(H[s:]);cut=s+2*X[s]+1
  for t in range(cut,Q+1):
   totals['floor_edge_targets']+=1
   assert H[t]>=m+1,(w,x,b,s,m,t)
 s=0;j=0
 while s<=Q:
  for t in range(s,Q+1):
   totals['recurrence_targets']+=1
   assert H[t]>=-L+j,(w,x,b,j,s,t)
  U=x+b*s+s*(s+1)//2;s=s+2*U+1;j+=1
 for u in range(Q):
  y=X[u];a=b+u;cut=0
  for j in range(y//(a+1)+2):
   cut+=2*(y+a*cut+cut*(cut+1)//2)+1
   if cut>Q-u:break  # Later iterates only increase; exclusion then vacuous here.
  for q in range(u+1,Q):
   if w[q]=='A' and H[q]==H[u]+1 and B[q]-B[u]==(q-u)*H[u]:
    totals['literal_source_hits']+=1;assert q<u+cut,(w,x,b,u,q,cut)
   if q>=u+cut:totals['source_cutoff_checks']+=1
 totals['positive_prefixes']+=1
 return H,X
for label,pairs in [('discovery',cfg['discovery']),('unused_parameter_controls',cfg['parameter_controls'])]:
 for x,b in pairs:
  count=0;stack=[('',x)]
  while stack:
   w,value=stack.pop()
   check(w,x,b);count+=1
   if len(w)<cfg['max_length']:
    for c,z in [('A',1),('S',-1)]:
     v=value+z*(b+len(w)+1)
     if v>0:stack.append((w+c,v))
  rows.append(dict(label=label,x=x,b=b,positive_prefixes=count))
fixtures=[]
for x,b in cfg['balanced_return_controls']:
 w='AS'*(x-1);H,X=check(w,x,b)
 assert H[-1]==0 and X[-1]==1 and len(w)==2*x-2
 fixtures.append(dict(x=x,b=b,last_floor_return=len(w),last_value=X[-1],cutoff=2*x+1))
assert totals['floor_edge_targets']>0 and totals['source_cutoff_checks']>0 and totals['literal_source_hits']>0,totals
Path(sys.argv[2]).write_text(json.dumps(dict(PASS=True,rows=rows,totals=totals,near_boundary_fixtures=fixtures,scope='Finite falsifier on all short numerical-positive weighted words and unused parameters; not a proof or canonical reachability'),indent=2)+'\n')
print(json.dumps(dict(PASS=True,totals=totals,near_boundary_fixtures=fixtures)))
