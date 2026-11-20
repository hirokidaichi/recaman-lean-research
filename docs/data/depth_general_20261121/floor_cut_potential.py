"""New predicate: construct bounded-value floor cuts, joint factor-three potential."""
import json,sys
from pathlib import Path
cfg=json.loads(Path(sys.argv[1]).read_text())
counts=dict(prefixes=0,floor_visit_pairs=0,witness_cuts=0,uniform_floor_targets=0)
def check(w,x,b):
 X=[x];H=[0]
 for q,c in enumerate(w):
  z=1 if c=='A' else -1;X.append(X[-1]+z*(b+q+1));H.append(H[-1]+z)
 assert min(X[1:],default=1)>0
 Q=len(w);L=x//(b+1)
 for c in range(Q+1):
  m=min(H[c:]);y=X[c]
  for v in range(c,Q+1):
   if H[v]==m:
    counts['floor_visit_pairs']+=1
    assert 2*X[v]+v-c<=2*y
    if y>=1:assert v-c<=2*y-2
 c=0;m=-L;P=b+2*x;bound=P
 if x==0:
  if Q==0:return
  c=1;m=1;P=3*(b+1);bound=P
  assert H[1]==1 and X[1]==b+1
 assert min(H[c:])>=m
 for j in range(cfg['max_level_increments']):
  D=bound-b-1
  if Q<D:break
  visits=[v for v in range(c,Q+1)if H[v]==m]
  if visits:
   v=visits[-1];assert v+1<=D<=Q and w[v]=='A'
   c=v+1
  m+=1;newP=b+c+2*X[c]
  assert newP<=3*P-1
  bound=3*bound-1;P=newP
  assert c<=D and min(H[c:])>=m and P<=bound
  counts['witness_cuts']+=1
  for t in range(D,Q+1):
   counts['uniform_floor_targets']+=1;assert H[t]>=m
 counts['prefixes']+=1
for pairs in [cfg['discovery'],cfg['parameter_controls']]:
 for x,b in pairs:
  stack=[('',x)]
  while stack:
   w,v=stack.pop();check(w,x,b)
   if len(w)<cfg['max_length']:
    for c,z in [('A',1),('S',-1)]:
     a=v+z*(b+len(w)+1)
     if a>0:stack.append((w+c,a))
# Exact extremizers in the WEAK numerical-positive model, without a seen set.
w='A';value=1;clock=1;ext=[]
for floor in range(1,cfg['sharp_floor_levels']+1):
 w+='AS'*(value-1);clock+=2*(value-1);value=1
 expected=1 if floor==1 else (5*3**(floor-2)-3)//2
 # floor j starts at (5*3^(j-2)-1)/2; the LAST visit is the next start minus1.
 expected_last=(5*3**(floor-1)-3)//2
 assert clock==expected_last,(floor,clock,expected_last)
 check(w,0,0);ext.append(dict(floor=floor,last_visit=clock,final_value=value))
 w+='A';clock+=1;value+=clock
assert counts['witness_cuts']>0 and counts['uniform_floor_targets']>0
Path(sys.argv[2]).write_text(json.dumps(dict(PASS=True,counts=counts,sharp_numerical_extremizers=ext,scope='Finite direct-value checks of a NEW cut/potential and all-level PAPER extremizer formulas; no canonical freshness claim'),indent=2)+'\n')
print(json.dumps(dict(PASS=True,counts=counts,sharp_numerical_extremizers=ext)))
