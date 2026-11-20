"""New predicates: generic S-admission equality and rational escape identity."""
import itertools,json,sys
from pathlib import Path
from fractions import Fraction as F
cfg=json.loads(Path(sys.argv[1]).read_text())
def data(w):
 H=[0];B=[0]
 for c in w:H.append(H[-1]+(1 if c=='A'else -1));B.append(B[-1]+H[-1])
 col=[]
 for v in range(1,len(w)+1):
  if w[v-1]!='S':continue
  for u in range(v):
   if H[u]==H[v]and B[v]-B[u]==(v-u)*H[v]:col.append(('I',u,v))
  for q in range(v):
   if w[q]=='A'and H[q]-1==H[v]and B[v]-B[q]==(v-q)*H[v]:col.append(('II',q,v))
 return H,B,sorted(col)
coherent=padding=activations=identities=pairs=0
by_length={}
for n in cfg['discovery_lengths']+cfg['parameter_control_lengths']:
 for letters in itertools.product('AS',repeat=n):
  w=''.join(letters);H,B,col=data(w)
  if not col:
   coherent+=1;by_length[n]=by_length.get(n,0)+1
   for d in cfg['padding_depths']:
    actual=data('S'*d+w)[2];expected=[]
    for q,c in enumerate(w):
     r=H[q]-1
     if c=='S'and 1<=r<=d and 2*B[q]==r*(2*q+r+1):
      expected.append(('I',d-r,d+q+1));activations+=1
    assert actual==sorted(expected),(w,d,actual,expected)
    padding+=1
  for x,b in cfg['numeric_parameter_pairs']:
   X=[x]
   for q,c in enumerate(w):X.append(X[-1]+(1 if c=='A'else -1)*(b+q+1))
   if not all(z>0 for z in X[1:]):continue
   D=0
   if x>0:
    while b*(D+1)+(D+1)*(D+2)//2<x:D+=1
   assert min(H)>=-D
   for t in range(1,n+1):
    rhs=F(X[t],b+t)-F(x,b+1)+sum((F(X[k],(b+k)*(b+k+1))for k in range(1,t)),F(0))
    assert rhs==H[t]
    lower=-F(x,b+1)+sum((F(1,b+2*j+1)for j in range(1,(t-1)//2+1)),F(0))
    assert H[t]>=lower;identities+=1
    for j in range(1,(t-1)//2+1):
     assert X[2*j-1]+X[2*j]>=b+2*j;pairs+=1
assert activations>0 and pairs>0
result=dict(PASS=True,coherent_words=coherent,coherent_by_length=by_length,padding_comparisons=padding,new_S_collisions=activations,rational_identities=identities,positive_value_pairs=pairs,scope='Finite NEW S threshold and independent rational/triangular predicates; not all-length proofs, not fresh canonical data')
Path(sys.argv[2]).write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
