"""NEW uniform floor/source-horizon consumers, exact rational envelope."""
import json,time
from fractions import Fraction
from collections import Counter
t0=time.process_time();C=Counter();records=[]
def run(x,b,V,Q):
 X=[x];H=[0];B=[0];stocks=[set(V)]
 for q in range(Q):
  n=b+q+1;candidate=X[-1]-n;e=-1 if candidate>0 and candidate not in stocks[-1] else 1
  y=X[-1]+e*n;X.append(y);H.append(H[-1]+e);B.append(B[-1]+H[-1]);stocks.append(stocks[-1]|{y})
 return X,H,B,stocks
def depth(x,b):
 d=0
 while b*(d+1)+(d+1)*(d+2)//2<x:d+=1
 return d
def envelope(G0,b):
 G=Fraction(G0);out=[]
 for j in range(10):
  u=(2*G/5-b-7).__floor__();out.append(u);G=(51*G-260)/20
 assert all(v>u for u,v in zip(out,out[1:]))
 return out
cases=[]
for x in [1,2,3]:
 for b in [0,1,4]:
  for extra in [[],list(range(1,x)),[x+2,x+7]]:
   cases.append(('discovery',x,b,{0,x,*extra},64))
for x,b in [(7,2),(11,0),(4,3)]:
 for extra in [[],list(range(1,x)),list(range(3,x,3))]:cases.append(('unused_parameters',x,b,{0,x,*extra},96))
for label,x,b,V,Q in cases:
 X,H,B,stocks=run(x,b,V,Q);D=depth(x,b);Us=envelope(13*b+26*x,b)
 assert min(H)>=-D
 for end in range(1,Q+1):
  c0=max(q for q in range(end+1) if H[q]==min(H[:end+1]));K0=sum(0<y<X[c0] for y in stocks[c0]);T0=13*(b+c0)+20*X[c0]-15*K0
  assert c0+2*X[c0]<=2*x and T0<=13*b+26*x
  for j,U in enumerate(Us,1):
   if U<=end:
    assert min(H[U:end+1])>=-D+j;C['uniform_floor_targets']+=1
 for u in range(Q):
  y=X[u];base=b+u;du=depth(y,base);cutoff=u+envelope(13*base+26*y,base)[du+1] if du+1<10 else Q+1
  for q in range(u+1,Q):
   literal=H[q]==H[u]+1 and B[q]-B[u]==(q-u)*H[u]
   if literal:C['literal_original_source_hits']+=1;assert q<cutoff
   if q>=cutoff:assert H[q]-H[u]>=2;C['nonvacuous_excluded_source_positions']+=1
 C[label+'_states']+=1
for b in [0,1,3,7]:
 X,H,B,V=run(0,b,{0},96);assert X[1]==b+1 and min(H[1:])>=1;Us=envelope(33*(b+1),b)
 for j,U in enumerate(Us,1):
  if U<=96:assert min(H[U:])>=1+j;C['zero_source_floor_targets']+=1
 if Us[0]<=96:
  assert all(H[q]>=2 for q in range(Us[0],97));C['zero_source_exclusion_positions']+=97-Us[0]
 records.append({'initial_base':b,'first_A_current':X[1],'source0_excluded_from':Us[0]})
print(json.dumps({'all_pass':True,'range_complete':True,'counts':dict(C),'zero_source':records,'finite_only':True,'scope':'new rational uniform thresholds and complete original-source exclusions; independent predicates on direct actual States; no fresh orbit ranges','worker_internal_cpu_seconds':time.process_time()-t0},indent=2))
