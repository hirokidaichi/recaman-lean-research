from pathlib import Path
import itertools,json
B=Path(__file__).parent

def local(w):
 F=[0];A=[0]
 for x in w:F.append(F[-1]+(1 if x else -1));A.append(A[-1]+F[-1])
 return any(F[-1]-F[t]==1 and A[-1]-A[t]-(len(w)-t)*F[t]==0 for t in range(len(w)))
cases=sup=0;rows=[]
for M,m in itertools.product([1,2,4,7],[1,3,6,9]):
 for h in [m+6,2*m+9]:
  for r,j in itertools.product(sorted({0,2*m,max(2*m,M*(m-1)),max(2*m,M*(m-1))+1}),sorted({0,1,m-1,2*m-2})):
   R=j+1;word=(False,)*h+(True,)*M+(False,)*m+(True,)*r+(False,)*j
   roots=[]
   # Actual prefix drop signatures, independent of the three-family arithmetic.
   u=(False,)*h+(True,)*M+(False,)*m
   for t in range(len(u)):
    level=key=0
    for c in u[t:]:
     if c:level+=1
     else:key+=4*level-2;level-=1
    if level+r==R and key==-2*R*R:roots.append(t)
   value=local(word);assert value==bool(roots),(h,M,m,r,j)
   if value:assert r<=max(2*m,M*(m-1));sup+=1
   cases+=1
for m in [2,3,7,11,23]:
 for h in [m+1,m+8]:
  r=4*(m-1);j=2*m-2
  assert local((False,)*h+(True,)*4+(False,)*m+(True,)*r+(False,)*j)
  assert r==max(2*m,4*(m-1));rows.append([h,4,m,r,j])
assert local((False,)*10+(False,)+(True,)*22+(False,)*10) # M0 invalidates h-independent bound
assert local((False,)*10+(True,)+(True,)*19+(False,)*9) # m0 invalidates it
out={'cases':cases,'supply_cases':sup,'violations':0,'sharp_family':rows,'excluded_zero_run_countercontrols':2,'holdout':'fresh h>=m+6 and threshold r values; full prefix signatures and forward windows'}
(B/'two-run-holdout.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
