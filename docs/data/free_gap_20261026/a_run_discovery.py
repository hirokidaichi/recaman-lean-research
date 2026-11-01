from pathlib import Path
import itertools,json
B=Path(__file__).parent

def ma(w):
 h=a=0
 for x in w:h+=1 if x else -1;a+=h
 return h,a

def local(w):
 F=[0];P=[0]
 for x in w:F.append(F[-1]+(1 if x else -1));P.append(P[-1]+F[-1])
 return any(F[-1]-F[t]==1 and P[-1]-P[t]-(len(w)-t)*F[t]==0 for t in range(len(w)))

cases=roots=bound=0
for n in range(8):
 for u in itertools.product([False,True],repeat=n):
  for r,j in itertools.product(range(7),repeat=2):
   cases+=1;w=u+(True,)*r+(False,)*j
   actual=local(w)
   rhs=False
   for t in range(n):
    m,a=ma(u[t:]);rhs|=(m+r==j+1 and 2*a-m*(m+1)==-2*(j+1)**2)
   assert actual==rhs,(u,r,j,actual,rhs)
   if actual:roots+=1;assert j+1<=u.count(False) and r<=2*u.count(False);bound+=1
out={'cases':cases,'supply_cases':roots,'bound_checks':bound,'violations':0,'discovery':'all u length0..7; r,j0..6'}
(B/'a-run-discovery.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
