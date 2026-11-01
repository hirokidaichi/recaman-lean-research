from pathlib import Path
import itertools,json
B=Path(__file__).parent

def mass_key(w):
 h=k=0
 for a in w:
  if a:h+=1
  else:k+=4*h-2;h-=1
 return h,k

def reverse_window(w):
 m=a=0
 for i,c in enumerate(reversed(w),1):
  sg=1 if c else -1;m+=sg;a+=i*sg
  if m==1 and a==0:return True
 return False

cases=valid=0
for n in [9,11,15]:
 for k in range(40):
  v=(53*k+11)%(1<<n);u=tuple(bool(v>>i&1) for i in range(n))
  for r,j in itertools.product([0,1,3,8],[0,2,5,9]):
   cases+=1;actual=reverse_window(u+(True,)*r+(False,)*j)
   keys=[mass_key(u[t:]) for t in range(n)]
   rhs=any(m+r==j+1 and key==-2*(j+1)**2 for m,key in keys)
   assert actual==rhs,(n,k,r,j)
   if actual:valid+=1;assert j+1<=u.count(False) and r<=2*u.count(False)
for h in [1,2,5,11,23]:
 u=(False,)*h;assert reverse_window(u+(True,)*(2*h)+(False,)*(h-1))
 assert mass_key(u)==(-h,-2*h*h)
out={'cases':cases,'supply_cases':valid,'violations':0,'sharp_family_controls':[1,2,5,11,23],'holdout':'fixed LCG words lengths9/11/15 with [0,1,3,8]x[0,2,5,9]; independent key via S increments and reversed suffix windows'}
(B/'a-run-holdout.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
