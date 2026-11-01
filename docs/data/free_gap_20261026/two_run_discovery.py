from pathlib import Path
import itertools,json
B=Path(__file__).parent

def local(w):
 m=a=0
 for k,c in enumerate(reversed(w),1):
  s=1 if c else -1;m+=s;a+=k*s
  if m==1 and a==0:return True
 return False

cases=sup=0
for h,M,m,r,j in itertools.product(range(5),range(6),range(6),range(15),range(8)):
 w=(False,)*h+(True,)*M+(False,)*m+(True,)*r+(False,)*j
 R=j+1
 rhs=(r==2*R and R<=m) or any(r+a==R+m and R*R==m*(m-2*a) for a in range(1,M+1)) or any(M+r==R+q+m and R*R==(q+m)**2-2*m*M for q in range(1,h+1))
 lhs=local(w);cases+=1
 assert lhs==rhs,(h,M,m,r,j,lhs,rhs)
 if lhs:
  sup+=1
  if M>=1 and m>=1:assert r<=max(2*m,M*(m-1)),(h,M,m,r,j)
out={'cases':cases,'supply_cases':sup,'violations':0,'discovery':'h0..4/M,m0..5/r0..14/j0..7; reversed window checker'}
(B/'two-run-discovery.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
