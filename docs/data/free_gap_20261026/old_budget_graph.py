from pathlib import Path
from functools import lru_cache
import json
B=Path(__file__).parent
@lru_cache(None)
def profile(w):
 h=a=0
 for c in w:h+=1 if c=='A' else -1;a+=h
 return h,a
@lru_cache(None)
def local(w):return any(profile(w[t:])==(1,0) for t in range(len(w)))

def gap(s,j):
 w,A,S,F,U=s;ns=min(19,S+j);v=w+'S'*j
 return(v[-19:] if ns==19 else v,A,ns,F,U if j==0 else False)

def move(s,j,e):
 w,A,S,F,U=gap(s,j);L=local(w);mass,area=profile(w);rho=1-mass;C=-area-len(w)*rho
 old=(S<19 and rho>=1 and C>=1 and rho*(rho+1)<=2*C+2 and 4*C<=5*rho*rho-11*rho+16 and (rho!=1 or C==1))
 if e:
  if L:pass
  elif old and not(S>=3 and U):U=S>=3
  else:return None
 elif L:return None
 nf=F+1-e
 if nf>4 or (S<19 and S-A-1+nf<1):return None
 v=w+'A'
 return(v[-19:] if S==19 else v,A+1,S,nf,U)

states=[('',0,0,0,False)];idx={states[0]:0};rows=[];ends=set()
while len(rows)<len(states):
 if len(states)>100000:raise RuntimeError('state guard')
 s=states[len(rows)]
 if s[1]>10:raise RuntimeError(('A11 retained witness',s))
 for j in range(20):
  w,A,S,F,U=gap(s,j)
  if S-A+F==1:ends.add(w)
 edges=[]
 for j in range(20):
  for e in [0,1]:
   t=move(s,j,e)
   if t is None:edges.append(None);continue
   if t not in idx:idx[t]=len(states);states.append(t)
   edges.append(idx[t])
 rows.append({'state':list(s),'edges':edges})
out={'states':len(states),'edges':sum(t is not None for r in rows for t in r['edges']),'endpoints':sorted(ends),'maxA':max(s[1] for s in states),'rows':rows,'evidence':'COMPUTED only; actual credit simulation/kernel separate'}
(B/'old-budget-certificate.json').write_text(json.dumps(out,separators=(',',':'))+'\n');print(json.dumps({k:v for k,v in out.items() if k!='rows'}))
