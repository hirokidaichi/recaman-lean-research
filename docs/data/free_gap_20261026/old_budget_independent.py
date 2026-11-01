from pathlib import Path
from functools import lru_cache
import json
B=Path(__file__).parent
@lru_cache(None)
def moments(w):
 mass=area=0
 for k,c in enumerate(reversed(w),1):sg=1 if c=='A' else -1;mass+=sg;area+=k*sg
 return mass,area
@lru_cache(None)
def tail_supply(w):
 return any(moments(w[t:])==(1,0) for t in range(len(w)))
def advance(s,j,e):
 word,adds,subs,free,spent=s;S=min(19,subs+j);u=word+'S'*j
 if S==19:u=u[-19:]
 used=spent if j==0 else False;L=tail_supply(u)
 if e==0:
  if L:return None
 else:
  if not L:
   m,a=moments(u);rho=1-m;C=-a-len(u)*rho
   if not(S<19 and rho>=1 and C>=1 and rho*(rho+1)<=2*C+2 and 4*C<=5*rho*rho-11*rho+16 and (rho!=1 or C==1)):return None
   if S>=3:
    if used:return None
    used=True
 F=free+(1 if e==0 else 0)
 if F>4 or (S<19 and S-(adds+1)+F<1):return None
 v=u+'A'
 return(v[-19:] if S==19 else v,adds+1,S,F,used)
seen=set();pending=[('',0,0,0,False)];edges=set();ends=set()
while pending:
 s=pending.pop()
 if s in seen:continue
 seen.add(s)
 if len(seen)>100000 or s[1]>10:raise RuntimeError('guard/A11')
 for j in reversed(range(20)):
  u=s[0]+'S'*j;S=min(19,s[2]+j)
  if S==19:u=u[-19:]
  if S-s[1]+s[3]==1:ends.add(u)
  for e in [1,0]:
   t=advance(s,j,e)
   if t is not None:edges.add((s,j,e,t));pending.append(t)
disc=json.loads((B/'old-budget-certificate.json').read_text());rs=disc['rows']
assert seen=={tuple(r['state']) for r in rs}
assert edges=={(tuple(r['state']),i//2,i%2,tuple(rs[t]['state'])) for r in rs for i,t in enumerate(r['edges']) if t is not None}
assert ends==set(disc['endpoints'])
old=json.loads(Path('docs/data/c1_four_20261024/macro-certificate.json').read_text())['rows']
oldstates={tuple(r['state']) for r in old};oldedges={(tuple(r['state']),i//2,i%2,tuple(old[t]['state'])) for r in old for i,t in enumerate(r['edges']) if t is not None}
proj={s[:4] for s in seen};pe={(s[:4],j,e,t[:4]) for s,j,e,t in edges}
assert proj<=oldstates and pe<=oldedges
controls=0
selected=sorted(seen)[::max(1,len(seen)//97)]
for s in selected:
 for j in [37,53,307,5003]:
  for e in [0,1]:
   assert advance(s,j,e)==advance(s,19,e);controls+=1
assert advance(('',10,19,3,True),20,0)[1]==11
# Independent known actual-prefix controls, not fresh mathematical holdouts.
actual=[]
for prefix in ['ASAAA','AASAAA','SAAASAAA','SSAAAASAAA']:
 tail='S'*5+'A'*3+'S'*4+'A'*4+'S'+'A'*3;whole=prefix+tail;state=('',0,0,0,False);j=0;free=0
 for q,c in enumerate(tail):
  if c=='S':j+=1;continue
  b=len(prefix)+q;e=int(any(moments(whole[t:b])==(1,0) for t in range(b)))
  nxt=advance(state,j,e);assert nxt is not None,(prefix,q,state,j,e)
  free+=1-e;state=nxt;j=0
 actual.append({'prefix':prefix,'free':free,'final_state':state})
out={'complete':True,'states':len(seen),'edges':len(edges),'projected_states':len(proj),'projected_edges':len(pe),'removed_old_states':len(oldstates-proj),'removed_old_edges':len(oldedges-pe),'endpoints':sorted(ends),'long_gap_controls':controls,'known_actual_controls':actual,'kernel_state_gate':len(seen)<=3000,'scope':'independent finite reverse DFS; actual-to-credit-model simulation and kernel not provided'}
(B/'old-budget-independent.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
