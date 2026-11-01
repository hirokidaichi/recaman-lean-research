from pathlib import Path
from functools import lru_cache
import json
P=Path(__file__).parent
@lru_cache(None)
def moments(w):
 r=a=0
 for c in w:r+=1 if c=='A' else -1;a+=r
 return r,a
@lru_cache(None)
def local(w):return any(moments(w[t:])==(1,0) for t in range(len(w)))
def step(s,j,e):
 w,A,S,F,U,cred=s;S2=min(19,S+j);v=w+'S'*j
 if S2==19:v=v[-19:];cred=()
 U2=U if j==0 else False;L=local(v)
 if e:
  if not L:
   r,a=moments(v);rho=1-r;C=-a-len(v)*rho
   if not(S2<19 and rho>=1 and C>=1 and rho*(rho+1)<=2*C+2 and 4*C<=5*rho*rho-11*rho+16 and (rho!=1 or C==1)):return None
   if S2>=3:
    if U2:return None
    U2=True
   d={r:(lo,hi) for r,lo,hi in cred}
   lo,hi=d.get(rho,(C,C));lo=min(lo,C);hi=max(hi,C)
   if hi-lo>4:return None
   d[rho]=(lo,hi);cred=tuple((r,*d[r]) for r in sorted(d))
 elif L:return None
 F2=F+1-e
 if F2>4 or (S2<19 and S2-A-1+F2<1):return None
 v+='A'
 return(v[-19:] if S2==19 else v,A+1,S2,F2,U2,cred)

base=json.loads(Path('docs/data/free_gap_20261026/old-budget-certificate.json').read_text());br=base['rows'];bs={tuple(r['state']) for r in br};be={(tuple(r['state']),i//2,i%2,tuple(br[t]['state'])) for r in br for i,t in enumerate(r['edges']) if t is not None}
states=[('',0,0,0,False,())];ids={states[0]:0};rows=[];stopped=False;edgecount=0
while len(rows)<len(states) and not stopped:
 s=states[len(rows)];edges=[]
 for j in range(20):
  for e in (0,1):
   t=step(s,j,e)
   if t is None:continue
   assert t[1]<=10,('new A11',s,j,e,t)
   if t not in ids:ids[t]=len(states);states.append(t)
   edges.append((j,e,ids[t]));edgecount+=1
   if len(states)>20000:stopped=True;break
  if stopped:break
 rows.append({'state':s,'edges':edges})
proj={s[:5] for s in states};pe={(tuple(r['state'][:5]),j,e,states[t][:5]) for r in rows for j,e,t in r['edges']}
assert proj<=bs and pe<=be
summary={'protocol':'SAME_MASS_PRUNING_PROTOCOL.json','complete_closure':not stopped,'states_seen':len(states),'states_processed':len(rows),'edges_processed':edgecount,'state_measurement_guard':20000,'kernel_state_gate':len(states)<=3000 and not stopped,'projected_states_seen':len(proj),'projected_edges_seen':len(pe),'baseline_states':len(bs),'baseline_edges':len(be),'removed_projected_states':len(bs-proj) if not stopped else None,'removed_projected_edges':len(be-pe) if not stopped else None,'unprocessed_queue':len(states)-len(rows),'status':'STOPPED state measurement guard' if stopped else ('STOPPED no projected reduction' if proj==bs and pe==be else 'COMPUTED pruning, kernel not supplied')}
(P/'same-mass-pruning.json').write_text(json.dumps(summary,indent=2)+'\n')
(P/'same-mass-pruning-data.json').write_text(json.dumps({'summary':summary,'rows':rows},separators=(',',':'))+'\n')
print(json.dumps(summary))
