from pathlib import Path
from collections import deque
import json
P=Path(__file__).parent
ATOMS=('A','SAAA','SSAAAASAAA')
def facts(w):
 r=a=0
 for c in w:r+=1 if c=='A' else -1;a+=r
 return r,a
SUFS={v:tuple(facts(v[t:]) for t in range(len(v))) for v in ATOMS}
def advance(state,v,R):
 d,e=facts(v)
 return tuple(sorted({(r+d,a+len(v)*r+e) for r,a in state if r+d<=R}|{p for p in SUFS[v] if p[0]<=R}))
out={'protocol':'JOINT_SIGNATURE_PROTOCOL.json','state_scope':'all suffix mass-area pairs in same actual BlockWord, positive mass<=R','limits':[5,7,11,19],'gate':3000,'runs':[],'complete_all_limits':False}
for R in out['limits']:
 states=[()];ids={():0};q=deque([0]);witness=[''];edges=[];stopped=False
 while q and not stopped:
  i=q.popleft()
  for v in ATOMS:
   nxt=advance(states[i],v,R)
   if nxt not in ids:
    ids[nxt]=len(states);states.append(nxt);witness.append(witness[i]+v);q.append(ids[nxt])
   edges.append((i,v,ids[nxt]))
   if len(states)>out['gate']:stopped=True;break
 row={'R':R,'states_seen':len(states),'edges_processed':len(edges),'closed':not stopped and not q,'unprocessed_queue':len(q),'max_pairs_seen':max(map(len,states)),'max_witness_length':max(map(len,witness)),'status':'STOPPED state gate' if stopped else 'COMPUTED closed'}
 out['runs'].append(row)
 (P/'signature-discovery.json').write_text(json.dumps(out,indent=2)+'\n')
 if stopped:break
 out['complete_all_limits']=R==out['limits'][-1]
 (P/('signature-R'+str(R)+'.json')).write_text(json.dumps({'R':R,'atoms':ATOMS,'states':states,'edges':edges,'witness':witness},separators=(',',':'))+'\n')
(P/'signature-discovery.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
