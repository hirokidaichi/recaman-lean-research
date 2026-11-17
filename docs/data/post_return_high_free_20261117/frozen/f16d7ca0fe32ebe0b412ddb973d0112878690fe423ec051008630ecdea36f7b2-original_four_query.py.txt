import json,time,hashlib
from collections import deque
from pathlib import Path
P=Path(__file__).resolve().parent;START=time.process_time()

def supply(w):
 mass=area=0
 for k,x in enumerate(reversed(w),1):
  z=1 if x=='A' else -1;mass+=z;area+=k*z
  if mass==1 and area==0:return True
 return False

initial=('',0,0,0);states=[initial];index={initial:0};words=[''];todo=deque([0]);rows=[];counter=None
while todo:
 if time.process_time()-START>3.5:raise RuntimeError('cooperative3.5CPU cap')
 i=todo.popleft();w,a,f,s=states[i];row={'state':list(states[i]),'S':None,'A':None};rows.append(row)
 for x in 'SA':
  aa=a+(x=='A');ff=f+int(x=='A' and not supply(w));ss=min(9,s+(x=='S'))
  if ff>4 or aa-ff+1>ss:continue
  word=words[i]+x
  if aa==8:
   counter={'word':word,'A':aa,'free':ff,'capped_S':ss,'parent_state':i};row['A']='counter';break
  nxt=((w+x)[-13:],aa,ff,ss)
  if nxt not in index:
   if len(states)>=6000:raise RuntimeError('6000-state cap')
   index[nxt]=len(states);states.append(nxt);words.append(word);todo.append(index[nxt])
  row[x]=index[nxt]
 if counter:break
out={'status':'counter' if counter else 'complete finite closure','states':len(states),'rows_evaluated':len(rows),'max_A':max(s[1] for s in states),'cpu_seconds':time.process_time()-START,'evidence':'COMPUTED; whole-history simulation and kernel certificate not supplied by this script','counter':counter}
(P/'original-four-summary.json').write_text(json.dumps(out,indent=2)+'\n')
(P/'original-four-graph.json').write_text(json.dumps({'rows':rows,'representative_words':words},indent=2)+'\n')
print(json.dumps(out),flush=True)
