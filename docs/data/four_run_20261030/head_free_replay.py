import json,time
from pathlib import Path
cpu0=time.process_time()
base=Path(__file__).resolve().parent
out=[]
for mode in ['discovery','holdout']:
 rec=json.loads((base/('H06-'+mode+'.log')).read_text())['witness'];w=rec['word'];n=rec['n'];b=rec['target'];head=rec['head']
 witnesses={};d=[0];free=[]
 for k,x in enumerate(w):
  assert time.process_time()-cpu0<.6
  sources=[]
  if x=='A':
   mass=moment=0
   for t in range(k-1,-1,-1):
    sign=1 if w[t]=='A' else -1
    mass+=sign;moment+=(k-t)*sign
    if mass==1 and moment==0:sources.append(t)
  if sources:witnesses[k]=sources
  if x=='A' and not sources:free.append(k)
  d.append(d[-1]+(x=='S')-bool(sources))
 head_free=sum(n<=k<head for k in free);full_free=sum(n<=k<b for k in free)
 assert d[n]==0 and min(d[n+1:b+1])>=1
 assert 0 in witnesses[b] and head-1 in witnesses[head+2] and w[head-1]=='S'
 assert head_free==rec['head_free'] and full_free==rec['full_free']
 out.append({'mode':mode,'literal_source_lists':witnesses,'free_positions':free,'zero':d[n],'positive_min':min(d[n+1:b+1]),'head_free':head_free,'full_free':full_free,'R':rec['R'],'head_counter':head_free<rec['R'],'full_counter':full_free<rec['R']})
print(json.dumps({'independent_replay_not_holdout':out,'cpu_seconds':time.process_time()-cpu0},indent=2))
