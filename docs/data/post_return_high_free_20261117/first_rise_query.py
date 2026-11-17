import json,time
from pathlib import Path
P=Path(__file__).resolve().parent;START=time.process_time()

def sources(w):
 mass=area=0;ans=[];q=len(w)
 for u in range(q-1,-1,-1):
  z=1 if w[u]=='A' else -1;mass+=z;area+=(q-u)*z
  if mass==1 and area==0:ans.append(u)
 return sorted(ans)

roots=[{'p':0,'x':None,'y':None,'word':'S'*8,'old_free':0}]
roots += [{'p':1,'x':x,'y':None,'word':'S'*(8-x)+'A'+'S'*(x+1),'old_free':1} for x in range(7)]
roots += [{'p':2,'x':x,'y':y,'word':'S'*(8-x)+'A'+'S'*(x+1-y)+'A'+'S'*(y+1),'old_free':2} for x in range(7) for y in range(min(x+1,6)+1)]
roots += [{'p':3,'x':x,'y':None,'word':'S'*(8-x)+'AAA'+'S'*(x+3),'old_free':2} for x in range(7)]
assert len(roots)==49
nodes=[];root_ids=[];counter=None;largest=0
for r,root in enumerate(roots):
 i=len(nodes);root_ids.append(i);nodes.append({'root':r,'tail':'','height':0,'free':root['old_free'],'A_sources':None,'children':{}});todo=[i]
 while todo:
  if time.process_time()-START>3.5:raise RuntimeError('cooperative3.5CPU cap')
  i=todo.pop();row=nodes[i];tail=row['tail'];h=row['height'];f=row['free'];word=root['word']+tail
  if len(tail)>=64:raise RuntimeError('64-future-length cap')
  row['A_sources']=ss=sources(word);ff=f+(not ss)
  for x in 'SA':
   hh=h+(1 if x=='A' else -1);gg=ff if x=='A' else f
   if hh<=0 or gg>4:continue
   if hh==7:
    counter={'root':root,'root_index':r,'word':word+x,'tail':tail+x,'free':gg,'height':hh,'from_node':i};row['children'][x]='counter';break
   if len(nodes)>=6000:raise RuntimeError('6000-node cap')
   j=len(nodes);row['children'][x]=j;nodes.append({'root':r,'tail':tail+x,'height':hh,'free':gg,'A_sources':None,'children':{}});todo.append(j);largest=max(largest,len(tail)+1)
  if counter:break
 if counter:break
result={'status':'counter' if counter else 'complete finite forest','roots_started':len(root_ids),'roots_total':49,'nodes':len(nodes),'largest_tail':largest,'counter':counter,'cpu_seconds':time.process_time()-START,'evidence':'COMPUTED; original-profile coverage/proof audit is separate'}
(P/'first-rise-summary.json').write_text(json.dumps(result,indent=2)+'\n')
(P/'first-rise-forest.json').write_text(json.dumps({'roots':roots,'root_ids':root_ids,'nodes':nodes},indent=2)+'\n')
print(json.dumps(result),flush=True)
