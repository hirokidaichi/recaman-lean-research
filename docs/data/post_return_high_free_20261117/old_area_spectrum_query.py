import json,time
from pathlib import Path
P=Path(__file__).resolve().parent;start=time.process_time()

def allowed(p,j,C):
 if j<0:return False
 tri=j*(j+1)//2
 if p<=2:
  return any(-tri+r*(1-2*j)<=C<=r*r-tri and (C-r+tri)%2==0 for r in range(p+1))
 return C==-tri or (j>=2 and C==1-tri) or (j>=1 and C==4-tri) or any(C==9-tri-6*s for s in range(j+1))

def local(w):
 a=b=0;ans=[]
 for u in range(len(w)-1,-1,-1):
  z=1 if w[u]=='A' else -1;a+=z;b+=(len(w)-u)*z
  if a==1 and b==0:ans.append(u)
 return sorted(ans)

nodes=[];root_ids=[];counter=None
for p,paid in enumerate((0,1,2,2)):
 root_ids.append(len(nodes));nodes.append(dict(p=p,tail='',height=0,area=0,paid=paid,children={}));todo=[len(nodes)-1]
 while todo:
  if time.process_time()-start>2.5:raise RuntimeError('cooperative2.5CPU cap')
  i=todo.pop();r=nodes[i];w=r['tail'];h=r['height'];B=r['area'];a=r['paid'];j=h-1;C=j*len(w)-B
  if len(w)>=64:raise RuntimeError('64-tail cap')
  r['local_sources']=ls=local(w);r['old_allowed']=old=allowed(p,j,C);r['old_j']=j;r['old_C']=C
  for x in 'SA':
   hh=h+(1 if x=='A' else -1);aa=a+(x=='A' and not (ls or old))
   if hh<=0 or aa>4:continue
   if hh==7:
    counter=dict(p=p,tail=w+x,paid=aa,from_node=i);r['children'][x]='counter';break
   if len(nodes)>=6000:raise RuntimeError('6000-node cap')
   r['children'][x]=len(nodes);todo.append(len(nodes));nodes.append(dict(p=p,tail=w+x,height=hh,area=B+hh,paid=aa,children={}))
  if counter:break
 if counter:break
out=dict(status='relaxed counter' if counter else 'complete finite relaxed forest',nodes=len(nodes),p_cases_started=len(root_ids),counter=counter,
         largest_tail=max(len(r['tail']) for r in nodes),cpu_seconds=time.process_time()-start,evidence='COMPUTED relaxed source model; no original parent counter or proof from finite absence')
(P/'old-area-spectrum-summary.json').write_text(json.dumps(out,indent=2)+'\n')
(P/'old-area-spectrum-forest.json').write_text(json.dumps(dict(root_ids=root_ids,nodes=nodes),indent=2)+'\n')
print(json.dumps(out),flush=True)
