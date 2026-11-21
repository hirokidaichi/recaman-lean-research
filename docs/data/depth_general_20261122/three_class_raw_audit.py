"""Independent broader RAW audit, pruning only the NEW monotone K<=3 support."""
import json,time
start=time.process_time();nodes=ends=0;counter=None;by_h={};stopped=None
def audit(h):
 global nodes,ends,counter
 H=list(range(0,-h-1,-1));B=[0]
 for e in H[1:]:B.append(B[-1]+e)
 O={(H[i],(i+1)*H[i]-B[i]) for i in range(h+1)};K=set();w=['S']*h
 count=0
 def dfs(F,minimum):
  global nodes,ends,counter
  nonlocal count
  nodes+=1;count+=1;q=len(w);r=q-h
  if nodes%128==0 and time.process_time()-start>.55:raise TimeoutError('partial raw audit, no extension')
  if r>0 and H[-1]==2-h:
   ends+=1;D=max(0,-h-minimum)
   if D>1 or F!=len(K):
    counter={'word':''.join(w),'h':h,'D':D,'F':F,'K':len(K),'classes':sorted(K)};raise ValueError('counter')
  if r==28:return
  if abs(2-h-H[-1])>28-r:return
  for s in [1,-1]:
   if not r and s<0:continue
   c=(H[-1]-1,(q+1)*(H[-1]-1)-B[-1])
   low=s==1 and c not in O and H[-1]<=1-h
   add=low and c not in K
   if add and len(K)==3:continue
   if add:K.add(c)
   hp=H[-1]+s;bp=B[-1]+hp;op=(hp,(q+2)*hp-bp);new=op not in O
   if new:O.add(op)
   H.append(hp);B.append(bp);w.append('A' if s==1 else 'S')
   dfs(F+int(low),min(minimum,hp))
   w.pop();H.pop();B.pop()
   if new:O.remove(op)
   if add:K.remove(c)
 dfs(0,-h);by_h[h]={'nodes':count,'completed':True}
try:
 for h in [1,4,9]:audit(h)
except (TimeoutError,ValueError) as e:stopped=str(e)
print(json.dumps({'nodes':nodes,'nonvacuous_return_prefixes':ends,'counter':counter,'completed_h':by_h,'stopped':stopped,'max_core':28,'worker_internal_cpu_seconds':time.process_time()-start},indent=2))
