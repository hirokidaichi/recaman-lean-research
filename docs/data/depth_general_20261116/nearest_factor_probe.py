"""Finite falsifier for 2D_near<=Flow; original actual sources retained, no free replacement."""
import sys,time,json
mode=sys.argv[1];beg=time.process_time();nodes=cases=0;done=[];counter=None;weak_counter=None;best=None;maxD=0
class Stop(Exception):pass

def guard():
 if time.process_time()-beg>1.4:raise Stop

def search(h,lim,reverse):
 global nodes,cases,counter,weak_counter,best,maxD
 H=[-i for i in range(h+1)];B=[0]
 for x in H[1:]:B.append(B[-1]+x)
 keys={}
 for t in range(h):keys.setdefault((H[t],B[t]-t*H[t]),[]).append(t)
 tail=[]
 def dfs(q,E,F,Flow,D,S):
  global nodes,cases,counter,weak_counter,best,maxD
  nodes+=1
  if nodes%2048==0:guard()
  if D:
   cases+=1;maxD=max(maxD,D)
   item={'h':h,'K':q-h,'word':'S'*h+''.join(tail),'Dnear':D,'Flow':Flow,'Fwhole':F,'double_minus_lowfree':2*D-Flow}
   if best is None or 2*D-Flow>best['double_minus_lowfree']:best=item
   if D>Flow:weak_counter=item
   if 2*D>Flow:counter=item;raise Stop
  if q==h+lim:return
  if reverse:
   src=[];a=0
   for t in range(q-1,-1,-1):
    a+=H[t+1]
    if H[q]==H[t]+1 and a-(q-t)*H[t]==0:src.append(t)
  else:src=keys.get((H[q]-1,B[q]-q*(H[q]-1)),[])
  supplied=bool(src);near=supplied and all(t<h for t in src) and H[q]+h==2
  key=(H[q],B[q]-q*H[q]);keys.setdefault(key,[]).append(q)
  for a in [False,True]:
   ee=E+int(a and supplied);ff=F+int(a and not supplied);fl=Flow+int(a and not supplied and H[q]<=-h+1);dd=D+int(a and near);ss=S+int(not a)
   if ee+1>ss:continue
   HH=H[q]+(1 if a else -1);H.append(HH);B.append(B[-1]+HH);tail.append('A' if a else 'S')
   dfs(q+1,ee,ff,fl,dd,ss);tail.pop();B.pop();H.pop()
  keys[key].pop()
  if not keys[key]:del keys[key]
 dfs(h,0,0,0,0,h)
try:
 params=[(h,18) for h in [1,2,3,4]] if mode=='forward' else [(h,14) for h in [17,31]]
 for h,k in params:search(h,k,mode=='reverse');done.append([h,k])
 status='all frozen ranges complete'
except Stop:status='counterexample' if counter else 'cooperative CPU stop; incomplete ranges unclaimed'
print(json.dumps({'mode':mode,'status':status,'complete_ranges':done,'nodes':nodes,'prefixes_with_near_targets':cases,'max_Dnear':maxD,'best':best,'strong_counter':counter,'weak_counter':weak_counter,'cpu_body_seconds':time.process_time()-beg,'scope':'finite actual-positive initial-S histories; reused/related prefix spaces are discovery, not fresh holdout; absence is no all-depth proof'}),flush=True)
