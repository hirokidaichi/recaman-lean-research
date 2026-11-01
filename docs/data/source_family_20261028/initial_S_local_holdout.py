"""Independent forward-area replay on disjoint R8..10; necessary bounds only."""
from pathlib import Path
import json,time,itertools
start=time.process_time()
def tick():
 if time.process_time()-start>7.5:raise TimeoutError('cooperative CPU guard')
def literal(w):
 height=[0];area=[0]
 for b in w:
  height.append(height[-1]+(1 if b else -1));area.append(area[-1]+height[-1])
 return height,area
def window_ok(w):
 z,a=literal(w);return z[-1]==1 and a[-1]==0
def evaluate(h,M,m,L,s,T):
 w=[False]*h+[True]*M+[False]*m+[True]*L+[False]*s+[True]*T
 z,a=literal(w);starts=[h,h+M+m,h+M+m+L+s];lens=[M,L,T];ss=[h,h+m,h+m+s]
 clocks=[]
 for begin,k in zip(starts,lens):
  hits=[]
  for t in range(begin,begin+k):
   if any(z[t]-z[u]==1 and a[t]-a[u]-(t-u)*z[u]==0 for u in range(t)):hits.append(t-begin)
  clocks.append(hits)
 if h==0:return None
 choices=[]
 opts=[range(2) if any(i not in clocks[k] and (k!=0 or i>=2) for i in range(lens[k])) else range(1) for k in range(3)]
 for extra in itertools.product(*opts):
  sup=0;ok=True
  for k in range(3):
   sup+=len(clocks[k])+extra[k]
   if sup>=ss[k]:ok=False;break
  if ok:choices.append(sup)
 if not choices:return None
 return M+L+T-max(choices),clocks,sorted(set(choices))
shapes=set()
for R in [7,8,9,10]:
 for K in range(R+1,21-R):
  A=K+R
  for q in range(1,K-1):
   for m in range(1,K-q):
    s=K-q-m
    for M in range(1,A-1):
     for L in range(1,A-M):
      tick();T=A-M-L
      w=[False]*q+[True]*M+[False]*m+[True]*L+[False]*s+[True]*T+[False]*(R-1)
      if window_ok(w):shapes.add((M,m,L,s,T,R,q))
rows=[];bad=[]
for M,m,L,s,T,R,q in sorted(shapes):
 for h in range(q,40):
  tick();r=evaluate(h,M,m,L,s,T)
  if r is None:continue
  row={'h':h,'M':M,'m':m,'L':L,'s':s,'T':T,'R':R,'q':q,'min_free':r[0],'local_clocks':r[1],'possible_total_supply_counts':r[2]};rows.append(row)
  if r[0]<R:bad.append(row)
out={'label':'COMPUTED','R_range':[7,10],'independent':'forward literal target and local windows; discovery source not imported','skeletons':len(shapes),'feasible_rows':len(rows),'min_free_minus_R':min([r['min_free']-r['R'] for r in rows],default=None),'residual_count':len(bad),'residual_rows':bad,'all_rows':rows,'worker_process_cpu_seconds':time.process_time()-start}
Path(__file__).with_name('initial-S-local-holdout.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k not in ['all_rows','residual_rows']}))
