"""Exact local clocks, sound count envelope only. No actual old history is asserted."""
from pathlib import Path
import json,time
start=time.process_time()
def tick():
 if time.process_time()-start>7.5:raise TimeoutError('cooperative9.5CPU stop before nominal10s RLIMIT')
def roots(v,K):
 m=ar=length=0;ans=set()
 for b in reversed(v):
  sg=1 if b else -1
  ar+=sg*(length+1);m+=sg;length+=1
  if 2*ar-m*(m+1)==-2 and 0<=1-m<K:ans.add(1-m)
 return ans
def envelope(h,M,m,L,s,T):
 if h==0:return None
 v=[False]*h;choices={0};local=[]
 for k,(A,Sbefore) in enumerate([(M,h),(L,h+m),(T,h+m+s)]):
  hit=roots(v,A);local.append(sorted(hit))
  available=any(i not in hit and (k!=0 or i>=2) for i in range(A))
  nxt=set()
  for z in choices:
   for old in range(2 if available else 1):
    total=z+len(hit)+old
    if total<=Sbefore-1:nxt.add(total)
  choices=nxt
  v += [True]*A
  if k==0:v += [False]*m
  elif k==1:v += [False]*s
 if not choices:return None
 return M+L+T-max(choices),local,sorted(choices)
skels=set()
for R in [5,6]:
 for K in range(R+1,21-R):
  A=K+R
  for m in range(1,K-1):
   for s in range(1,K-m):
    q=K-m-s
    for M in range(1,A-1):
     tick();num=K*K-R*R-2*M*(m+s)
     if num<=0 or num%(2*s):continue
     L=num//(2*s);T=A-M-L
     if min(L,T)<1:continue
     skels.add((M,m,L,s,T,R,q))
rows=[];bad=[];feasible=0;minimum=100;perR={R:0 for R in [5,6]}
for M,m,L,s,T,R,q in sorted(skels):
 perR[R]+=1
 target=[False]*q+[True]*M+[False]*m+[True]*L+[False]*s+[True]*T+[False]*(R-1)
 walk=area=0
 for b in target:walk+=1 if b else -1;area+=walk
 assert walk==1 and area==0
 for h in range(q,40):
  tick();e=envelope(h,M,m,L,s,T)
  if e is None:continue
  feasible+=1;r,local,choices=e;minimum=min(minimum,r-R)
  row={'h':h,'M':M,'m':m,'L':L,'s':s,'T':T,'R':R,'q':q,'min_free':r,'local_clocks':local,'possible_total_supply_counts':choices}
  rows.append(row)
  if r<R:bad.append(row)
out={'label':'COMPUTED','kind':'initial-S target necessary-count envelope, not actual old histories','R_range':[5,6],'skeletons':len(skels),'per_R':perR,'h_range':'q..39','feasible_rows':feasible,'min_free_minus_R':minimum,'residual_count':len(bad),'residual_rows':bad,'all_rows':rows,'worker_process_cpu_seconds':time.process_time()-start}
Path(__file__).with_name('initial-S-local-discovery.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k not in ['all_rows','residual_rows']}));print('first residual',json.dumps(bad[:3]))
