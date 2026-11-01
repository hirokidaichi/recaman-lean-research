"""Exact local clocks, sound count envelope only. No actual old history is asserted."""
from pathlib import Path
import json,time
start=time.process_time()
def tick():
 if time.process_time()-start>9.5:raise TimeoutError('cooperative9.5CPU stop before nominal10s RLIMIT')
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
for R in range(5,8):
 for K in range(R+1,21-R):
  for d in range(1,21):
   for L in range(1,21):
    tick();num=K*K-R*R-2*d*K
    if num<=0 or num%(2*L):continue
    s=num//(2*L);m=K-s;T=K+R-d-L
    if min(m,s,T)<1 or max(m,s)>38:continue
    for M in range(d,21-L-T):skels.add((M,m,L,s,T,R,d))
rows=[];bad=[];feasible=0;minimum=100;perR={R:0 for R in range(5,8)}
for M,m,L,s,T,R,d in sorted(skels):
 perR[R]+=1
 for h in range(40):
  tick();e=envelope(h,M,m,L,s,T)
  if e is None:continue
  feasible+=1;r,local,choices=e;minimum=min(minimum,r-R)
  row={'h':h,'M':M,'m':m,'L':L,'s':s,'T':T,'R':R,'d':d,'min_free':r,'local_clocks':local,'possible_total_supply_counts':choices}
  rows.append(row)
  if r<R:bad.append(row)
controls={'E430_R5_minfree':envelope(39,1,6,5,1,6),'R5_M5_clock0':sorted(roots([False]*2+[True]*5+[False]*6+[True]*5+[False],6)),'M4_R5_second_clock4':sorted(roots([False]+[True]*4+[False]*6,6)),'R4_middleS_clock0':sorted(roots([False]*2+[True]*4+[False],5))}
out={'label':'COMPUTED','kind':'necessary-count envelope, not actual old histories','R_range':[5,7],'skeletons':len(skels),'per_R':perR,'h_cases_each':40,'feasible_rows':feasible,'min_free_minus_R':minimum,'residual_count':len(bad),'residual_rows':bad,'controls':controls,'all_rows':rows,'worker_process_cpu_seconds':time.process_time()-start}
Path(__file__).with_name('first-A-local-discovery.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k not in ['all_rows','residual_rows']}));print('first residual',json.dumps(bad[:3]))
