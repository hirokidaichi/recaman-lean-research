from pathlib import Path
import json,itertools
B=Path(__file__).parent

def supply(w):
 m=a=0
 for k,c in enumerate(reversed(w),1):
  sg=1 if c else -1;m+=sg;a+=k*sg
  if m==1 and a==0:return True
 return False
rows=[]
for seed in range(128):
 runs=[(bool(seed>>i&1),[0,1,4,17][(seed+3*i)%4]) for i in range(seed%7)]
 w=tuple(b for b,n in runs for _ in range(n))
 for K in [0,1,3,17,31]:
  supplied=sum(supply(w+(True,)*i) for i in range(K))
  assert supplied<=len(runs),(seed,K,runs,supplied)
  rows.append([seed,K,supplied])
for h,Budget in itertools.product([1,5,23],[2,7,19]):
 w=(False,)*h;K=Budget+1;s=sum(supply(w+(True,)*i) for i in range(K))
 assert s==1 and K-s==Budget
out={'cases':len(rows),'violations':0,'sharp_controls':9,'holdout':'128 explicit RLEs incl zero/repeated runs, K0/1/3/17/31; reversed suffix checker'}
(B/'run-budget-holdout.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
