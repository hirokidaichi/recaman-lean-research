from pathlib import Path
import itertools,json
B=Path(__file__).parent

def profile(w):
 h=a=0
 for b in w:h+=1 if b else -1;a+=h
 return h,2*a-h*(h+1)

def local(w):
 F=[0];A=[0]
 for b in w:F.append(F[-1]+(1 if b else -1));A.append(A[-1]+F[-1])
 return any(F[-1]-F[t]==1 and A[-1]-A[t]-(len(w)-t)*F[t]==0 for t in range(len(w)))
cases=roots=0
for n in range(9):
 for w in itertools.product([False,True],repeat=n):
  runs=[len(list(g)) for _,g in itertools.groupby(w)]
  oldroots=[profile(w[t:]) for t in range(n) if profile(w[t:])[1]==-2]
  assert len(oldroots)<=len(runs)
  for K in range(13):
   count=sum(local(w+(True,)*i) for i in range(K))
   assert count<=len(runs),(w,K,count,runs)
   assert K<=(K-count)+len(runs);cases+=1
  roots+=len(oldroots)
out={'cases':cases,'negative_key_roots':roots,'violations':0,'discovery':'all words length0..8, compact exact RLE, K0..12'}
(B/'run-budget-discovery.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
