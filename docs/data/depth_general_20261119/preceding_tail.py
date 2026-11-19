from pathlib import Path
import sys,json,hashlib
P=Path(__file__).resolve().parent
W='SSAAASSSSAAAASAS'
def check(N,L):
 n=1000*(N+L*L+1);x=(L+5)*n+100*(N+1);w=W*N+'A';T=len(w)
 H=[0];B=[0]
 for c in w:H.append(H[-1]+(1 if c=='A'else-1));B.append(B[-1]+H[-1])
 a=[x+(n+q+1)*H[q]-B[q]for q in range(T+1)]
 ps=[x-l*n+l*(l-1)//2 for l in range(L+1)]
 cs=[ps[l]-(n-l+1)for l in range(1,L+1)]
 U={0,ps[L]}|set(cs)|{a[16*j+r]-(n+16*j+r+1)for j in range(N)for r in [2,3,9,10]}|{a[16*N]-(n+16*N+1)}
 assert len(U)<=n-L+1 and min(U)==0 and max(U)<=(n-L)*(n-L+1)//2
 V=set(U);v=ps[L];past=[v];tail=[]
 for i in range(L):
  t=n-L+i+1;r=v-t
  assert r>0 and r in U
  v+=t;tail.append(v);V.add(v);past.append(v)
 assert v==x and tail==list(reversed(ps[:-1]))
 for q,c in enumerate(w):
  t=n+q+1;r=v-t;can=r>0 and r not in V
  assert can==(c=='S'),(N,L,q,c,r)
  v=v-t if can else v+t
  assert v==a[q+1]
  if c=='S':assert v not in U and all(v!=z for z in past)
  V.add(v);past.append(v)
 return {'N':N,'L':L,'n':n,'seed_clock':n-L,'x':x,'seed_value':ps[L],'seed_old_stock_size':len(U),'max_old_stock':max(U),'range_bound':(n-L)*(n-L+1)//2,'all_tail_A_forced_by_original_U':True,'all_W_greedy_and_S_novelty':True,'canonical_prefix_reached':False,'whole_raw_A_prefix_positive':False}
D=[(1,0),(1,1),(2,3),(3,10)];H=[(5,17),(11,31),(2,64)]
out={'discovery':[check(*p)for p in D],'holdout':[check(*p)for p in H],'scope':'COMPUTED finite arbitrary-seed preceding-A-tail plus W replay; not canonical prefix or C1'}
(P/'preceding-tail-summary.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
