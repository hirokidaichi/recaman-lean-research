"""Exact predeclared age inequality/envelope and actual sharp-family tests."""
from itertools import product
import json,time
start=time.process_time()
words=collisions=0
for L in range(13):
 for w in product([-1,1],repeat=L):
  H=B=0
  for e in w:H+=e;B+=H
  words+=1
  assert -L*L+H*H+2*(L+1)*H<=4*B<=L*L-H*H+2*(L+1)*H
  if H!=1 and B%(H-1)==0:
   n=B//(H-1)
   if n>=L+1:
    collisions+=1
    assert 4*n<=L*L+4*L
rows=[]
for m in [1,2,3,5,11,17]:
 b=m*m-1;x=m*m+1;v='A'*(m+1)+'S'*(m-1);w=v+'A';L=2*m;n=m*m+2*m
 cs=[x+(j-1)*b+(j*j-j-2)//2 for j in range(m+1)]
 stock={0,x,*cs};seen=set(stock);X=x;H=[0];B=[0];values=[x];signs=[]
 for q,expected in enumerate(w):
  c=X-(b+q+1)
  got='S' if c>0 and c not in seen else 'A'
  assert got==expected,(m,q,got,expected,c)
  X=c if got=='S' else X+b+q+1
  signs.append(got);values.append(X);seen.add(X)
  H.append(H[-1]+(1 if got=='A' else -1));B.append(B[-1]+H[-1])
 suppliers=[u for u in range(L) if H[L]==H[u]+1 and B[L]-B[u]==(L-u)*H[u]]
 assert not suppliers
 assert values[L]-n==x and 4*n==L*L+4*L
 rows.append({'m':m,'base':b,'initial_current':x,'initial_distinct_stock':sorted(stock),'word':w,'outputs':values,'age':L,'step_clock':n,'final_original_P2_sources':suppliers,'equality':True})
print(json.dumps({'words':words,'eligible_nonP2_numeric_equations':collisions,'sharp_actual_controls':rows,'worker_internal_cpu_seconds':time.process_time()-start},indent=2))
