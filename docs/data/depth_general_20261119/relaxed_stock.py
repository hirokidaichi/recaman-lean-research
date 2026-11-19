from pathlib import Path
import json,sys,hashlib,time
P=Path(__file__).resolve().parent
W='SSAAASSSSAAAASAS'
def reverse_sources(w,q):
 m=b=0;out=[]
 for k,c in enumerate(reversed(w[:q]),1):
  z=1 if c=='A' else -1;m+=z;b+=k*z
  if m==1 and b==0:out.append(q-k)
 return sorted(out) if w[q]=='A' else []
def check(N):
 w=W*N+'A';T=len(w);n=1000*(N+1);x=10*n+100*N+100
 H=[0];B=[0]
 for c in w:H.append(H[-1]+(1 if c=='A' else -1));B.append(B[-1]+H[-1])
 a=[x+(n+q+1)*H[q]-B[q]for q in range(T+1)]
 stock_indices=[16*j+r for j in range(N)for r in [2,3,9,10]]+[16*N]
 V0={0,x}|{a[q]-(n+q+1)for q in stock_indices}
 assert len(V0)<=n+1 and min(V0)==0 and max(V0)<=n*(n+1)//2
 V=set(V0);value=x;A=S=E=0;free=[];raw_sources={};decisions=[]
 for q,c in enumerate(w):
  assert value==a[q]
  r=value-(n+q+1);can_subtract=r>0 and r not in V
  assert can_subtract==(c=='S'),(N,q,c,r)
  nxt=value-(n+q+1) if can_subtract else value+(n+q+1)
  assert nxt==a[q+1]
  if c=='S':
   assert nxt>0 and nxt not in V0 and not any(nxt==a[i]for i in range(q+1))
   S+=1
  else:
   assert r<=0 or r in V0 or any(r==a[i]for i in range(q+1))
   ss=reverse_sources(w,q);raw_sources[q]=ss;E+=bool(ss);A+=1
   if not ss:free.append(q)
  assert S-E>=1
  decisions.append(can_subtract);V.add(nxt);value=nxt
 for j in range(N):
  for q,u in [(4,1),(11,8),(12,1),(14,7)]:assert 16*j+u in raw_sources[16*j+q]
 Vzero=sum(h==0 for h in H[:-1]);Flow=sum(H[q]<=0 for q in free)
 assert Vzero==5*N+1 and Flow<=4*N+1 and Vzero-Flow>=N
 row={'N':N,'T':T,'n':n,'x':x,'old_stock_size':len(V0),'old_stock_max':max(V0),'tri_n':n*(n+1)//2,'minimum_segment_value':min(a),'all_greedy_decisions':True,'every_S_arrival_reverse_novelty':True,'all_A_original_sources_reverse':True,'raw_V0_visits':Vzero,'raw_low_free':Flow,'raw_count_error':Vzero-Flow,'word_sha256':hashlib.sha256(w.encode()).hexdigest(),'canonical_prefix_reached':False}
 if N==1:row.update(word=w,old_stock=sorted(V0),values=a,raw_sources=raw_sources)
 return row
mode=sys.argv[1];ns=[1,2,3] if mode=='discovery'else[5,11];t=time.process_time();rows=[check(N)for N in ns]
(P/('relaxed-stock-'+mode+'-summary.json')).write_text(json.dumps({'mode':mode,'rows':rows,'cpu_seconds':time.process_time()-t,'scope':'COMPUTED finite local greedy decision/stock audit, not canonical prefix reachability or all-N proof'},indent=2)+'\n')
print(json.dumps(rows))
