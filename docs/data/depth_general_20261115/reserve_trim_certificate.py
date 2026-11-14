import json,time
start=time.process_time()
def query(w,q,cut=0):
 if q<len(w) and w[q]!='A':return []
 m=a=0;out=[]
 for k,x in enumerate(reversed(w[:q]),1):
  v=1 if x=='A' else -1;m+=v;a+=k*v
  if m==1 and a==0 and q-k>=cut:out.append(q-k)
 return sorted(out)
def scan(w):
 H=[0];F=[0];E=[0];S=[0];positive=True
 for q,ch in enumerate(w):
  e=ch=='A' and bool(query(w,q));E.append(E[-1]+e);S.append(S[-1]+(ch=='S'));F.append(F[-1]+(ch=='A' and not e));H.append(H[-1]+(1 if ch=='A' else -1));positive &= E[-1]+1<=S[-1]
 return dict(H=H,F=F,E=E,S=S,positive=bool(positive))
P='S'+'A'*11+'S'*16+'A'*3+'S'*3+'A'*4+'SA'+'S'*4+'A'*7
w='S'*11+P+'A'+'S'*4+'A'*4
cases=[('plateau',w,12),('SA','SA',1),('tail_starts_S','SSSA',2),('last_S_source','SSSSSAAA',5),('empty_tail','S',1),('empty_head','SA',0)]
rows=[]
for name,w,h in cases:
 r=scan(w);assert r['positive'];K=len(w)-h
 U=max([0]+[max(0,r['E'][h+k]+1-(r['S'][h+k]-h)) for k in range(1,K+1)])
 old=[]
 for q in range(K+1):
  ts=query(w,h+q)
  if ts and not any(t>=h for t in ts):old.append((q,r['H'][h+q]-r['H'][h]-1))
 V=max([0]+[v for _,v in old]);Cstar=max(U,V);valid=[]
 for C in range(h+1):
  g='S'*C+w[h:];s=scan(g)
  targets=all(bool(query(w,h+q))==bool(query(g,C+q)) for q in range(K+1))
  counts=all(r['E'][h+k]==s['E'][C+k] and r['F'][h+k]==s['F'][C+k] for k in range(K+1))
  if targets and counts and s['positive']:valid.append(C)
 assert valid==list(range(Cstar,h+1)),(name,U,V,valid)
 rows.append(dict(name=name,h=h,K=K,U=U,V=V,least_head=Cstar,valid_heads=valid,full_free=r['F'][-1],old_targets_and_depths=old))
print(json.dumps({'scope':'six exact finite normalizer tests, not a proof for all histories; default extension A, target qK included','rows':rows,'algorithm_cpu_seconds':time.process_time()-start},sort_keys=True))
