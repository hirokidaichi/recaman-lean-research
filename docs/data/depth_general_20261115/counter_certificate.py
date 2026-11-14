import json,time
start=time.process_time()
def literal(w,h):
 H=[0];B=[0];sources={};S=E=A=F=D=0;positive=True;prefix=[]
 for q,ch in enumerate(w):
  ts=[]
  if ch=='A':
   A+=1;m=a=0
   for k,x in enumerate(reversed(w[:q]),1):
    v=1 if x=='A' else -1;m+=v;a+=k*v
    if m==1 and a==0:ts.append(q-k)
   ts.sort();E+=bool(ts);F+=not ts;D+=bool(ts) and not any(t>=h for t in ts)
  else:S+=1
  sources[q]=ts
  H.append(H[-1]+(1 if ch=='A' else -1));B.append(B[-1]+H[-1]);positive &= E+1<=S
  prefix.append((A,S,E,F,D))
 return dict(length=len(w),initial_S=h,H=H,B=B,sources=sources,A=A,S=S,E=E,F=F,D=D,positive=positive,prefix=prefix)
def forward(w):
 H=B=0;table={};out={}
 for q,ch in enumerate(w):
  key=(H-1,B-q*(H-1));out[q]=sorted(table.get(key,[])) if ch=='A' else []
  table.setdefault((H,B-q*H),[]).append(q)
  H+=1 if ch=='A' else -1;B+=H
 return out
P='S'+'A'*11+'S'*16+'A'*3+'S'*3+'A'*4+'SA'+'S'*4+'A'*7
Q=P+'A'+'S'*4+'A'*4
w='S'*11+Q;r=literal(w,12);assert r['sources']==forward(w)
assert len(P)==51 and len(Q)==60 and len(w)==71
assert r['positive'] and max(r['H'][1:])<=-1
assert r['sources'][62]==[11] and r['sources'][70]==[11]
for q,t in [(67,36),(68,49),(69,66)]:assert t in r['sources'][q]
assert all(w[q]=='S' or r['sources'][q] for q in range(63,70))
level=[t for t in range(60) if r['H'][11+t]==r['H'][11]]
Bnorm=lambda t:r['B'][11+t]-r['B'][11]-t*r['H'][11]
assert level==[0,2,22,50,54,58]
assert [Bnorm(t) for t in level]==[0,-1,99,-1,3,-1]
free=[q for q,ch in enumerate(w) if ch=='A' and not r['sources'][q]]
latest=[max(t for t in free if t<q) for q in (62,70)];assert latest[0]==latest[1]
b='SSSAAAASAAA';bnd=literal(b,3);assert bnd['sources']==forward(b) and bnd['positive']
assert bnd['H'][-1]-bnd['H'][3]==6 and bnd['F']==4
print(json.dumps({'scope':'exact finite two-implementation certificate, not an orbit reachability or infinite absence proof','word':w,'h':12,'length':71,'counts':{k:r[k] for k in ('A','S','E','F','D','positive')},'targets':{q:r['sources'][q] for q in (62,67,68,69,70)},'latest_free_for_targets':latest,'height_source_table':[(t,Bnorm(t)) for t in level],'all_actual_supplied':{q:ts for q,ts in r['sources'].items() if ts},'factor_one_boundary':{'word':b,'rise':6,'free':4,'positive':True,'actual_sources':{q:ts for q,ts in bnd['sources'].items() if ts}},'algorithm_cpu_seconds':time.process_time()-start},sort_keys=True))
