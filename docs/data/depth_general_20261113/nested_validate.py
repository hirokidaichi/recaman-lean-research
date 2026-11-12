import json,time,sys
start=time.process_time()
mode=sys.argv[1]; ns=list(range(0,9)) if mode=='reverse' else list(range(9,25))
rows=[]
for N in ns:
 w='SSS'+'SAA'+'ASSSSAAA'*N+'A'; f=[1 if x=='A' else -1 for x in w]
 h=[0]
 for x in f:h.append(h[-1]+x)
 sources={}
 for q,x in enumerate(f):
  if x!=1:continue
  ss=[]
  if mode=='reverse':
   mass=area=0
   for k,x0 in enumerate(reversed(f[:q]),1):
    mass+=x0;area+=k*x0
    if mass==1 and area==0:ss.append(q-k)
  else:
   for t in range(q):
    mass=area=0
    for x0 in f[t:q]:mass+=x0;area+=mass
    if mass==1 and area==0:ss.append(t)
  sources[q]=sorted(ss)
 E=sum(bool(v) for v in sources.values()); A=len(sources); F=A-E
 S=Ec=Ac=0; positive=True
 for q,x in enumerate(f):
  S+=x==-1; Ac+=x==1; Ec+=bool(sources.get(q,[]))
  positive &= Ec+1<=S
 qs=[6+8*j for j in range(N+1)]
 selected={q:sources[q] for q in qs}
 r=-5
 low=sum(2*(r-h[q])-1 for q,x in enumerate(f) if x==1 and h[q]<r)
 above=lambda x:max(0,x-r)*(max(0,x-r)+1)
 below=lambda x:max(0,r-x)*(max(0,r-x)+1)
 P=2*sum(x-r for x in h[1:])+below(h[-1])-below(h[0])+2*low-above(h[-1])+above(h[0])
 Q=sum(2*(h[3]-r)*(q-3-1)-2 for q in qs)
 row=dict(N=N,length=len(w),A=A,E=E,free=F,floor=min(h),positive=bool(positive),selected_sources=selected,Q=Q,P=P)
 assert positive and min(h)>=-5 and all(v==[3] for v in selected.values()),row
 assert (A,E,F)==(4*N+3,2*N+1,2*N+2),row
 assert Q==(N+1)*(6+16*N) and P==48+32*N,row
 rows.append(row)
 if time.process_time()-start>.75:raise RuntimeError('cooperative algorithm cap')
print(json.dumps(dict(kind='finite independent validation, not all-N proof; histories overlap across N',mode=mode,rows=rows,algorithm_cpu=time.process_time()-start),sort_keys=True))
