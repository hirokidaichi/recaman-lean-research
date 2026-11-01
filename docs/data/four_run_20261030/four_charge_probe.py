import json,random,time
start=time.process_time();outputs=[]
atoms=[('A',1),('SAAA',2),('SSAAAASAAA',4)]

def forward(w):
 f=[0];a=[0]
 for x in w:f.append(f[-1]+(1 if x=='A' else -1));a.append(a[-1]+f[-1])
 return [x=='A' and any(f[k]-f[t]==1 and a[k]-a[t]-(k-t)*f[t]==0 for t in range(k)) for k,x in enumerate(w)]

def backward(w):
 out=[]
 for k,x in enumerate(w):
  z=False;c=d=0
  if x=='A':
   for t in range(k-1,-1,-1):
    s=1 if w[t]=='A' else -1;c+=s;d+=(k-t)*s
    if c==1 and d==0:z=True;break
  out.append(z)
 return out

for mode,seed,cl,ch,alo,ahi,lim in [('discovery',20261230,0,8,12,20,8),('holdout',20261231,9,16,21,30,10)]:
 rng=random.Random(seed);p0=time.process_time();cnt={'sampled':0,'zero':0,'positive':0,'counter':0};best=None;witness=None
 for ix in range(100000):
  if time.process_time()-p0>.35:reason='cooperative CPU stop; incomplete sample';break
  cnt['sampled']+=1;whole=rng.randint(cl,ch);mass=0;old=''
  while mass<whole:
   a,m=rng.choice([a for a in atoms if a[1]<=whole-mass]);old+=a;mass+=m
  if len(old)>(20 if mode=='discovery' else 40):continue
  n=len(old);A=rng.randint(alo,ahi);cuts=sorted(rng.sample(range(1,A),3));M,L,U,T=cuts[0],cuts[1]-cuts[0],cuts[2]-cuts[1],A-cuts[2]
  h,m,s,v=[rng.randint(1,lim) for _ in range(4)]
  tail='S'*h+'A'*M+'S'*m+'A'*L+'S'*s+'A'*U+'S'*v+'A'*T
  w=old+tail;b=len(w);ends=(forward if mode=='discovery' else backward)(w);d=[0]
  for k,x in enumerate(w):d.append(d[-1]+(x=='S')-ends[k])
  if d[n]!=0:continue
  cnt['zero']+=1
  if min(d[n+1:b+1])<1:continue
  cnt['positive']+=1
  F=sum(w[k]=='A' and not ends[k] for k in range(n,b));charge=A-2*F
  rec={'old':old,'whole_mass':whole,'n':n,'h':h,'M':M,'m':m,'L':L,'s':s,'U':U,'v':v,'T':T,'word':w,'EndN':[k for k,e in enumerate(ends) if e],'A':A,'actual_free':F,'charge':charge,'min_positive':min(d[n+1:b+1])}
  if best is None or charge>best['charge']:best=rec
  if charge>3:witness=rec;cnt['counter']+=1;reason='first auxiliary charge counterexample; no target assumption';break
 else:reason='sample cap; finite sample only'
 outputs.append({'mode':mode,'seed':seed,'reason':reason,'counts':cnt,'max_charge_example':best,'witness':witness,'phase_cpu_seconds':time.process_time()-p0})
print(json.dumps({'outputs':outputs,'algorithm_cpu_seconds':time.process_time()-start},indent=2))
