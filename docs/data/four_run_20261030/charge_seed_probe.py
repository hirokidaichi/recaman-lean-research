import time,json
start=time.process_time();outputs=[]

def fwd(w):
 f=[0];a=[0]
 for c in w:f.append(f[-1]+(1 if c=='A' else -1));a.append(a[-1]+f[-1])
 return [c=='A' and any(f[k]-f[t]==1 and a[k]-a[t]-(k-t)*f[t]==0 for t in range(k)) for k,c in enumerate(w)]

def rev(w):
 e=[]
 for k,c in enumerate(w):
  m=q=0;z=False
  if c=='A':
   for t in range(k-1,-1,-1):
    s=1 if w[t]=='A' else -1;m+=s;q+=(k-t)*s
    if m==1 and q==0:z=True;break
  e.append(z)
 return e

seed='S'*5+'A'*3+'S'*4+'A'*4+'S'+'A'*3
for mode,olds,gaps in [('discovery',['ASAAA'],range(1,9)),('holdout',['A','AA','SAAA','SSAAAASAAA'],range(9,17))]:
 count={'tuples':0,'valid':0,'counter':0};best=None;witness=None;done=False
 for old in olds:
  for v in gaps:
   for T in range(1,13):
    if time.process_time()-start>.7:done=True;break
    count['tuples']+=1;n=len(old);w=old+seed+'S'*v+'A'*T;e=(fwd if mode=='discovery' else rev)(w);d=[0]
    for k,c in enumerate(w):d.append(d[-1]+(c=='S')-e[k])
    if d[n]!=0 or min(d[n+1:])<1:continue
    count['valid']+=1
    F=sum(w[k]=='A' and not e[k] for k in range(n,len(w)));A=10+T;charge=A-2*F
    rec={'old':old,'word':w,'v':v,'T':T,'n':n,'EndN':[k for k,z in enumerate(e) if z],'actual_free':F,'A':A,'charge':charge,'min_positive':min(d[n+1:])}
    if best is None or charge>best['charge']:best=rec
    if charge>3:count['counter']+=1;witness=rec;done=True;break
   if done:break
  if done:break
 outputs.append({'mode':mode,'counts':count,'completed_domain':not done,'best':best,'witness':witness})
print(json.dumps({'outputs':outputs,'algorithm_cpu_seconds':time.process_time()-start},indent=2))
