"""Frozen source-conditioned sampled falsifier; not exhaustive."""
import random,time,json,sys
mode=sys.argv[1];assert mode in ('discovery','holdout')
seed=20261130 if mode=='discovery' else 20261131
rng=random.Random(seed);start=time.process_time()
rl,rh=(5,8) if mode=='discovery' else (9,13)
cl,ch=(3,12) if mode=='discovery' else (13,28)
atoms=[('A',1),('SAAA',2),('SSAAAASAAA',4)]

def cumulative(w):
 f=[0];ar=[0]
 for c in w:f.append(f[-1]+(1 if c=='A' else -1));ar.append(ar[-1]+f[-1])
 return f,ar

def forward(w):
 f,a=cumulative(w)
 return [c=='A' and any(f[k]-f[t]==1 and a[k]-a[t]-(k-t)*f[t]==0 for t in range(k)) for k,c in enumerate(w)]

def backward(w):
 out=[]
 for k,c in enumerate(w):
  hit=False;m=q=0
  if c=='A':
   for t in range(k-1,-1,-1):
    z=1 if w[t]=='A' else -1;m+=z;q+=(k-t)*z
    if m==1 and q==0:hit=True;break
  out.append(hit)
 return out

counts={x:0 for x in ['sampled','integer_shape','source_P2','zero','positive','C_gt5','whole_mass_gt_target','full_counter']}
best=None;witness=None
for ix in range(200000):
 if time.process_time()-start>.8:reason='CPU cooperative stop; incomplete sample';break
 counts['sampled']+=1
 target_mass=rng.randint(cl,ch);old='';whole=0
 while whole<target_mass:
  choices=[x for x in atoms if x[1]<=target_mass-whole]
  a,mass=rng.choice(choices);old+=a;whole+=mass
 if len(old)>70:continue
 n=len(old);t=rng.randrange(n);u=old[t:]
 C=sum(1 if c=='A' else -1 for c in u)
 if not 1<=C<=13:continue
 D=cumulative(u)[1][-1];R=rng.randint(rl,rh)
 A=rng.randint(2*R+2,min(29,R+16));T=rng.randint(3,R+1);H=A-T
 if H<3:continue
 cuts=sorted(rng.sample(range(1,H),2));M=cuts[0];L=cuts[1]-cuts[0];U=H-cuts[1]
 if M+L>=R and A<2*R+3:continue
 if M+L<R and A>R+12:continue
 s,v=rng.randint(1,10),rng.randint(1,10)
 num=A*(A-2*R)-(D+C*(C-1)//2)-2*(M+L)*s-2*H*v
 if num%(2*M):continue
 m=num//(2*M);h=C+A-R-m-s-v
 if m<1 or h<1:continue
 tail='S'*h+'A'*M+'S'*m+'A'*L+'S'*s+'A'*U+'S'*v+'A'*T+'S'*(R-1)
 if len(tail)>64:continue
 counts['integer_shape']+=1
 w=old+tail+'A';b=len(w)-1;head=b-(R-1)-T;local=head+2
 f,ar=cumulative(w)
 assert f[b]-f[t]==1 and ar[b]-ar[t]-(b-t)*f[t]==0
 assert f[local]-f[head-1]==1 and ar[local]-ar[head-1]-(local-head+1)*f[head-1]==0
 counts['source_P2']+=1
 e=(forward if mode=='discovery' else backward)(w);d=[0]
 for k,c in enumerate(w):d.append(d[-1]+(c=='S')-e[k])
 if d[n]!=0:continue
 counts['zero']+=1
 if min(d[n+1:b+1])<1:continue
 counts['positive']+=1;counts['C_gt5']+=C>5;counts['whole_mass_gt_target']+=whole>C
 free=sum(w[k]=='A' and not e[k] for k in range(n,b));margin=free-R
 rec={'old':old,'whole_mass':whole,'target_source':t,'target_mass':C,'R':R,'h':h,'M':M,'m':m,'L':L,'s':s,'U':U,'v':v,'T':T,'j':R-1,'word':w,'n':n,'target':b,'local_source':head-1,'local_clock':local,'EndN':[k for k,z in enumerate(e) if z],'full_free':free,'margin':margin,'min_positive':min(d[n+1:b+1])}
 if best is None or margin<best['margin']:best=rec
 if free<R:counts['full_counter']+=1;witness=rec;reason='first full-tail counterexample';break
else:reason='sample limit; no exhaustive claim'
print(json.dumps({'mode':mode,'seed':seed,'reason':reason,'counts':counts,'best_margin_example':best,'witness':witness,'algorithm_cpu_seconds':time.process_time()-start},indent=2))
