"""Frozen sampled falsifier, not an exhaustive finite classification."""
import sys,random,time,json
mode=sys.argv[1]
assert mode in ('discovery','holdout')
seed=20261030 if mode=='discovery' else 20261031
rng=random.Random(seed);cpu0=time.process_time()
oldwords=['A','AA','SAAA'] if mode=='discovery' else ['SSAAAASAAA','SAAASAAA','AASAAA']
lo,hi,cap=(4,10,6) if mode=='discovery' else (11,14,10)

def metrics(w):
 f=[0];ar=[0]
 for x in w:
  f.append(f[-1]+(1 if x=='A' else -1));ar.append(ar[-1]+f[-1])
 return f,ar

def supplies_forward(w):
 f,ar=metrics(w)
 return [x=='A' and any(f[k]-f[t]==1 and ar[k]-ar[t]-(k-t)*f[t]==0 for t in range(k)) for k,x in enumerate(w)]

def supplies_backward(w):
 out=[]
 for k,x in enumerate(w):
  hit=False;mass=area=0
  if x=='A':
   for t in range(k-1,-1,-1):
    sign=1 if w[t]=='A' else -1
    mass+=sign;area+=(k-t)*sign
    if mass==1 and area==0:hit=True;break
  out.append(hit)
 return out

count={'sampled':0,'integral_positive_m_h':0,'literal_P2_pass':0,'zero_pass':0,'allpositive_pass':0,'head_counter':0,'full_counter':0}
controls=[];witness=None
for idx in range(200000):
 if time.process_time()-cpu0>1.6:reason='cooperative CPU stop; incomplete sample';break
 count['sampled']+=1
 old=rng.choice(oldwords);R=rng.randint(lo,hi)
 M,L,U=[rng.randint(1,cap) for _ in range(3)]
 T=rng.randint(3,R+1);s,v=rng.randint(1,cap),rng.randint(1,cap)
 C=sum(1 if x=='A' else -1 for x in old);D=metrics(old)[1][-1]
 A=M+L+U+T;H=M+L+U
 num=A*(A-2*R)-(D+C*(C-1)//2)-2*(M+L)*s-2*H*v
 if num%(2*M):continue
 m=num//(2*M);h=C+A-R-m-s-v
 if m<1 or h<0:continue
 count['integral_positive_m_h']+=1
 tail='S'*h+'A'*M+'S'*m+'A'*L+'S'*s+'A'*U+'S'*v+'A'*T+'S'*(R-1)
 w=old+tail+'A';n=len(old);head=n+len(tail)-(R-1)-T;b=len(w)-1
 f,ar=metrics(w)
 local=head+2
 assert f[b]==1 and ar[b]==0
 assert f[local]-f[head-1]==1 and ar[local]-ar[head-1]-(local-head+1)*f[head-1]==0
 count['literal_P2_pass']+=1
 ends=(supplies_forward if mode=='discovery' else supplies_backward)(w)
 d=[0]
 for k,x in enumerate(w):d.append(d[-1]+(x=='S')-ends[k])
 if d[n]!=0:continue
 count['zero_pass']+=1
 if not all(d[k]>=1 for k in range(n+1,b+1)):continue
 count['allpositive_pass']+=1
 fh=sum(w[k]=='A' and not ends[k] for k in range(n,head))
 ff=sum(w[k]=='A' and not ends[k] for k in range(n,b))
 rec={'old':old,'R':R,'h':h,'M':M,'m':m,'L':L,'s':s,'U':U,'v':v,'T':T,'j':R-1,'word':w,'n':n,'head':head,'target':b,'local_source':head-1,'local_clock':local,'EndN':[k for k,z in enumerate(ends) if z],'head_free':fh,'full_free':ff,'d_at_n':d[n],'min_positive':min(d[n+1:b+1]),'target_supplied':ends[b]}
 if len(controls)<3:controls.append(rec)
 if fh<R:
  count['head_counter']+=1;count['full_counter']+=ff<R
  witness=rec;reason='first head-counterexample; not necessarily full-tail counterexample';break
else:reason='sample cap; randomized finite sample only'
print(json.dumps({'mode':mode,'seed':seed,'reason':reason,'counts':count,'controls':controls,'witness':witness,'worker_algorithm_cpu_seconds':time.process_time()-cpu0},indent=2))
