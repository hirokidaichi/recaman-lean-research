import sys,time,json,itertools,random,hashlib
start=time.process_time();mode=sys.argv[1]
def measure(w):
 h=a=0
 for x in w:h+=1 if x=='A' else -1;a+=h
 return h,a
def sources(w,q):
 ss=[]
 if mode=='reverse':
  h=a=0
  for k,x in enumerate(reversed(w[:q]),1):
   v=1 if x=='A' else -1;h+=v;a+=k*v
   if h==1 and a==0:ss.append(q-k)
 else:
  hs=[0];ps=[0]
  for x in w[:q]:hs.append(hs[-1]+(1 if x=='A' else -1));ps.append(ps[-1]+hs[-1])
  for t in range(q):
   if hs[q]-hs[t]==1 and ps[q]-ps[t]-(q-t)*hs[t]==0:ss.append(t)
 return sorted(ss)
if mode=='reverse':
 loops=[''.join(w) for n in range(2,13,2) for w in itertools.product('AS',repeat=n) if w.count('A')==n//2]
else:
 rng=random.Random(2026111306);loops=[]
 for n in (14,16):
  ws=set()
  while len(ws)<32:
   w=list('A'*(n//2)+'S'*(n//2));rng.shuffle(w);ws.add(''.join(w))
  loops+=sorted(ws)
digest=hashlib.sha256();samples=[];maxd=0;neutral=0
for z in loops:
 L=len(z);mass,B=measure(z);assert mass==0
 d=L+abs(B)+2;old='S'*(d+1)+'A'*d+'S'*(2*d-2)+'A'*(d+1);q=5*d-1;c=4*d-1
 new=old[:c]+z+old[c:]
 so=sources(old,q);sn=sources(new,q+L)
 assert old[q]==new[q+L]=='A' and so==[d] and sn==[],dict(z=z,d=d,old=so,new=sn)
 for w in (old,new):
  h=0
  for x in w:
   h+=1 if x=='A' else -1
   assert h<=-1,dict(z=z,d=d,height=h)
 row=dict(z=z,L=L,B=B,d=d,q=q,c=c,old_sources=so,new_sources=sn)
 digest.update((json.dumps(row,sort_keys=True)+'\n').encode())
 if d>maxd:maxd=d;samples.append(row)
 neutral+=B==0
 if time.process_time()-start>1.5:raise RuntimeError('cooperative algorithm cap')
print(json.dumps(dict(mode=mode,scope='finite universal-loop-paper falsifier; not proof of all z',cases=len(loops),neutral_area0_cases=neutral,max_d=maxd,all_positive_height_barrier=True,all_old_unique=True,all_new_unsupplied=True,case_output_sha256=digest.hexdigest(),record_samples=samples,algorithm_cpu=time.process_time()-start),sort_keys=True))
