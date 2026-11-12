import sys,time,json,random
start=time.process_time();mode=sys.argv[1]
def root(h):
 H=P=0;old=set()
 for q in range(h):old.add((H,P-q*H));H-=1;P+=H
 return (h,H,P,old,set(),h,0,0,0,0,'')
def step(s,ch):
 q,H,P,old,local,S,E,A,F,D,w=s
 key=(H-1,P-q*(H-1));o=key in old;l=key in local;end=o or l
 local=local|{(H,P-q*H)}
 if ch=='A':A+=1;E+=end;F+=not end;D+=o and not l;H+=1
 else:S+=1;H-=1
 return (q+1,H,P+H,old,local,S,E,A,F,D,w+ch)
def literal(h,w):
 word='S'*h+w;S=E=A=F=D=0;positive=True
 for q,ch in enumerate(word):
  if ch=='S':S+=1
  else:
   A+=1;mass=area=0;old=local=False
   for k,x in enumerate(reversed(word[:q]),1):
    v=1 if x=='A' else -1;mass+=v;area+=k*v
    if mass==1 and area==0:
     if q-k<h:old=True
     else:local=True
   E+=old or local;F+=not (old or local);D+=old and not local
  positive &= E+1<=S
 return dict(h=h,tail=w,A=A,E=E,F=F,D=D,positive=bool(positive),excess=D-F)
count=valid=0;best=None;counter=None
if mode=='beam':
 for h in (1,2,3,4,8,16):
  states=[root(h)]
  for depth in range(128):
   children=[]
   for s in states:
    for ch in 'AS':
     ns=step(s,ch);count+=1
     if ns[5]<ns[6]+1:continue
     valid+=1;children.append(ns)
     row=dict(h=h,tail=ns[-1],A=ns[7],E=ns[6],F=ns[8],D=ns[9],positive=True,excess=ns[9]-ns[8])
     score=(row['D']/(row['F']+1),row['excess'],row['D'])
     if best is None or score>best[0]:best=(score,row)
     if ns[9]>ns[8]:counter=literal(h,ns[-1]);assert counter['positive'] and counter['excess']>0;break
    if counter:break
   if counter:break
   states=sorted(children,key=lambda x:(x[9]/(x[8]+1),x[9]-x[8],x[9]),reverse=True)[:40]
   if time.process_time()-start>1.4:raise RuntimeError('cooperative algorithm cap')
  if counter:break
 if best:
  verified=literal(best[1]['h'],best[1]['tail'])
  assert all(verified[k]==best[1][k] for k in ('A','E','F','D','positive','excess'))
  best=verified
else:
 rng=random.Random(2026111309)
 for h in (5,9,17):
  for length in (192,224):
   for j in range(32):
    prob=.55+.10*(j%3);w=''.join('A' if rng.random()<prob else 'S' for _ in range(length));row=literal(h,w);count+=1
    if not row['positive']:continue
    valid+=1
    score=(row['D']/(row['F']+1),row['excess'],row['D'])
    if best is None or score>best[0]:best=(score,row)
    if row['excess']>0:counter=row;break
    if time.process_time()-start>1.4:raise RuntimeError('cooperative algorithm cap')
   if counter:break
  if counter:break
 if best:best=best[1]
print(json.dumps(dict(mode=mode,scope='finite falsifier, no absence proof',count=count,valid=valid,best=best,counterexample=counter,algorithm_cpu=time.process_time()-start),sort_keys=True))
