"""Frozen later-length independent cases; suffix literal test, not affine keys."""
import json,random,time
ROOTS=['SSAAAASAAA','ASSAAAASAAA','SSAAAASAAAA']
LENGTHS=[192,224]
SEED=2026111303
r=random.Random(SEED);start=time.process_time();cases=0;best=None;counter=None;stop='protocol complete'
def endable(w):
 m=area=0
 for k,s in enumerate(reversed(w),1):
  a=1 if s=='A' else -1;m+=a;area+=k*a
  if m==1 and area==0:return True
 return False
for root in ROOTS:
 for limit in LENGTHS:
  for case in range(256):
   w=root;tail='';A=E=S=0;h=sum(1 if s=='A' else -1 for s in root);low=h;init=h;positions=[]
   for i in range(limit):
    supplied=endable(w)
    chooseA=r.random()<(0.55+0.1*(case%4)) and S>=E+supplied+1
    if chooseA:
     A+=1;E+=supplied
     if supplied:positions.append(len(w))
     s='A'
    else:S+=1;s='S'
    h+=1 if s=='A' else -1;low=min(low,h);tail+=s;w+=s
    assert S>=E+1
   cases+=1;free=A-E;record=dict(root=root,tail=tail,A=A,supplied=E,free=free,excess=A-3*free,depth=init-low,positions=positions)
   if best is None or record['excess']>best['excess']:best=record
   if record['excess']>0:counter=record;break
   if time.process_time()-start>3.3:stop='cooperative CPU cutoff';break
  if counter or stop!='protocol complete':break
 if counter or stop!='protocol complete':break
print(json.dumps(dict(kind='independent frozen later-length holdout; known prefixes not globally fresh',seed=SEED,roots=ROOTS,lengths=LENGTHS,cases=cases,best=best,counterexample=counter,stop=stop,worker_algorithm_cpu=time.process_time()-start),sort_keys=True))
