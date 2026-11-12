import time,json,sys,random
start=time.process_time();mode=sys.argv[1]
def literal(h,tail):
 w='S'*h+tail;F=E=S=A=0;prev=None;pair=None;hits=[];positive=True
 for q,ch in enumerate(w):
  if ch=='S':S+=1
  else:
   A+=1;m=a=0;o=l=False
   for k,x in enumerate(reversed(w[:q]),1):
    v=1 if x=='A' else -1;m+=v;a+=k*v
    if m==1 and a==0:
     if q-k<h:o=True
     else:l=True
   E+=o or l;F+=not(o or l)
   if o and not l:
    hits.append((q,F))
    if prev and prev[1]==F:pair=[prev[0],q]
    prev=(q,F)
  positive &= E+1<=S
 return dict(h=h,tail=tail,A=A,E=E,F=F,positive=bool(positive),hits=hits,pair=pair)
def root(h):
 H=P=0;old=set()
 for q in range(h):old.add((H,P-q*H));H-=1;P+=H
 return (h,H,P,old,set(),h,0,0,0,None,'')
def step(s,ch):
 q,H,P,old,local,S,E,A,F,prev,w=s;key=(H-1,P-q*(H-1));o=key in old;l=key in local;sup=o or l
 local=local|{(H,P-q*H)};pair=None
 if ch=='A':
  if not sup and prev:return None,None
  A+=1;E+=sup;F+=not sup
  if o and not l:
   if prev is not None:pair=[prev,q]
   prev=q
  H+=1
 else:S+=1;H-=1
 return (q+1,H,P+H,old,local,S,E,A,F,prev,w+ch),pair
counter=None;visits=valid=0;maxfrozen=0
if mode=='beam':
 for h in (1,2,3,4,8,16):
  ss=[root(h)]
  for depth in range(160):
   cs=[]
   for s in ss:
    for ch in 'AS':
     visits+=1;ns,pair=step(s,ch)
     if ns is None or ns[5]<ns[6]+1:continue
     valid+=1;cs.append(ns)
     if ns[9] is not None:maxfrozen=max(maxfrozen,len(ns[-1])-(ns[9]-h))
     if pair:
      row=literal(h,ns[-1]);assert row['positive'] and row['pair'];counter=row;break
    if counter:break
   if counter:break
   ss=sorted(cs,key=lambda x:(x[9] is not None,x[8],x[7]),reverse=True)[:48]
   if time.process_time()-start>1.4:raise RuntimeError('cooperative cap')
  if counter:break
else:
 rng=random.Random(2026111310)
 for h in (5,9,17):
  for length in (192,224):
   for j in range(32):
    w=''.join('A' if rng.random()<(.55+.1*(j%3)) else 'S' for _ in range(length));row=literal(h,w);visits+=1
    if not row['positive']:continue
    valid+=1
    if row['pair']:counter=row;break
    if time.process_time()-start>1.4:raise RuntimeError('cooperative cap')
   if counter:break
  if counter:break
print(json.dumps(dict(mode=mode,scope='finite latest-free map falsifier, not parent inequality proof',visits=visits,valid=valid,max_frozen_tail=maxfrozen,counterexample=counter,algorithm_cpu=time.process_time()-start),sort_keys=True))
