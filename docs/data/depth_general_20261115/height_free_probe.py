import json,sys,time,random
start=time.process_time();mode=sys.argv[1]
def root(h):
 H=B=0;points=set()
 for q in range(h):points.add((H,B-q*H));H-=1;B+=H
 return (h,H,B,points,h,0,0,0,'')
def step(s,ch,h):
 q,H,B,ps,S,E,F,A,w=s;end=ch=='A' and (H-1,B-q*(H-1)) in ps
 ps=ps|{(H,B-q*H)}
 if ch=='A':E+=end;F+=not end;A+=1;H+=1
 else:S+=1;H-=1
 return (q+1,H,B+H,ps,S,E,F,A,w+ch)
def literal(h,tail):
 w='S'*h+tail;S=E=F=0;H=0;best=0;positive=True;at=None
 for q,ch in enumerate(w):
  if ch=='S':S+=1;H-=1
  else:
   m=a=0;end=False
   for k,x in enumerate(reversed(w[:q]),1):
    v=1 if x=='A' else -1;m+=v;a+=k*v;end|=m==1 and a==0
   E+=end;F+=not end;H+=1
  positive &= E+1<=S
  if q+1>=h and H+h-2*F>best:best=H+h-2*F;at=q+1
 return dict(h=h,tail=tail,positive=bool(positive),final_rise=H+h,free=F,maximum_excess=best,violation_clock=at)
visits=valid=0;counter=None;best=None
if mode=='discovery':
 for h in (1,2,3,4,8,16,32):
  states=[root(h)]
  for depth in range(96):
   children=[]
   for s in states:
    for ch in 'AS':
     visits+=1;ns=step(s,ch,h)
     if ns[4]<ns[5]+1:continue
     valid+=1;children.append(ns);score=(ns[1]+h-2*ns[6],ns[1]+h,ns[7])
     if best is None or score>best[0]:best=(score,h,ns[-1])
     if score[0]>0:
      counter=literal(h,ns[-1]);assert counter['positive'] and counter['maximum_excess']>0;break
    if counter:break
   if counter:break
   states=sorted(children,key=lambda x:(x[1]+h-2*x[6],x[1]+h,x[7]),reverse=True)[:32]
   if visits>=100000 or time.process_time()-start>1.3:break
  if counter or visits>=100000 or time.process_time()-start>1.3:break
 if best:best=literal(best[1],best[2])
else:
 rng=random.Random(2026111503)
 for h in (5,7,11,19):
  for length in (128,160):
   for j in range(16):
    tail=''.join('A' if rng.random()<(.5+.08*(j%4)) else 'S' for _ in range(length));r=literal(h,tail);visits+=1
    if r['positive']:
     valid+=1
     if best is None or (r['maximum_excess'],r['final_rise'])>(best['maximum_excess'],best['final_rise']):best=r
     if r['maximum_excess']>0:counter=r;break
    if time.process_time()-start>1.3:break
   if counter or time.process_time()-start>1.3:break
  if counter or time.process_time()-start>1.3:break
print(json.dumps({'mode':mode,'scope':'finite original-history height/free falsifier; no absence proof','visits':visits,'valid':valid,'best':best,'counterexample':counter,'algorithm_cpu_seconds':time.process_time()-start},sort_keys=True))
