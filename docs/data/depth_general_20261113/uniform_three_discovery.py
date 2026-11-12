"""Frozen beam falsifier, original affine-area source keys; no depth or width cutoff."""
from collections import Counter
import json,time
ROOTS=['','A','AA','SAAA','ASAAA','SAAASAAA']
LIMIT=160
BEAM=64
started=time.process_time();visits=0;best=None;counter=None;stop='protocol complete'
def literal(w):
 m=z=0
 for k,s in enumerate(reversed(w),1):
  v=1 if s=='A' else -1;m+=v;z+=k*v
  if m==1 and z==0:return True
 return False

def verify(root,tail):
 w=root;A=E=S=0;h=sum(1 if s=='A' else -1 for s in root);low=h;initial=h
 positions=[]
 for i,s in enumerate(tail):
  if s=='A':
   A+=1
   if literal(w):E+=1;positions.append(len(w))
  else:S+=1
  assert S>=E+1,(root,tail,i)
  h+=1 if s=='A' else -1;low=min(low,h);w+=s
 return dict(root=root,tail=tail,A=A,supplied=E,free=A-E,depth=initial-low,positions=positions,excess=A-3*(A-E))
for root in ROOTS:
 h=P=0;orig=set()
 for t,s in enumerate(root):orig.add((h,P-t*h));h+=1 if s=='A' else -1;P+=h
 initial=h
 states=[('',h,P,0,0,0,frozenset(orig),h)]
 for length in range(LIMIT):
  if time.process_time()-started>3.3:stop='cooperative CPU cutoff';break
  nxt=[]
  for tail,h,P,A,E,S,orig,low in states:
   q=len(root)+length;sup=(h-1,P-q*(h-1)) in orig;neworig=orig|{(h,P-q*h)}
   for sign in ['A','S']:
    a=A+(sign=='A');e=E+(sign=='A' and sup);s=S+(sign=='S')
    if s<e+1:continue
    hh=h+(1 if sign=='A' else -1);word=tail+sign;v=(word,hh,P+hh,a,e,s,neworig,min(low,hh));nxt.append(v);visits+=1
    free=a-e;excess=a-3*free
    if best is None or (excess,a)>(best['excess'],best['A']):best=verify(root,word)
    if excess>0:counter=verify(root,word);break
   if counter:break
  if counter:break
  nxt.sort(key=lambda x:(x[3]/max(1,x[3]-x[4]),x[3]-3*(x[3]-x[4]),x[4],-abs(x[1]-initial)),reverse=True)
  # Keep multiple actual histories for the same counts; this is heuristic, not exhaustive.
  states=nxt[:BEAM]
 if counter or stop!='protocol complete':break
print(json.dumps(dict(kind='finite heuristic discovery, not exhaustive',roots=ROOTS,max_tail=LIMIT,beam=BEAM,visits=visits,best=best,counterexample=counter,stop=stop,worker_algorithm_cpu=time.process_time()-started),sort_keys=True))
