"""Predeclared nested zero-mean bridge family; exact all-prior-source audit."""
import json,time
start=time.process_time()

def inspect(w,h):
 H=[0];B=[0];O={(0,0)};C=set();low=set();free=[];actual={};bad=[];positive=True
 for q,s in enumerate(w):
  c=(H[-1]-1,(q+1)*(H[-1]-1)-B[-1]);sup=[]
  if s=='A':
   sup=[u for u in range(q) if H[q]==H[u]+1 and B[q]-B[u]==(q-u)*H[u]]
   actual[q]=sup
   if not sup:
    free.append(q)
    if H[-1]<=1-h:low.add(c)
   C.add(c)
  hp=H[-1]+(1 if s=='A' else -1);bp=B[-1]+hp;op=(hp,(q+2)*hp-bp)
  if s=='S' and (op in O or op in C):bad.append(q+1)
  O.add(op);H.append(hp);B.append(bp)
  if sum(t=='S' for t in w[:q+1])-sum(bool(v) for v in actual.values())<1:positive=False
 D=max(0,-h-min(H));Flow=sum(H[q]<=1-h for q in free)
 return {'word':w,'h':h,'D':D,'K_LOW':len(low),'F_LOW':Flow,'classes':sorted(low),'positive':positive,'return':H[-1],'bad_S':bad,'actual_sources':actual,'free':free}

rows=[]
for d in [1,3,5,7]:
 t=2*d+1;core='A'*(3*d)+'S'*(4*d)+'A'*t+'S'*(2*t+2)+'A'*(t+2+d)
 h=(len(core)//2)+3;w='S'*h+core+'AA'
 r=inspect(w,h);r['d']=d;rows.append(r)
 if time.process_time()-start>.65:break
print(json.dumps({'family':'A^(3d) S^(4d) Z_(2d+1) A^d, d odd, initial h=coreA+3, suffix AA','rows':rows,'worker_internal_cpu_seconds':time.process_time()-start},indent=2))
