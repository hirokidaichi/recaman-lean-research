import json,time
from pathlib import Path
P=Path(__file__).resolve().parent;start=time.process_time()

def suppliers(w):
 a=b=0;out=[]
 for u in range(len(w)-1,-1,-1):
  x=1 if w[u]=='A' else -1;a+=x;b+=(len(w)-u)*x
  if a==1 and b==0:out.append(u)
 return sorted(out)

def loose(h,B,t):
 j=h-1;C=j*t-B
 if j<0:return []
 tri=j*(j+1)//2
 return [r for r in range(4) if -tri+r*(1-2*j)<=C<=r*r-tri and (C-r+tri)%2==0]

todo=[('',0,0,2)];nodes=0;witness=None;status=None
while todo:
 if time.process_time()-start>1.5:status='STOPPED cooperative CPU cap';break
 w,h,B,paid=todo.pop();nodes+=1
 if nodes>6000 or len(w)>=64:status='STOPPED node/length cap';break
 ls=suppliers(w);old=loose(h,B,len(w))
 for x in 'SA':
  hh=h+(1 if x=='A' else -1);pp=paid+(x=='A' and not(ls or old))
  if hh<=0 or pp>4:continue
  if hh==7:witness=w+x;status='weakened-model counter';break
  todo.append((w+x,hh,B+hh,pp))
 if witness:break
if status is None:status='complete weakened forest; COMPUTED only'

# Independent forward formulas verify the exact counter and the originals.
def forward(w):
 H=[0];B=[0]
 for x in w:H.append(H[-1]+(1 if x=='A' else -1));B.append(B[-1]+H[-1])
 return H,B

trace=[];noncontiguous=[]
if witness:
 H,B=forward(witness);paid=2
 for q,x in enumerate(witness):
  assert H[q+1]>0
  if x=='S':continue
  ss=[u for u in range(q) if H[q]==H[u]+1 and B[q]-B[u]==(q-u)*H[u]]
  assert ss==suppliers(witness[:q])
  j=H[q]-1;C=j*q-B[q];tri=j*(j+1)//2
  rs=[] if j<0 else [r for r in range(4) if 2*C>=-j*(j+1)+2*r*(1-2*j) and
      2*C<=2*r*r-j*(j+1) and (C-r+tri)%2==0]
  tight=j>=0 and (C==-tri or (j>=2 and C==1-tri) or (j>=1 and C==4-tri) or
      any(C==9-tri-6*s for s in range(j+1)))
  paid+=not(ss or rs)
  trace.append(dict(q=q,height=H[q],local_sources=ss,old_j=j,old_C=C,loose_r=rs,
                    contiguous_allowed=tight,paid=paid))
  if rs and not ss and not tight:noncontiguous.append(q)
 assert H[-1]==7 and paid<=4 and noncontiguous

boundaries=[]
for w,h in [('S'*8+'AAAA'+'S'+'AAA',4),('S'*8+'AAAA'+'S'+'AAAA',3)]:
 H,B=forward(w);free=[];all_sources={};actual=0;S=0
 for q,x in enumerate(w):
  if x=='A':
   ss=[u for u in range(q) if H[q]==H[u]+1 and B[q]-B[u]==(q-u)*H[u]]
   assert ss==suppliers(w[:q]);all_sources[str(q)]=ss
   if ss:actual+=1
   else:free.append(q)
  else:S+=1
  assert actual+1<=S
 v=max(i for i,x in enumerate(H) if x==min(H))
 assert w[:h]=='S'*h and H[-1]==2-h
 boundaries.append(dict(word=w,h=h,H=H,free=free,all_sources=all_sources,last_minimum=v,rise=H[-1]-H[v]))
assert boundaries[0]['free']==[8,9,11,14] and boundaries[0]['rise']==6
assert boundaries[1]['free']==[8,9,11,14,16] and boundaries[1]['rise']==7
out=dict(status=status,nodes=nodes,witness=witness,trace=trace,noncontiguous_admission_clocks=noncontiguous,
         original_boundaries=boundaries,cpu_seconds=time.process_time()-start,
         evidence='COMPUTED targeted weakening and boundary audit; never an original PC5 counter')
(P/'contiguity-audit-summary.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k not in ['trace','original_boundaries']}),flush=True)
