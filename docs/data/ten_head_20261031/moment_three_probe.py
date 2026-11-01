import sys,json
split=sys.argv[1]
Ss=list(range(6,17)) if split=='discovery' else list(range(17,21))
def supply(w):
 if split=='discovery':
  fw=[0];ar=[0]
  for b in w:fw.append(fw[-1]+(1 if b else -1));ar.append(ar[-1]+fw[-1])
  return [t for t in range(len(w)) if fw[-1]-fw[t]==1 and ar[-1]-ar[t]-(len(w)-t)*fw[t]==0]
 mass=moment=0;result=[]
 for k,b in enumerate(reversed(w),1):
  a=1 if b else -1;mass+=a;moment+=k*a
  if (mass,moment)==(1,0):result.append(len(w)-k)
 return result
out={'split':split,'S_range':Ss,'heads':0,'target_cases':0,'violations':[],'by_S':{},'seen_local_clocks':[]}
seen=set()
for S in Ss:
 params={}
 for C,key,name in [(1,0,'A'),(2,0,'AA'),(2,-2,'SAAA')]:
  for v in range(1,4):
   for R in range(5,11):
    T=R+v-C;B=R*R+2*C*(S+v)-v*v+key//2
    if not (4*S+6<=B<=6*S+4 and T<=R+1 ):continue
    params.setdefault(B,[]).append((C,key,name,v,R,T))
 for h in range(1,S-1):
  for m in range(1,S-h):
   s=S-h-m
   for M in range(1,S-1):
    for L in range(1,S-M):
     U=S-M-L;out['heads']+=1
     B=S*S-2*(M*(m+s)+L*s)
     if B not in params:continue
     z=[False]*h+[True]*M+[False]*m+[True]*L+[False]*s+[True]*U
     head_lower=max(S-10,min(4,S//2))
     for C,key,name,v,R,T in params[B]:
      out['target_cases']+=1
      clocks={i:supply(z+[False]*v+[True]*i) for i in range(T)}
      seen.update(i for i,ts in clocks.items() if ts)
      free=[i for i,ts in clocks.items() if not ts]
      margin=3-(T-len(free))
      q=out['by_S'].setdefault(str(S),{'cases':0,'min_margin':100,'worst':None})
      q['cases']+=1
      if margin<q['min_margin']:
       q['min_margin']=margin;q['worst']={'S':S,'head':[h,M,m,L,s,U],'B':B,'target':name,'v':v,'R':R,'T':T,'head_lower_unused':head_lower,'local_count':T-len(free),'last_free':free,'sources':clocks,'margin':margin}
      if margin<0:out['violations'].append(q['worst'])
out['seen_local_clocks']=sorted(seen)
print(json.dumps(out,sort_keys=True))
