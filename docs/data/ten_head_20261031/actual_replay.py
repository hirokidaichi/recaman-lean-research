import json

def profile(w):
 mass=area=0
 for a in w:
  mass+=1 if a else -1;area+=mass
 return mass,area

def end_sources(w,b):
 return [t for t in range(b) if profile(w[t:b])==(1,0)] if w[b] else []
out={'scope':'finite actual Bool histories, not canonical Recaman orbit; old contexts independent replay, not fresh head holdout','contexts':{},'violations':[]}
for old in ([True],[True,True],[False,True,True,True]):
 key=''.join('A' if x else 'S' for x in old);d={'tested':0,'positive':0,'examples':{}}
 for h in range(1,9):
  for m in range(1,10-h):
   s=10-h-m
   if s<1:continue
   for M in range(1,9):
    for L in range(1,10-M):
     U=10-M-L
     if U<1:continue
     z=[False]*h+[True]*M+[False]*m+[True]*L+[False]*s+[True]*U
     _,area=profile(z)
     if area not in (-46,-56):continue
     v,T,j=(1,5,4) if area==-46 else (2,7,5)
     w=old+z+[False]*v+[True]*T+[False]*j+[True];n=len(old);target=len(w)-1
     src=[end_sources(w,b) for b in range(len(w))]
     E=[bool(x) for x in src]
     assert sum(E[:n])==old.count(False)
     d['tested']+=1
     positive=all(sum(E[:k])+1<=w[:k].count(False) for k in range(n+1,target+1))
     if not positive:continue
     d['positive']+=1
     F=sum(w[k] and not E[k] for k in range(n,n+20+v+T))
     Fh=sum(w[k] and not E[k] for k in range(n,n+20))
     Fl=sum(w[k] and not E[k] for k in range(n+20+v,n+20+v+T))
     assert n-1 in src[target]
     assert n+20+v-1 in src[n+20+v+2]
     assert all(not any(t<n for t in src[b]) for b in range(n+20+v,n+20+v+T))
     if F<j+1:out['violations'].append([key,h,M,m,L,s,U,v,T,j,F])
     d['examples'].setdefault(str(-area),{'head':[h,M,m,L,s,U],'v':v,'T':T,'j':j,'target_sources':src[target],'free_head':Fh,'free_last':Fl,'free_full':F,'zero_at_n':True,'full_positive':True})
 out['contexts'][key]=d
print(json.dumps(out,sort_keys=True))
