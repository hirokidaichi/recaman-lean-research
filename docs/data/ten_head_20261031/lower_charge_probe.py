import json,sys
split=sys.argv[1];S=int(sys.argv[2])
R=int(sys.argv[3]);B=int(sys.argv[4]);v=1;j=R-1;T=R
old=[True]*int(sys.argv[5]);n=len(old)
def profile(w):
 if split=='discovery':
  a=s=0
  for x in w:s+=1 if x else -1;a+=s
  return s,a
 rev=w[::-1]
 return sum(1 if x else -1 for x in rev),sum((i+1)*(1 if x else -1) for i,x in enumerate(rev))
def sources(w,b):return [t for t in range(b) if profile(w[t:b])==(1,0)] if w[b] else []
out={'split':split,'S':S,'B':B,'R':R,'scope':'literal actual Bool histories, full free charge; not canonical orbit proof','matching_heads':0,'positive_heads':0,'old_clock0_heads':0,'min_free':999,'counterexamples':[],'examples':[]}
for h in range(1,S-1):
 for m in range(1,S-h):
  s=S-h-m
  for M in range(1,S-1):
   for L in range(1,S-M):
    U=S-M-L
    z=[False]*h+[True]*M+[False]*m+[True]*L+[False]*s+[True]*U
    if profile(z)!=(0,-B):continue
    out['matching_heads']+=1
    w=old+z+[False]*v+[True]*T+[False]*j+[True];target=len(w)-1;last=n+2*S+v
    src=[sources(w,b) for b in range(len(w))];E=[bool(x) for x in src]
    assert sum(E[:n])==old.count(False)
    positive=all(sum(E[:k])+1<=w[:k].count(False) for k in range(n+1,target+1))
    if not positive:continue
    out['positive_heads']+=1
    assert n-1 in src[target] and last-1 in src[last+2]
    assert T<=2+j
    if 0 in src[last]:out['old_clock0_heads']+=1
    F=sum(w[b] and not E[b] for b in range(n,last+T))
    out['min_free']=min(out['min_free'],F)
    if F<R:out['counterexamples'].append({'head':[h,M,m,L,s,U],'free':F,'R':R,'sources':src})
    if len(out['examples'])<2:out['examples'].append({'head':[h,M,m,L,s,U],'v':v,'T':T,'j':j,'actual_zero':True,'actual_fullpositive':True,'free_full':F,'old_supply_source':0,'old_supply_clock':0,'target_source':n-1,'local_final_S_clock':2})
print(json.dumps(out,sort_keys=True))
