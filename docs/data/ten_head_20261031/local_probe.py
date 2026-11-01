import sys,json
split=sys.argv[1]
def profile(w):
 s=a=0
 for b in w:
  s+=1 if b else -1
  a+=s
 return s,a

def supply(w):
 if split=='discovery':
  return [t for t in range(len(w)) if profile(w[t:])==(1,0)]
 # Independent newest-first mass/moment replay on held-out head compositions.
 result=[]
 for t in range(len(w)):
  newest=w[t:][::-1]
  mass=sum(1 if b else -1 for b in newest)
  moment=sum((k+1)*(1 if b else -1) for k,b in enumerate(newest))
  if (mass,moment)==(1,0): result.append(t)
 return result
out={'split':split,'heads_total':0,'cases':{},'violations':[]}
for h in range(1,9):
 for m in range(1,10-h):
  s=10-h-m
  if s<1: continue
  for M in range(1,9):
   for L in range(1,10-M):
    U=10-M-L
    if U<1 or ((M<=L)!=(split=='discovery')):continue
    out['heads_total']+=1
    z=[False]*h+[True]*M+[False]*m+[True]*L+[False]*s+[True]*U
    mass,area=profile(z)
    assert mass==0 and len(z)==20
    for v,T,j,B,need in [(1,5,4,46,1),(2,7,5,56,2)]:
     if area!=-B:continue
     assert profile([True]+z+[False]*v+[True]*T+[False]*j)==(1,0)
     clocks={i:supply(z+[False]*v+[True]*i) for i in range(T)}
     free=[i for i,ts in clocks.items() if not ts]
     d=out['cases'].setdefault(str(B),{'heads':0,'min_free':100,'max_local':0,'min_example':None,'free_histogram':{}})
     d['heads']+=1;d['max_local']=max(d['max_local'],T-len(free))
     d['free_histogram'][str(len(free))]=d['free_histogram'].get(str(len(free)),0)+1
     if len(free)<d['min_free']:
      d['min_free']=len(free);d['min_example']={'h':h,'M':M,'m':m,'L':L,'s':s,'U':U,'v':v,'T':T,'free':free,'sources':clocks}
     if len(free)<need: out['violations'].append(d['min_example'])
print(json.dumps(out,sort_keys=True))
