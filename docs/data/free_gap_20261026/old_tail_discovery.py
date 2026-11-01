from pathlib import Path
import itertools,json
B=Path(__file__).parent;atoms=['A','SAAA','SSAAAASAAA']

def pf(w):
 m=a=0
 for c in w:m+=1 if c=='A' else -1;a+=m
 return m,2*a-m*(m+1)
prefixes=[''.join(x)+'A'*a for n in range(4) for x in itertools.product(atoms,repeat=n) for a in range(2)]
tails=[''.join(x) for n in range(3,9) for x in itertools.product('SA',repeat=n) if x.count('S')>=3]
cases=events=0;viol=[]
for w in prefixes:
 roots=[pf(w[t:]) for t in range(len(w))]
 for v in tails:
  mv,pv=pf(v);S=v.count('S');clocks={};cases+=1
  for t,(mu,pu) in enumerate(roots):
   i=1-mu-mv
   if i>=0 and pu+pv+4*mu*S==-2:clocks.setdefault(i,[]).append(t)
  events+=len(clocks)
  if len(clocks)>1:viol.append({'prefix':w,'tail':v,'clocks':clocks})
out={'cases':cases,'old_events':events,'violations':viol[:10],'discovery':'grammar<=3 atoms/pad0..1 x all tails length3..8 with S>=3; all old clocks at once'}
(B/'old-tail-discovery.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
