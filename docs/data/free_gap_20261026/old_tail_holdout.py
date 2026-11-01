from pathlib import Path
import json
B=Path(__file__).parent;atoms=['A','SAAA','SSAAAASAAA'];cases=events=0;viol=[]
def direct(w):
 m=a=0
 for k,c in enumerate(reversed(w),1):s=1 if c=='A' else -1;m+=s;a+=k*s
 return m,a
for seed in range(96):
 x=seed+73;w=''
 for k in range(5+seed%9):
  x=(1664525*x+1013904223)%(1<<32);w+=atoms[x%3]
 w+='A'*(seed%5)
 for N in [11,13,17]:
  x=(53*seed+331)%(1<<N);v=''.join('A' if x>>i&1 else 'S' for i in range(N))
  if v.count('S')<3:continue
  clocks={};cases+=1
  for t in range(len(w)):
   mass,area=direct(w[t:]+v);i=1-mass
   if i>=0 and 2*area-mass*(mass+1)==-2:clocks.setdefault(i,[]).append(t)
  events+=len(clocks)
  if len(clocks)>1:viol.append({'prefix':w,'tail':v,'clocks':clocks})
out={'cases':cases,'old_events':events,'violations':viol[:10],'holdout':'96 deterministic5..13 atom words/pad0..4 with fresh11/13/17 tails; independent reversed whole suffix'}
(B/'old-tail-holdout.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
