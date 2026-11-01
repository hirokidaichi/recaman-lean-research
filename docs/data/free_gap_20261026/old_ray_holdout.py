from pathlib import Path
import json
B=Path(__file__).parent;atoms=['A','SAAA','SSAAAASAAA'];cases=events=0;violations=[];prefix_viol=[]

def direct_profile(w):
 # Reverse weighted moment, independent of the forward-key implementation.
 mass=area=0
 for k,c in enumerate(reversed(w),1):
  s=1 if c=='A' else -1;mass+=s;area+=k*s
 return mass,area
for seed in range(96):
 x=seed+19;parts=[]
 for i in range(5+seed%11):
  x=(1103515245*x+12345)%(1<<31);parts.append(atoms[x%3])
 w=''.join(parts)+'A'*(seed%5)
 for k in range(len(w)+1):
  m,a=direct_profile(w[:k]);p=2*a-m*(m+1)
  if p < -8 or (m<0 and p>0):prefix_viol.append([seed,k,m,p])
 for h in [17,23,31,97]:
  clocks={};cases+=1
  for t in range(len(w)):
   mass,area=direct_profile(w[t:]+'S'*h)
   # A-only leaves P invariant and raises mass by one each time.
   i=1-mass
   if i>=0 and 2*area-mass*(mass+1)==-2:clocks.setdefault(i,[]).append(t)
  events+=len(clocks)
  if len(clocks)>1:violations.append({'seed':seed,'prefix':w,'h':h,'clocks':clocks})
out={'cases':cases,'old_events':events,'clock_violations':violations[:10],'prefix_bound_violations':prefix_viol[:10],'holdout':'96 deterministic5..15 atom words/pad0..4, h17/23/31/97; reversed mass/moment source'}
(B/'old-ray-holdout.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
