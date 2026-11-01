from pathlib import Path
import itertools,json
B=Path(__file__).parent;atoms=['A','SAAA','SSAAAASAAA']

def profile(w):
 m=a=0
 for b in w:m+=1 if b=='A' else -1;a+=m
 return m,2*a-m*(m+1)
words=[''.join(x) for n in range(5) for x in itertools.product(atoms,repeat=n)]
cases=events=duplicates=0;violations=[];prefix_viol=[]
for beta in words:
 for pad in range(3):
  w=beta+'A'*pad
  for k in range(len(w)+1):
   m,key=profile(w[:k])
   if key < -8 or (m<0 and key>0):prefix_viol.append([w,k,m,key])
  profiles=[profile(w[t:]) for t in range(len(w))]
  for h in range(17):
   candidates={};cases+=1
   for t,(m,key) in enumerate(profiles):
    i=h+1-m
    if i>=0 and key+4*h*m-2*h*h==-2:candidates.setdefault(i,[]).append(t)
   events+=len(candidates);duplicates+=sum(len(v)-1 for v in candidates.values())
   if len(candidates)>1:violations.append({'prefix':w,'h':h,'clocks':candidates})
out={'cases':cases,'old_events':events,'duplicate_starts_same_clock':duplicates,'clock_violations':violations[:10],'prefix_bound_violations':prefix_viol[:10],'discovery':'all grammar atom words up to4 atoms/pad0..2, h0..16; target is new count, not old r4 horizon'}
(B/'old-ray-discovery.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
