from pathlib import Path
import itertools,json
B=Path(__file__).parent
maxcount=0;cases=0;bad=[]
# Fresh literal source profiles, no discovery square formulas.
for h,M,m,L,s in itertools.product([1,9,17],[33,37],[2,11],[35,41],[3,13]):
 w='S'*h+'A'*M+'S'*m+'A'*L+'S'*s;clocks=set()
 for t in range(len(w)):
  mass=area=0
  for c in w[t:]:mass+=1 if c=='A' else -1;area+=mass
  if 2*area-mass*(mass+1)==-2 and mass<=1:clocks.add(1-mass)
 cases+=1;maxcount=max(maxcount,len(clocks))
 if len(clocks)>2:bad.append({'parameters':[h,M,m,L,s],'clocks':sorted(clocks)})
out={'cases':cases,'max_clock_count':maxcount,'countermodels':bad,'domain':'h1/9/17,M33/37,m2/11,L35/41,s3/13; parameter tuples disjoint from discovery','evidence':'independent finite literal-window holdout, not proof'}
(B/'three-source-holdout.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
