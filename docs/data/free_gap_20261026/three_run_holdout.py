from pathlib import Path
import itertools,json
BASE=Path(__file__).parent
PREFIXES=['AAASAAA','SAAASAAA','SSAAAASAAA'];DOMAIN=[5,7]
def supplied(w,b):
 if w[b]!='A':return False
 for t in range(b):
  mass=area=0
  for c in w[t:b]:mass+=1 if c=='A' else -1;area+=mass
  if mass==1 and area==0:return True
 return False
def examine(beta,args):
 tail=''.join(('S' if i%2==0 else 'A')*v for i,v in enumerate(args));w=beta+tail;n=len(beta)
 E=S=r=0;positive=True;zero=False
 for b,c in enumerate(w):
  if b==n:zero=E==S
  end=supplied(w,b);E+=end;S+=c=='S';r+=b>=n and c=='A' and not end
  if b>=n and S-E<1:positive=False
 if not zero or not positive:return None,[]
 A=tail.count('A');records=[]
 for j in range(A//2):
  full=w+'S'*j+'A'
  if supplied(full,len(full)-1):records.append({'prefix':beta,'parameters':args,'A':A,'free':r,'gap':j,'badgap':j+1>r,'badcount':A>2*r+1})
 return r,records
counts={'tuples':0,'positive':0,'target_supplies':0,'free_gap_violations':0,'conditional_count_violations':0};bad=[]
for beta in PREFIXES:
 for args in itertools.product(DOMAIN,repeat=6):
  counts['tuples']+=1;r,records=examine(beta,args)
  if r is None:continue
  counts['positive']+=1
  for row in records:
   counts['target_supplies']+=1;counts['free_gap_violations']+=row['badgap'];counts['conditional_count_violations']+=row['badcount']
   if row['badgap'] or row['badcount']:bad.append(row)
# Known terminal is a diagnostic, not a new/fresh holdout case.
beta='ASAAA';args=(5,3,4,4,1,3);r,records=examine(beta,args)
assert r==4 and sum(args[1::2])==10 and not records
out={'protocol':'THREE_RUN_PROTOCOL.json','prefixes':PREFIXES,'domain':DOMAIN,'counts':counts,'counterexamples':bad[:5],'known_terminal_control':{'prefix':beta,'parameters':args,'A':10,'free':r,'target_supplies':len(records)},'evidence':'independent finite holdout with direct interval mass/area, not a proof'}
(BASE/'three-run-holdout.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
