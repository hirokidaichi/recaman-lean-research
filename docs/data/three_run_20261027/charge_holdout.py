from pathlib import Path
import itertools,json
BASE=Path(__file__).parent
A='A';B='SAAA';C='SSAAAASAAA';prefixes=[A+B+B,B+C+A,C+A+C,A+C+B]
def supply(w,b):
 if w[b]!='A':return False
 mass=area=0
 for k in range(1,b+1):
  d=1 if w[b-k]=='A' else -1;mass+=d;area+=d*k
  if mass==1 and area==0:return True
 return False
def check(beta,args):
 tail=''.join(('S' if i%2==0 else 'A')*v for i,v in enumerate(args));w=beta+tail;n=len(beta);S=E=r=0;pos=True;zero=False;events=[]
 for b,c in enumerate(w):
  if b==n:zero=S==E
  en=supply(w,b);E+=en;S+=c=='S';r+=b>=n and c=='A' and not en
  events.append({'clock':b,'sign':c,'supply':en,'d':S-E,'free':r})
  if b>=n and S-E<1:pos=False
 if not zero or not pos:return None
 total=tail.count('A');charge=total-2*r;gaps=[]
 for j in range(total//2):
  ww=w+'S'*j+'A'
  if supply(ww,len(ww)-1):gaps.append(j)
 return {'prefix':beta,'parameters':args,'A':total,'free':r,'charge':charge,'next_supplied_gaps':gaps,'ledger':events}
counts={'tuples':0,'positive':0,'charge_gt2':0,'eq2_with_target':0,'parent_gap_counterexamples':0};bad=[];mx=-100
for beta in prefixes:
 for args in itertools.product([5,8],repeat=6):
  if 8 not in args:continue
  counts['tuples']+=1;d=check(beta,args)
  if d is None:continue
  counts['positive']+=1;mx=max(mx,d['charge']);counts['charge_gt2']+=d['charge']>2;counts['eq2_with_target']+=d['charge']==2 and bool(d['next_supplied_gaps']);counts['parent_gap_counterexamples']+=sum(j+1>d['free'] for j in d['next_supplied_gaps'])
  if d['charge']>2 or (d['charge']==2 and d['next_supplied_gaps']) or any(j+1>d['free'] for j in d['next_supplied_gaps']):bad.append(d)
# Known equality-terminal control, separated from fresh parameter holdout.
control=check('ASAAA',(5,3,4,4,1,3));assert control['charge']==2 and not control['next_supplied_gaps']
out={'protocol':'CHARGE_PROTOCOL.json','prefixes':prefixes,'domain':[5,8],'at_least_one8':True,'counts':counts,'max_charge':mx,'counterexamples':bad,'known_control':control,'evidence':'independent backward-interval window implementation; disjoint protocol tuples; known prefix words not claimed new'}
(BASE/'charge-holdout.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
