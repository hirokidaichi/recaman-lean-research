from pathlib import Path
import itertools,json
BASE=Path(__file__).parent
PREFIXES=['','AAA','SAAA','ASAAA'];DOMAIN=[1,2,3,4]
def ledger(w,n):
 F=P=E=S=R=0;heights=[0];areas=[0];events=[];seen={0:{0:0}};positive=True;zero=False
 for b,ch in enumerate(w):
  t=seen.get(F-1,{}).get(P-b*(F-1)) if ch=='A' else None
  end=t is not None
  if b==n:zero=S==E
  if ch=='S':S+=1;F-=1
  else:F+=1;E+=end;R+=b>=n and not end
  P+=F;heights.append(F);areas.append(P)
  seen.setdefault(F,{}).setdefault(P-(b+1)*F,b+1)
  events.append({'i':b,'c':ch,'end':end,'t':t,'d':S-E,'free':R})
  if b>=n and S-E<1:positive=False
 return zero,positive,R,heights,areas,events
counts={'tuples':0,'positive':0,'target_supplies':0,'free_gap_violations':0,'conditional_count_violations':0}
badgap=[];badcount=[];maxsurplus=-999;extreme=None
for beta in PREFIXES:
 for args in itertools.product(DOMAIN,repeat=6):
  counts['tuples']+=1
  tail=''.join(('S' if i%2==0 else 'A')*v for i,v in enumerate(args));w=beta+tail;n=len(beta);B=len(w)
  zero,pos,r,F,P,ev=ledger(w,n)
  if not zero or not pos:continue
  counts['positive']+=1;A=sum(args[i] for i in [1,3,5]);roots={}
  for t in range(B):
   mass=F[B]-F[t];area=P[B]-P[t]-(B-t)*F[t]
   if mass>0 and 2*area+mass*(mass-1)==0:roots.setdefault(mass-1,t)
  for j,t in roots.items():
   z,p,rr,_,_,ee=ledger(w+'S'*j+'A',n)
   assert z and ee[-1]['end'] and all(v['d']>=1 for v in ee[n:-1])
   counts['target_supplies']+=1
   row={'prefix':beta,'parameters':args,'tail':tail,'gap':j,'A':A,'free':r,'start':t,'ledger':ee}
   if j+1>r:counts['free_gap_violations']+=1;badgap.append(row)
   if A>2*r+1:counts['conditional_count_violations']+=1;badcount.append(row)
   if A-2*r>maxsurplus:maxsurplus=A-2*r;extreme=row
out={'protocol':'THREE_RUN_PROTOCOL.json','prefixes':PREFIXES,'domain':DOMAIN,'counts':counts,'free_gap_counterexamples':badgap[:3],'conditional_count_counterexamples':badcount[:3],'max_A_minus_2free_when_target':maxsurplus,'extreme':extreme,'evidence':'finite exact; discovery only'}
(BASE/'three-run-discovery.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
