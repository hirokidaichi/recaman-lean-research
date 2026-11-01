from pathlib import Path
import itertools,json
BASE=Path(__file__).parent
atoms=['A','SAAA','SSAAAASAAA'];prefixes=sorted({''}|{a for a in atoms}|{a+b for a in atoms for b in atoms},key=lambda w:(len(w),w))
domain=[1,2,3,4,6]
def ledger(w,n):
 F=P=E=S=R=0;H=[0];V=[0];seen={0:{0:0}};ev=[];zero=False;pos=True
 for b,c in enumerate(w):
  t=seen.get(F-1,{}).get(P-b*(F-1)) if c=='A' else None;end=t is not None
  if b==n:zero=E==S
  if c=='S':S+=1;F-=1
  else:E+=end;R+=b>=n and not end;F+=1
  P+=F;H.append(F);V.append(P);seen.setdefault(F,{}).setdefault(P-(b+1)*F,b+1)
  ev.append({'clock':b,'sign':c,'supplied':end,'start':t,'S':S,'E':E,'d':S-E,'free':R})
  if b>=n and S-E<1:pos=False
 return zero,pos,R,H,V,ev
counts={'tuples':0,'positive':0,'charge_eq2':0,'charge_gt2':0,'eq2_with_target':0,'parent_gap_counterexamples':0};hist={};bad=[];extreme=None;mx=-100;stopped=False
for beta in prefixes:
 if stopped:break
 for args in itertools.product(domain,repeat=6):
  counts['tuples']+=1;tail=''.join(('S' if i%2==0 else 'A')*v for i,v in enumerate(args));w=beta+tail;n=len(beta);B=len(w)
  z,p,r,H,V,ev=ledger(w,n)
  if not z or not p:continue
  counts['positive']+=1;A=sum(args[1::2]);C=A-2*r;hist[C]=hist.get(C,0)+1
  roots={}
  for t in range(B):
   mass=H[B]-H[t];area=V[B]-V[t]-(B-t)*H[t]
   if mass>0 and 2*area+mass*(mass-1)==0:roots.setdefault(mass-1,t)
  row={'prefix':beta,'parameters':args,'tail':tail,'A':A,'free':r,'charge':C,'next_supplied_gaps':roots}
  if C>mx:mx=C;extreme=row
  if C==2:counts['charge_eq2']+=1
  if C>2:counts['charge_gt2']+=1
  if C==2 and roots:counts['eq2_with_target']+=1
  gaps=[j for j in roots if j+1>r]
  counts['parent_gap_counterexamples']+=len(gaps)
  if C>2 or (C==2 and roots) or gaps:
   # Retain a full actual ledger and replay any target with the same original base.
   row['ledger']=ev
   for j in roots:
    zz,pp,rr,_,_,ee=ledger(w+'S'*j+'A',n);assert zz and ee[-1]['supplied'];assert all(e['d']>=1 for e in ee[n:-1])
   row['gap_violations']=gaps;bad.append(row);stopped=True;break
out={'protocol':'CHARGE_PROTOCOL.json','prefixes':prefixes,'domain':domain,'counts':counts,'charge_histogram':hist,'max_charge':mx,'extreme':extreme,'counterexamples':bad,'complete_declared_domain':not stopped,'stop_at_first_counterexample':stopped,'evidence':'exact finite discovery of actual original-base histories; no general proof'}
(BASE/'charge-discovery.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
