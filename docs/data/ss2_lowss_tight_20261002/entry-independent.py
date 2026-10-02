from pathlib import Path
from itertools import combinations
import hashlib,json
root=Path(__file__).resolve().parents[3]
frozen=root/'docs/data/ss2_lowss_tight_20261002'
for line in (frozen/'PRE_RUN_SHA256SUMS').read_text().splitlines():
 h,p=line.split(None,1);assert hashlib.sha256((root/p).read_bytes()).hexdigest()==h
rows=[]
for L in [3,7,11,15,19,23]:
 count=donors=candidates=violations=anySSviolations=S_candidates=S_violations=0;tails={}
 for plus in combinations(range(1,L+1),(L+1)//2):
  if 2*sum(plus)!=L*(L+1)//2:continue
  count+=1; aset=set(plus);z=[1 if i in aset else -1 for i in range(1,L+1)]
  if sum(a==b==-1 for a,b in zip(z,z[1:]))!=2:continue
  H=[0];M=[0]
  for i,v in enumerate(z,1):H.append(H[-1]+v);M.append(M[-1]+i*v)
  if any((H[i],M[i])==(1,0) for i in range(1,L)):continue
  donors+=1;r=max(i for i,v in enumerate(z,1) if v==-1);tails[L-r]=tails.get(L-r,0)+1
  for c in range(1,r):
   mass=H[r]-H[c];moment=M[r]-M[c]-c*mass
   if z[c-1]==1:
    candidates+=1
    if (mass,moment)==(1,0):
     anySSviolations+=1
     v=z[c:r]
     if sum(a==b==-1 for a,b in zip(v,v[1:]))<=1:violations+=1
   else:
    S_candidates+=1
    v=z[c:r]
    if (mass,moment)==(1,0) and sum(a==b==-1 for a,b in zip(v,v[1:]))<=1:S_violations+=1
 row=dict(length=L,p2=count,minimal_ss2=donors,current_A_candidates=candidates,lowSS_violations=violations,anySS_earlier_cover_violations=anySSviolations,current_S_candidates=S_candidates,current_S_lowSS_covers=S_violations,tails=tails)
 assert violations==anySSviolations==0,row
 rows.append(row)
record=dict(status='PASS',scope='same frozen reused lengths; independent integer prefix-sum checker',frozen_hashes_match=True,rows=rows)
print(json.dumps(record,indent=2))
