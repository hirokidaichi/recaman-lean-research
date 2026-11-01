from pathlib import Path
import json
B=Path(__file__).parent
rows=[]
for params,expected in [([1,5,6,4,6],[2,4,5]),([10,24,21,3,4],[2,3,9,11])]:
 h,M,m,L,s=params;w='S'*h+'A'*M+'S'*m+'A'*L+'S'*s;found={}
 for i in range(1+max(expected)):
  v=w+'A'*i;witnesses=[]
  for t in range(len(v)):
   mass=area=0
   for c in v[t:]:mass+=1 if c=='A' else -1;area+=mass
   if mass==1 and area==0:witnesses.append({'start':t,'mass':mass,'area':area})
  if witnesses:found[i]=witnesses
 assert sorted(found)==expected,(params,found)
 rows.append({'parameters':params,'word':w,'clocks':found,'actual_C1_assumptions':'not required/not claimed; relaxed local-word model only'})
# Quantifier audit: realize the word as one full original-base history.
v='S'*10+'A'*24+'S'*21+'A'*3+'S'*4
full=v+'A'*12;E=S=R=0;ledger=[]
for b,c in enumerate(full):
 starts=[]
 if c=='A':
  for t in range(b):
   mass=area=0
   for q in full[t:b]:mass+=1 if q=='A' else -1;area+=mass
   if mass==1 and area==0:starts.append(t)
 E+=bool(starts);S+=c=='S';R+=c=='A' and not starts
 ledger.append({'clock':b,'sign':c,'old_base':0,'supplied':bool(starts),'starts':starts,'S':S,'E':E,'free':R,'deficit':S-E})
assert all(x['deficit']>=1 for x in ledger)
assert [i for i in range(12) if ledger[len(v)+i]['supplied']]==[2,3,9,11]
actual={'prefix':'empty BlockWord','zero_at_n0':True,'positive_at_all_nonempty_prefixes':True,'third_A_run_supply_clocks':[2,3,9,11],'ledger':ledger,'scope':'actual original0 EndN sign-history model; no orbit/a_n, d1 endpoint or C1/Q counterexample claimed'}
out={'actual_history_quantifier_audit':actual,'counterexamples':rows,'role':'independent literal replay of discovery counterexamples; not fresh holdout','refutes':['local <=2','repaired local <=3'],'does_not_refute':['parent free-gap','C1','conditional totalA<=2r+1']}
(B/'three-source-replay.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
