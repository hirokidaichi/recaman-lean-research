#!/usr/bin/env python3
"""Frozen SS-source late-born-blocker refinement C; no new holdout."""
import hashlib,json,pathlib,collections
REV='612fcfaf74bfb49f3ae05a268057c82f70dcca26'
print('source_revision='+REV)
print('script_sha256='+hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest())
print('command=python3 experiments/parallel20260907/entry_source_birth.py')
print('protocol=H-20260907-05 second pass C; canonical [0,1000000]; already-used regression, not holdout')
a=[0];sign=['-'];birth={0:0};bad=[];count=0;total=0;addsources=[]
for T in range(1,1000001):
 c=a[-1]-T;s=c>0 and c not in birth;m=c if s else a[-1]+T
 a.append(m);sign.append('S' if s else 'A')
 if m not in birth:
  if 1<=m<T:
   p=T-1;k=0
   while p>=2 and sign[p-1]=='A' and sign[p]=='S':p-=2;k+=1
   if k>0 and sign[p]=='A':addsources.append(dict(T=T,m=m,p=p,k=k,value=a[p],previous_two=a[p-2:p],bound=m+5*k+3))
   if k>0 and sign[p]=='S':
    count+=1
    assert p>=2 and sign[p-1]=='S'
    bs=[m+3*j for j in range(1,k+1)]
    total+=len(bs)
    failures=[(b,birth[b]) for b in bs if birth[b]>b]
    if failures:
     bad.append(dict(T=T,m=m,p=p,k=k,root_values=a[p-2:p+1],word='SS'+'AS'*k+'S' if k<30 else 'SS(AS)^'+str(k)+'S',failed_blockers=failures[:6],failed_count=len(failures)))
  birth[m]=T
print('SS_chains='+str(count)+' blocked_candidates='+str(total))
print('claim_C_bad_chains='+str(len(bad)))
for e in bad[:5]:print('counterexample='+json.dumps(e,sort_keys=True))
print('addition_sources='+json.dumps(addsources,sort_keys=True))
print('first_counterexample_birth_trace='+json.dumps(a[bad[0]['failed_blockers'][0][1]-3:bad[0]['failed_blockers'][0][1]+4]) if bad else 'no counterexample')
print('PASS: exact classification complete')
