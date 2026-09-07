#!/usr/bin/env python3
"""Fixed negative control found after the primary protocol; no holdout claim."""
import hashlib,json,pathlib
REV='612fcfaf74bfb49f3ae05a268057c82f70dcca26'
print('source_revision='+REV)
print('script_sha256='+hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest())
print('command=python3 experiments/parallel20260907/entry_canonical_swap.py')
print('protocol=fixed canonical 19 first-hit counterfactual; post-discovery exact verification, not holdout')
a=[0];birth={0:0}
for t in range(1,99733):
 c=a[-1]-t; w=c if c>0 and c not in birth else a[-1]+t
 a.append(w);birth.setdefault(w,t)
H0=set(birth);H1=H0-{99819,99885}|{99753,99951}
B=99752;Q=66;n=99732;v=a[-1]
summary=lambda H: (len(H),max(H),sum(H),tuple(sum(x%Q==r for x in H) for r in range(Q)))
assert H0.intersection(range(B+1))==H1.intersection(range(B+1))
assert summary(H0)==summary(H1)
assert set(a[:37425])<=H0.intersection(H1)
assert 19 not in H0|H1
paths=[]
for H in [H0.copy(),H1.copy()]:
 w=v;path=[v]
 for t in (n+1,n+2):
  c=w-t;w=c if c>0 and c not in H else w+t;H.add(w);path.append(w)
 paths.append(path)
assert paths==[[199486,99753,19],[199486,299219,398953]]
print(json.dumps(dict(clock=n,value=v,low_window=B,modulus=Q,cardinality=len(H0),maximum=max(H0),sum=sum(H0),equal_mod_histogram=True,remove=[99819,99885],remove_first_times=[birth[99819],birth[99885]],add=[99753,99951],common_canonical_prefix_through=37424,paths=paths),sort_keys=True))
print('PASS; H0 is canonical, H1 is a weakened-history counterfactual; no claim of H1 canonical reachability')
