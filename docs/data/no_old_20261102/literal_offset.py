"""Frozen independent nonemptiness cases; literal all-start P2 evaluation."""
import sys,json
case=sys.argv[1]
if case=='discovery': old='AAAA'; params=(11,6,1,2,1,5);R=5;C=4
elif case=='holdout': old='AAAAA';params=(13,4,1,1,1,10);R=6;C=5
else: raise ValueError(case)
h,M,m,L,s,U=params
z=[False]*h+[True]*M+[False]*m+[True]*L+[False]*s+[True]*U
w=[c=='A' for c in old];n=len(w);H=len(z);v=C+2;T=R+2;j=R-1
full=w+z+[False]*v+[True]*T+[False]*j+[True]
def mass(a):return sum(1 if b else -1 for b in a)
def area(a):return sum((len(a)-i)*(1 if b else -1) for i,b in enumerate(a))
def wins(b):return [r for r in range(b) if mass(full[r:b])==1 and area(full[r:b])==0]
sup=[bool(full[b] and wins(b)) for b in range(len(full))]
end=n+H+v+T
positive=[sum(not a for a in full[:b])-sum(sup[:b]) for b in range(n+1,end+j+1)]
target=[r for r in wins(end+j) if r<n and mass(w[r:])==C]
old_last={i:[r for r in wins(n+H+v+i) if r<n] for i in range(T)}
free=lambda a,b:sum(full[k] and not sup[k] for k in range(a,b))
out={'case':case,'old':old,'head':params,'R':R,'head_mass':mass(z),'S':sum(not b for b in z),'B':-area(z),'zero':sum(sup[:n])==sum(not b for b in w),'min_positive':min(positive),'target_sources':target,'old_last':old_last,'head_free':free(n,n+H),'full_free':free(n,end),'last_supply_clocks':[i for i in range(T) if sup[n+H+v+i]],'initial_S_last_sources':{i:[r for r in wins(n+H+v+i) if n<=r<n+h] for i in range(T)}}
assert out['head_mass']==0 and out['zero'] and out['min_positive']>=1 and target
assert not any(old_last.values())
assert out['full_free']>=R
print(json.dumps(out,sort_keys=True))
