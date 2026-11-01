"""Two frozen, independent literal cases; exact original-base window evaluation."""
import sys, json

def word(s): return [c == 'A' for c in s]
def seg(h,M,m,L,s,U): return [False]*h+[True]*M+[False]*m+[True]*L+[False]*s+[True]*U
def mass(w): return sum(1 if x else -1 for x in w)
def area(w): return sum((len(w)-k)*(1 if x else -1) for k,x in enumerate(w))
def wins(w,b):
    return [t for t in range(b) if mass(w[t:b])==1 and area(w[t:b])==0]

case=sys.argv[1]
if case=='discovery': old='AASAAA'; params=(10,5,1,4,1,3)
elif case=='holdout': old='SAAAASAAA'; params=(13,10,1,3,1,2)
else: raise ValueError(case)
z=seg(*params); w=word(old); n=len(w); H=len(z); S=sum(not x for x in z)
R=6 if case=='discovery' else 9; v=4; T=R+1; j=R-1; old_i=1 if case=='discovery' else 0
full=w+z+[False]*v+[True]*T+[False]*j+[True]
end=n+H+v+T
sup=[bool(full[b] and wins(full,b)) for b in range(len(full))]
pos=[sum(not x for x in full[n:n+k])-sum(sup[n:n+k]) for k in range(1,H+v+T+1)]
target=[t for t in wins(full,end+j) if t<n and mass(w[t:])==3]
old0=[t for t in wins(full,n+H+v+old_i) if t<n and mass(w[t:])==5-old_i]
local=[q for q in range(1,5) if n+H+v-q in wins(full,n+H+v+2)]
free=sum(full[b] and not sup[b] for b in range(n,end))
out=dict(case=case,old=old,head=params,S=S,B=-area(z),zero=sum(sup[:n])==sum(not x for x in w),
         min_positive=min(pos),target_sources=target,old0_sources=old0,local_q_clock2=local,
         head_free=sum(full[b] and not sup[b] for b in range(n,n+H)),full_free=free,
         last_supply_clocks=[i for i in range(T) if sup[n+H+v+i]],
         first_A_local_sources_clock3=[t-n for t in wins(full,n+H+v+3) if n+params[0]<=t<n+params[0]+params[1]])
assert mass(z)==0
assert out['zero'] and out['min_positive']>=1 and target and old0 and local
assert free>=R
print(json.dumps(out,sort_keys=True))
