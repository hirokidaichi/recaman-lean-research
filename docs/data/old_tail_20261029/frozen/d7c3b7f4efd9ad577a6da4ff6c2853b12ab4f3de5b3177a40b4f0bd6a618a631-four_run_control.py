"""One fixed genuine-four-run control. No discovery search or holdout."""
import json
from pathlib import Path
n=1;h=6;M=6;m=2;L=1;s=1;U=6;v=4;T=2;j=0
w=[True]+[False]*h+[True]*M+[False]*m+[True]*L+[False]*s+[True]*U+[False]*v+[True]*(T+1)
B=h+M+m+L+s+U+v+T;target=n+B
# Literal independent suffix mass/moment, not free tags or the earlier forward replay.
def win(t,k):
 z=[1 if x else -1 for x in w[t:k]]
 return sum(z)==1 and sum((len(z)-i)*x for i,x in enumerate(z))==0
es=[x and any(win(t,k) for t in range(k)) for k,x in enumerate(w)]
zero=sum(es[:n])==sum(not x for x in w[:n])
pos=all(sum(es[:q])+1<=sum(not x for x in w[:q]) for q in range(n+1,target+1))
assert zero and pos and es[target] and win(26,29)
assert all(x>=1 for x in [M,m,L,s,U,v,T])
E=sum(es[n:target]);A=sum(w[n:target]);free=A-E
assert E<=19
out={'label':'COMPUTED','role':'fixed nonvacuity, not a new general theorem or standard Recaman orbit','word':''.join('A' if x else 'S' for x in w),'n':n,'B':B,'j':j,'target':target,'target_source':26,'old_zero':zero,'all_positive':pos,'genuine_four_runs':True,'EndN_clocks':[k for k,x in enumerate(es) if x],'actual_supplies':E,'actual_A':A,'actual_free':free,'budget_19':E<=19,'scope':'no counterexample absence claim; j0 does not activate the conditional residual antecedent'}
(Path(__file__).parent/'FOUR_RUN_CONTROL.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
