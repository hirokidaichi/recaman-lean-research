from pathlib import Path
import json
P=Path(__file__).parent;src=json.loads((P/'first-A-count-audit.json').read_text());rows=[]
for z in src['witnesses']:
 M,L,T,R,d,s,m=(z[k] for k in ('M','L','T','R','d','s','m'));a,b,c=z['free_counts']
 word='A'*d+'S'*m+'A'*L+'S'*s+'A'*T+'S'*(R-1)
 # Independent oldest-first walk, no square formula used in this check.
 level=area=0
 for ch in word:level+=1 if ch=='A' else -1;area+=level
 assert (level,area)==(1,0)
 assert 1<=d<=M and M+L+T<=20 and 5<=R<=10 and m>=0 and s>=0
 assert min(M,2)<=a<=M and M<=2*a and M-a<=2
 assert 0<=b<=L and L-b<=3 and 0<=c<=T and T-c<=6
 assert M+L<=2*(a+b)+1 and 4<=a+b+c<R and M+L+T-a-b-c<=11
 # Literal actual EndN audit on empty prefix for h=39 is a diagnostic only;
 # no actual prefix realizing the numerical free counts is assumed.
 actual='S'*39+'A'*M+'S'*m+'A'*L+'S'*s+'A'*T
 E=F=S=H=V=0;heights=[0];areas=[0];free=[];oldn=0
 for i,ch in enumerate(actual):
  supplied=ch=='A' and any(H-heights[t]==1 and V-areas[t]-(i-t)*heights[t]==0 for t in range(i))
  if ch=='A':F+=not supplied
  else:S+=1
  if i>=39:free.append(F)
  H+=1 if ch=='A' else -1;V+=H;heights.append(H);areas.append(V)
 rows.append({'numeric':z,'literal_P2_source':word,'mass':level,'area':area,'empty_prefix_head39_actual_free':F,'numeric_free':a+b+c,'scope':'numeric count witness does not assert these actual free counts'})
out={'rows':rows,'checks_passed':True,'scope':'independent literal P2/count replay of selected witnesses, no holdout or actual C1 counterexample'}
(P/'first-A-count-replay.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
