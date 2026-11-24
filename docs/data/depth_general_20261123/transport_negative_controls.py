"""Two NEW exact assumption controls, not a range extension or a failed-job repair."""
import json
cases=[('clipped_floor',1000,0,{0,984,999,1000},'AAASSSA'),('repeated_A_output',5,4,{0,2,3,4,5},'AASSA')];out=[]
for name,x,b,initial,w in cases:
 seen=set(initial);X=[x];H=[0];stock=[set(seen)]
 for q,sgn in enumerate(w):
  step=b+q+1;candidate=X[-1]-step;got='S' if candidate>0 and candidate not in seen else 'A';assert got==sgn
  y=X[-1]+(step if got=='A' else -step);seen.add(y);X.append(y);H.append(H[-1]+(1 if got=='A' else -1));stock.append(set(seen))
 v=max(q for q,h in enumerate(H) if h==0);cp=v+1;m=sum(h==0 for h in H[1:v+1]);K=sum(0<y<x for y in initial);Kn=sum(0<y<X[cp] for y in stock[cp]);expected=max(0,K+m+1-max(0,x-X[cp]+1));assert Kn>=expected
 T=13*b+20*x-15*K;Tn=13*(b+cp)+20*X[cp]-15*Kn;assert 20*Tn<=51*T-260
 if name=='clipped_floor':assert X==[1000,1001,1003,1006,1002,997,991,998] and X[cp]<x and Kn<K+m+1
 else:assert X[1]==X[-1] and w[0]==w[-1]=='A'
 out.append({'name':name,'x':x,'base':b,'FULL_initial_stock':sorted(initial),'word':w,'values':X,'last_floor_next_clock':cp,'K':K,'Knext':Kn,'m':m,'unclipped_bound':K+m+1,'clipped_bound':expected,'T_Tnext':[T,Tn]})
print(json.dumps({'all_pass':True,'controls':out,'scope':'exact finite actual negative controls to unclipped stock and fresh-departure A claims; not C1'},indent=2))
