"""NEW A-departure interval producer and two all-depth potential consumers."""
import json,time
from collections import Counter
from fractions import Fraction
t0=time.process_time();C=Counter();records=[]
def actual(x,b,stock,Q):
 X=[x];H=[0];V=[set(stock)]
 for q in range(Q):
  n=b+q+1;c=X[-1]-n;e=-1 if c>0 and c not in V[-1] else 1;y=X[-1]+e*n
  X.append(y);H.append(H[-1]+e);V.append(V[-1]|{y})
 return X,H,V
cases=[]
for x in range(1,9):
 for b in [0,1,5,17]:
  for mask in [0,1,2**(x-1)-1,sum(1<<j for j in range(0,x-1,2))]:
   for extra in [[],[x+2,x+11]]:cases.append(('discovery',x,b,{0,x,*extra,*[y for y in range(1,x) if mask>>(y-1)&1]},[12,20,28]))
for x in [13,21]:
 for b in [3,9]:
  for stock in [{0,x},{0,x,*range(1,x)},{0,x,*range(2,x,3)},{0,x,x+2,x+11,*range(3,x,4)}]:cases.append(('unused_parameters',x,b,stock,[16,24,36]))
for label,x0,b,stock,ends in cases:
 X,H,V=actual(x0,b,stock,max(ends));C[label+'_states']+=1
 for Q in ends:
  for c in range(Q):
   if H[Q]<=H[c] or min(H[c:Q+1])<H[c]:continue
   visits=[q for q in range(c,Q+1) if H[q]==H[c]];v=visits[-1];cp=v+1;s=(v-c)//2;m=len(visits)-1;x=X[c];y=X[cp];z=X[v];a=b+c
   K=sum(0<t<x for t in V[c]);Kn=sum(0<t<y for t in V[cp]);M=x-1-m-K;r=x-z-3*s+2*m;R=2*m-s-r
   Z=[X[q+1] for q in visits];assert Z[0]==x+a+1 and Z[-1]==y and all(t-u<=1 for u,t in zip(Z,Z[1:]))
   assert R==y-Z[0] and all(t in V[cp] for t in range(Z[0],y))
   assert Kn>=max(0,min(x,y-1)-M)+max(0,R)
   T=13*a+20*x-15*K;Tn=13*(b+cp)+20*y-15*Kn;W=12*a+15*x-10*K;Wn=12*(b+cp)+15*y-10*Kn
   assert 13*Tn<=33*T-166 and 15*Wn<=34*W-30 and W>=15 and 5*(a+2*x)<=2*W-20
   C['original_cut_strip_checks']+=1;C['positive_strip']+=R>0;C['repeated_departures']+=len(set(Z))<len(Z);C['clipped']+=y<=x
 for j in range(1,5):
  G=Fraction(12*(b+2*x0))
  for _ in range(j-1):G=(34*G-30)/15
  U=(2*G/5-b-5).__floor__();d=0
  while b*(d+1)+(d+1)*(d+2)//2<x0:d+=1
  if U<=max(ends):assert min(H[U:])>=-d+j;C['new_uniform_horizon_targets']+=1
for a in [0,1,7,31,101]:
 X,H,V=actual(1,a,{0,1},1);T=13*a+20;Tn=13*(a+1)+20*X[1]-15*sum(0<t<X[1] for t in V[1]);assert 13*Tn==33*T-166;records.append({'a':a,'T':T,'Tnext':Tn})
for b in [7,19,61]:
 h=2;I=2*b;X,H,V=actual(I,b-h,{0,I},2*b+2);c=2;cp=3;T=13*b+20;Knext=sum(0<t<X[cp] for t in V[cp]);Tn=13*(b+1)+20*X[cp]-15*Knext
 assert X[c]==1 and Knext==2 and Tn==33*b+23;C['full_original_S_lift_sharp_slope']+=1
print(json.dumps({'all_pass':True,'range_complete':True,'counts':dict(C),'exact_T33_equalities':records,'finite_only':True,'scope':'NEW literal A interval producer and T33/W34 consumer; finite parameters not proof or fresh orbit holdout','worker_internal_cpu_seconds':time.process_time()-t0},indent=2))
