"""NEW original-stock transport/slack potential, frozen independent controls."""
import json,time
from collections import Counter
t0=time.process_time();C=Counter();examples={}
def direct(x,b,stock,Q):
 X=[x];H=[0];V=[set(stock)]
 for q in range(Q):
  step=b+q+1;candidate=X[-1]-step
  e=-1 if candidate>0 and candidate not in V[-1] else 1
  out=X[-1]+e*step;X.append(out);H.append(H[-1]+e);V.append(V[-1]|{out})
 return X,H,V
cases=[]
for x in range(1,9):
 for b in [0,1,4]:
  for mask in [0,1,2**(x-1)-1,sum(1<<j for j in range(0,x-1,2))]:
   for extras in [[],[x+1,x+4,x+11]]:
    cases.append(('discovery',x,b,{0,x,*extras,*[y for y in range(1,x) if mask>>(y-1)&1]},30))
for x,b in [(12,2),(17,6),(29,11),(43,3)]:
 for stock in [{0,x},{0,x,*range(1,x)},{0,x,*range(2,x,3)},{0,x,x+2,x+17,*range(3,x,4)}]:
  cases.append(('unused_parameters',x,b,stock,42))
for label,x0,b,stock,Q in cases:
 X,H,V=direct(x0,b,stock,Q);C[label+'_states']+=1
 for end in range(1,Q+1):
  for c in range(end):
   if H[end]<=H[c] or min(H[c:end+1])<H[c]:continue
   visits=[q for q in range(c,end+1) if H[q]==H[c]];v=visits[-1];cp=v+1
   x=X[c];y=X[cp];z=X[v];a=b+c;s=(v-c)//2;m=len(visits)-1
   K=sum(0<w<x for w in V[c]);Kn=sum(0<w<y for w in V[cp]);M=x-1-m-K;r=x-z-3*s+2*m
   P=a+2*x;Pn=b+cp+2*y;slack=3*P-1-4*K-Pn
   assert s>=m and M>=0 and r>=0 and slack==4*M+2*r
   expected=max(0,K+m+1-max(0,x-y+1));assert Kn>=expected
   T=13*a+20*x-15*K;Tn=13*(b+cp)+20*y-15*Kn
   assert T>=20 and 5*P<=2*T-30
   assert 20*Tn<=51*T-260
   C['transport_and_potential_checks']+=1;C['clipped_checks']+=y<=x;C['nonempty_returns']+=m>0
   if y<x and 'clipping' not in examples:examples['clipping']={'x0':x0,'b':b,'stock':sorted(stock),'c':c,'end':end,'x':x,'y':y,'K':K,'m':m,'Knext':Kn,'unclipped_bound':K+m+1,'correct_clipped_bound':expected}
   cuts=[c];Ts=[T];bound=31*T-260
   for level in range(H[c]+1,H[end]+1):
    vj=max(q for q in range(cuts[-1],end+1) if H[q]==level-1);cj=vj+1
    kj=sum(0<w<X[cj] for w in V[cj]);tj=13*(b+cj)+20*X[cj]-15*kj
    n=len(cuts);assert 20**n*(31*tj-260)<=33**0*51**n*(31*T-260)
    cuts.append(cj);Ts.append(tj);C['iterated_checks']+=1
# Independent abstract integer/slack controls, including non-actual weakened geometry.
for a in [0,1,7]:
 for z in range(1,6):
  for s in range(0,9):
   for m in range(s+1):
    if (s==0)!=(m==0):continue
    for r in range(0,7):
     if s==0 and r:continue
     x=z+3*s-2*m+r
     for M in range(0,x-m):
      K=x-1-m-M;y=z+a+2*s+1;L=min(x,y-1);Kn=max(0,L-M)
      T=13*a+20*x-15*K;Tn=13*(a+2*s+1)+20*y-15*Kn
      assert 20*Tn<=51*T-260
      C['abstract_piecewise_checks']+=1
      C['abstract_clipped']+=y<=x
print(json.dumps({'all_pass':True,'range_complete':True,'counts':dict(C),'examples':examples,'finite_only':True,'scope':'NEW transport and actual-stock T recurrence, literal full-cut State plus independent abstract slack; no fresh orbit holdout','worker_internal_cpu_seconds':time.process_time()-t0},indent=2))
