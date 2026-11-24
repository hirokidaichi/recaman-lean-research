"""NEW independent algebra and explicitly clipped controls for the new strip consumer."""
import json,time
from collections import Counter
C=Counter();t0=time.process_time()
for a in [0,1,4,17]:
 for z in range(1,7):
  for s in range(0,11):
   for m in range(s+1):
    if (s==0)!=(m==0):continue
    for r in range(0,8):
     if s==0 and r:continue
     x=z+3*s-2*m+r;R=2*m-s-r;y=z+a+2*s+1
     for M in range(x-m):
      K=x-1-m-M;Kn=max(0,min(x,y-1)-M)+max(0,R)
      T=13*a+20*x-15*K;Tn=13*(a+2*s+1)+20*y-15*Kn;W=12*a+15*x-10*K;Wn=12*(a+2*s+1)+15*y-10*Kn
      assert 13*Tn<=33*T-166 and 15*Wn<=34*W-30
      C['independent_abstract_checks']+=1;C['clipped_abstract']+=y<=x;C['positive_strip_abstract']+=R>0
# Literal direct replay of the previously found exact controls; these are NOT fresh orbit data.
controls=[(1000,0,{0,984,999,1000},'AAASSSA'),(5,4,{0,2,3,4,5},'AASSA')]
for k in [15,35]:
 l=3*k;b=5*k*k-k-2;x=10*l*l;I=x+2*b-1;y=x-(4*k*k-5*k+1)
 cand=lambda j:x+(j-2)*b+j*(j-3)//2
 V={0,I,*[cand(j) for j in range(1,l+1) if j!=3],x-l*l-b-2*l-1,x-l*l-1,*range(y,x)}
 controls.append((I,b-2,V,'SS'+'A'*l+'S'*l+'AA'))
for initial,b,stock,w in controls:
 X=[initial];H=[0];V=[set(stock)]
 for q,e in enumerate(w):
  n=b+q+1;c=X[-1]-n;actual='S' if c>0 and c not in V[-1] else 'A';assert actual==e
  v=X[-1]+(n if e=='A' else -n);X.append(v);H.append(H[-1]+(1 if e=='A' else -1));V.append(V[-1]|{v})
 for c in range(len(w)):
  if min(H[c:])<H[c] or H[-1]<=H[c]:continue
  visits=[q for q in range(c,len(w)+1) if H[q]==H[c]];cp=visits[-1]+1;x=X[c];y=X[cp];K=sum(0<v<x for v in V[c]);Kn=sum(0<v<y for v in V[cp]);a=b+c
  Z=[X[q+1] for q in visits];assert all(j in V[cp] for j in range(Z[0],y))
  T=13*a+20*x-15*K;Tn=13*(b+cp)+20*y-15*Kn;W=12*a+15*x-10*K;Wn=12*(b+cp)+15*y-10*Kn
  assert 13*Tn<=33*T-166 and 15*Wn<=34*W-30;C['explicit_original_control_cuts']+=1;C['explicit_actual_clipped']+=y<x;C['explicit_repeated_departures']+=len(set(Z))<len(Z)
print(json.dumps({'all_pass':True,'range_complete':True,'counts':dict(C),'scope':'NEW independent strip-algebra and new predicate on OLD exact clipped/full-source controls, not fresh holdout','worker_internal_cpu_seconds':time.process_time()-t0},indent=2))
