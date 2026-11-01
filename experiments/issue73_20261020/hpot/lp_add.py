# LP: does an additive potential Phi(T)=sum_{p in T} w(p) exist (on all prefixes of length < n)?
import sys, numpy as np, scipy.sparse as sp
from scipy.optimize import linprog
from tstate import step, gain
n=int(sys.argv[1]); nonneg = len(sys.argv)>2 and sys.argv[2]=='nonneg'
var={}
def vid(p):
  if p not in var: var[p]=len(var)
  return var[p]
rows=[];cols=[];vals=[];rhs=[];r=0
T0=frozenset({(0,0)})
seen=set()
stack=[(T0,0)]
labels=[]
while stack:
  T,k=stack.pop()
  # Phi(T)>=0 : -sum w <= 0
  for p in T: rows.append(r);cols.append(vid(p));vals.append(-1.0)
  rhs.append(0.0); labels.append(('nonneg',T)); r+=1
  if k==n: continue
  for s in (1,-1):
    T2=step(T,s); g=gain(T,s)
    # Phi(T2)-Phi(T) <= -g
    coef={}
    for p in T2: coef[vid(p)]=coef.get(vid(p),0)+1
    for p in T: coef[vid(p)]=coef.get(vid(p),0)-1
    for c_,v in coef.items():
      if v: rows.append(r);cols.append(c_);vals.append(float(v))
    rhs.append(float(-g)); labels.append(('step',T,s)); r+=1
    stack.append((T2,k+1))
A=sp.csr_matrix((vals,(rows,cols)),shape=(r,len(var)))
bounds=[(0 if nonneg else None,None)]*len(var)
i0=var[(0,0)]; bounds[i0]=(0,0)
res=linprog(np.zeros(len(var)),A_ub=A,b_ub=np.array(rhs),bounds=bounds,method='highs')
print('n',n,'vars',len(var),'cons',r,'status',res.status,res.message)
if res.status==0:
  w=res.x; 
  items=sorted(var.items(), key=lambda kv:(kv[0][1],kv[0][0]))
  print([ (p,round(w[i],3)) for p,i in items if abs(w[i])>1e-9][:80])
