import sys, numpy as np, scipy.sparse as sp
from scipy.optimize import linprog
from tstate import step, gain
n=int(sys.argv[1])
var={}
def vid(p):
  if p not in var: var[p]=len(var)
  return var[p]
rows=[];cols=[];vals=[];rhs=[];lab=[];r=0
stack=[(frozenset({(0,0)}),'')]
while stack:
  T,w=stack.pop()
  for p in T: rows.append(r);cols.append(vid(p));vals.append(-1.0)
  rhs.append(0.0); lab.append('Phi(%s)>=0'%w); r+=1
  if len(w)==n: continue
  for s in (1,-1):
    T2=step(T,s); g=gain(T,s); coef={}
    for p in T2: coef[vid(p)]=coef.get(vid(p),0)+1
    for p in T: coef[vid(p)]=coef.get(vid(p),0)-1
    for c_,v in coef.items():
      if v: rows.append(r);cols.append(c_);vals.append(float(v))
    ch='A' if s>0 else 'S'
    rhs.append(float(-g)); lab.append('Phi(%s)-Phi(%s)<=%d'%(w+ch,w,-g)); r+=1
    stack.append((T2,w+ch))
A=sp.csr_matrix((vals,(rows,cols)),shape=(r,len(var)))
keep=[i for p,i in var.items() if p!=(0,0)]
A2=A[:,keep]
# find y>=0: A2^T y = 0, b^T y = -1, min sum y
Aeq=sp.vstack([A2.T, sp.csr_matrix(np.array(rhs)[None,:])])
beq=np.zeros(Aeq.shape[0]); beq[-1]=-1
res=linprog(np.ones(r),A_eq=Aeq,b_eq=beq,bounds=[(0,None)]*r,method='highs')
print(res.status, res.fun)
y=res.x
for i in np.argsort(-y):
  if y[i]>1e-9: print(round(y[i],4), lab[i])
