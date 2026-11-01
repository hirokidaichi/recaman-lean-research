"""Is there an ADDITIVE monovariant Phi(s)=sum_{w in s} f(w) (f arbitrary on window types (age,d,psi,owned))
with Phi(good)=0, Phi nondecreasing on every reachable non-END transition, Phi(exit)>=1, f(closable)<=0 ?"""
import sys
from collections import defaultdict, deque, Counter
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix
import core
L=int(sys.argv[1]); K=int(sys.argv[2]); core.setb(L,K)
mode=sys.argv[3] if len(sys.argv)>3 else 'add'
g={}; dq=deque([()]); seen={()}
while dq:
    s=dq.popleft()
    if s=='END': continue
    g[s]=core.step(s)
    for t,i in g[s]:
        if t not in seen: seen.add(t); dq.append(t)
rev=defaultdict(list)
for a,l in g.items():
    for b,i in l: rev[b].append(a)
good={'END'}; dq=deque(['END'])
while dq:
    b=dq.popleft()
    for a in rev[b]:
        if a not in good: good.add(a); dq.append(a)
def feats(s):
    c=Counter()
    for w in s: c[('w',w[:4])]+=1
    if mode=='addE': c[('E',core.E(s))]+=1
    if mode=='addpair':
        ws=sorted(w[:4] for w in s)
        for i in range(len(ws)):
            for j in range(i+1,len(ws)): c[('p',ws[i],ws[j])]+=1
    return c
idx={}
def vec(s):
    v={}
    for k,c in feats(s).items():
        if k not in idx: idx[k]=len(idx)
        v[idx[k]]=v.get(idx[k],0)+c
    return v
rows=[]; rhs=[]; eqrows=[]
for a,l in g.items():
    va=vec(a)
    for b,i in l:
        if b=='END': continue
        vb=vec(b)
        r=dict(va)
        for k,c in vb.items(): r[k]=r.get(k,0)-c   # Phi(a)-Phi(b) <= 0
        rows.append(r); rhs.append(0)
        if a in good and b not in good:
            r2={k:-c for k,c in vb.items()}; rows.append(r2); rhs.append(-1)
for s in good:
    if s!='END': eqrows.append(vec(s))
for k,i in list(idx.items()):
    if k[0]=='w' and core.closable(k[1]+(0,)):
        rows.append({i:1}); rhs.append(0)
n=len(idx)
A=lil_matrix((len(rows),n))
for r,row in enumerate(rows):
    for k,c in row.items(): A[r,k]=c
Aeq=lil_matrix((max(1,len(eqrows)),n))
for r,row in enumerate(eqrows):
    for k,c in row.items(): Aeq[r,k]=c
res=linprog(np.zeros(n),A_ub=A.tocsr(),b_ub=np.array(rhs,float),A_eq=Aeq.tocsr(),b_eq=np.zeros(Aeq.shape[0]),bounds=[(-1e4,1e4)]*n,method='highs')
print('L',L,'K',K,'mode',mode,'vars',n,'constraints',len(rows),'status',res.status,res.message)
