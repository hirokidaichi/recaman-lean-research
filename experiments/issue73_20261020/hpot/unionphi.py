# test Theta = sum_h max(Phi1_h, flag_h) for the union class (shallow or capped windows)
import sys
N=int(sys.argv[1])
def analyze(w):
  F=[0]
  for ch in w: F.append(F[-1]+(1 if ch=='A' else -1))
  k=len(w)
  # shallow-valid points: t with min F[t..k] >= F[t]-1 ; (d,c)
  G=[0]
  for i in range(1,k+1): G.append(G[-1]+F[i])
  pts={}
  for t in range(k+1):
    if min(F[t:k+1])>=F[t]-1:
      d=F[k]-F[t]; a=G[k]-G[t]-(k-t)*F[t]; c=a-d*(d+1)//2
      pts.setdefault(F[t],set()).add((d,c))
  phi1={h:sum(1 for d,c in P if c<0)-sum(1 for d,c in P if c==-1 and d>=2) for h,P in pts.items()}
  flag={}
  for h in set(F):
    # S from h after last time walk >= h+2
    last=max([u for u in range(k+1) if F[u]>=h+2],default=-1)
    flag[h]=1 if any(w[s]=='S' and F[s]==h for s in range(last+1,k)) else 0
  return F,G,phi1,flag
def theta(w):
  F,G,phi1,flag=analyze(w)
  return sum(max(phi1.get(h,0),flag.get(h,0)) for h in set(F))
def gain(w):  # last clock b=len(w)-1 endable in union class?
  b=len(w)-1
  if w[b]!='A': return -1
  F=[0]
  for ch in w: F.append(F[-1]+(1 if ch=='A' else -1))
  G=[0]
  for i in range(1,len(F)): G.append(G[-1]+F[i])
  for t in range(b-3,-1,-4):
    h=F[t]
    if F[b]==h+1 and G[b]-G[t]==(b-t)*h:
      seg=F[t:b+1]
      if min(seg)>=h-1 or max(seg)<=h+1: return 1
  return 0
bad=[]
import itertools
for n in range(0,N):
  for tup in itertools.product('AS',repeat=n):
    w=''.join(tup); th=theta(w)
    for ch in 'AS':
      if theta(w+ch)>th-gain(w+ch): bad.append(w+ch)
print(len(bad),sorted(bad,key=len)[:10])
