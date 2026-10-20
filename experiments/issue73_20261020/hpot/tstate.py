# T-state reformulation: points (d,c), d=F(k)-F(t), c=a-d(d+1)/2, a=sum_{v=t+1}^k (F(v)-F(t)).
# step +1: (d,c)->(d+1,c); step -1: (d,c)->(d-1,c+2d-1); add (0,0). gain on A iff (1,-1) in T.
def step(T,s):
  if s>0: T2={(d+1,c) for d,c in T}
  else: T2={(d-1,c+2*d-1) for d,c in T}
  T2.add((0,0)); return frozenset(T2)
def gain(T,s):
  return (1 if (1,-1) in T else 0) if s>0 else -1
def endcount(st):
  F=[0];G=[0]
  for ch in st: F.append(F[-1]+(1 if ch=='A' else -1)); G.append(G[-1]+F[-1])
  e=0
  for b in range(len(st)):
    if st[b]=='A' and any(F[b]==F[t]+1 and G[b]-G[t]==(b-t)*F[t] for t in range(b-3,-1,-4)): e+=1
  return e
if __name__=='__main__':
  import itertools
  for n in range(1,15):
    for w in itertools.product('AS',repeat=n):
      T=frozenset({(0,0)}); g=0
      for ch in w:
        s=1 if ch=='A' else -1; g+=gain(T,s); T=step(T,s)
      st=''.join(w)
      assert g==endcount(st)-st.count('S'),st
  print('T-state reformulation agrees with direct endability for all strings <=14')
