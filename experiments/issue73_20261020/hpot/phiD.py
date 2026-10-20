# test Phi_D(T) = #{valid (d,c): c<0} - #{valid (d,c): c=-1, d>=2}, valid = walk since t never below F(t)-D
# (points with d < -D are discarded).  gains: A step with (1,-1) valid. Check: Phi>=0, Phi(after)<=Phi(before)-gain.
import sys
D=int(sys.argv[1]); N=int(sys.argv[2])
def step(T,s):
  if s>0: T2={(d+1,c) for d,c in T}
  else: T2={(d-1,c+2*d-1) for d,c in T}
  T2={(d,c) for d,c in T2 if d>=-D}; T2.add((0,0)); return frozenset(T2)
def phi(T): return sum(1 for d,c in T if c<0)-sum(1 for d,c in T if c==-1 and d>=2)
bad=0; ex=[]; cnt=0
stack=[(frozenset({(0,0)}),'')]
while stack:
  T,w=stack.pop(); cnt+=1
  if len(w)==N: continue
  for s in (1,-1):
    g=(1 if (1,-1) in T else 0) if s>0 else -1
    T2=step(T,s)
    if phi(T2)>phi(T)-g:
      bad+=1
      if len(ex)<5: ex.append(w+('A' if s>0 else 'S'))
    stack.append((T2,w+('A' if s>0 else 'S')))
print('D',D,'N',N,'nodes',cnt,'violations',bad,ex)
