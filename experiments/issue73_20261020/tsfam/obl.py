import sys
from collections import Counter
DM,QM=6,16
cfgs=[]
for line in open(sys.argv[1]):
    p=line.split(); d=int(p[0]); last=p[1]
    c=Counter(tuple(map(int,x.split(','))) for x in p[2:])
    cfgs.append((d,last,c))
def holds(S,s,L):
    # obligation: S (multiset) present, d<=s, last in L  is impossible
    if s<0: return True,None
    need=Counter(S)
    for d,last,c in cfgs:
        if d<=s and last in L and all(c[k]>=v for k,v in need.items()): return False,(d,last,sorted(c.elements()))
    return True,None
def inwin(S): return all(-DM<=D<=DM and -QM<=Q<=QM for D,Q in S)
def rm00(S):
    S=list(S)
    if (0,0) in S: S.remove((0,0))
    return S
def pred(S,s,L):
    out=[]
    S=rm00(S)
    if 'S' in L: out.append((tuple(sorted((D+1,Q) for D,Q in S)),s-1,'AS-'))
    if 'A' in L:
        Sa=[(D-1,Q-2*D+1) for D,Q in S]
        out.append((tuple(sorted(Sa)),s,'AS-'))
        out.append((tuple(sorted(Sa+[(1,0)])),s+1,'AS-'))
    return out
seeds=[]
JM=int(sys.argv[2]) if len(sys.argv)>2 else 3
for j in range(0,JM):
  for i in range(0,JM):
    if i+j>=1 or True:
      seeds.append((tuple(sorted([(j+1,0),(i+j,-(2*i+1))])),2,'A'))
seen={}; queue=list(seeds); bad=[]; unres=[]
SMAXD=int(sys.argv[3]) if len(sys.argv)>3 else 4
while queue:
    ob=queue.pop()
    if ob in seen: continue
    S,s,L=ob
    if s<0: seen[ob]=True; continue
    if len(S)==0: seen[ob]=False; bad.append((ob,'EMPTY')); continue
    if not inwin(S) or s>SMAXD: seen[ob]=None; unres.append(ob); continue
    ok,w=holds(S,s,L); seen[ob]=ok
    if not ok: bad.append((ob,w)); continue
    for p in pred(S,s,L): queue.append(p)
print("obligations:",len(seen),"false:",len(bad),"unresolved:",len(unres))
for b in bad[:15]: print("FALSE",b)
from collections import Counter as C
print("unres by s:",C(o[1] for o in unres), "examples:",unres[:5])
