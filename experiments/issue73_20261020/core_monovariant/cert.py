"""Explicit certificate that no additive monovariant exists: a reachable path exit -> state whose windows are all
'good windows' (f forced 0) or closable (f<=0)."""
import sys
from collections import defaultdict, deque
import core
L=int(sys.argv[1]); K=int(sys.argv[2]); core.setb(L,K)
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
zero={w[:4] for s in good if s!='END' for w in s}
def nonpos(s): return all(w[:4] in zero or core.closable(w) for w in s)
exits=[(a,b,i) for a in good if a!='END' for b,i in g[a] if b!='END' and b not in good]
par={}
dq=deque()
for a,b,i in exits:
    if b not in par: par[b]=(a,i); dq.append(b)
while dq:
    s=dq.popleft()
    if nonpos(s) and s not in good:
        path=[]; cur=s
        while cur in par:
            p,i=par[cur]; path.append((p,i,cur)); cur=p
            if cur in good: break
        for p,i,c in reversed(path): print(p,'--',i,'->',c)
        break
    for t,i in g.get(s,[]):
        if t!='END' and t not in par and t not in good: par[t]=(s,i); dq.append(t)
print('zero windows:',sorted(zero))
