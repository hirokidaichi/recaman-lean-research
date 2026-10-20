import sys
def analyze(w):
    s=[1 if ch=='A' else -1 for ch in w]; n=len(s)
    F=[0]
    for x in s: F.append(F[-1]+x)
    def win(t,b): # window [t,b-1], P2: mass 1, moment sum sigma(c)(b-c)=0
        return sum(s[t:b])==1 and sum(s[c]*(b-c) for c in range(t,b))==0
    E=[s[b]==1 and any(win(t,b) for t in range(0,b)) for b in range(n)]
    # last maximal run of endable A's separated only by S's ending at last A
    As=[i for i in range(n) if s[i]==1]
    run=[]
    for b in reversed(As):
        if not E[b]: break
        run.append(b)
        if b>0 and s[b-1]==1 and not E[b-1]: break
    run=run[::-1]
    out=[]
    for r0 in range(len(run)):  # sub-runs b_{r0}..last ; but tsr uses last r; report for each start
        b1=run[r0]; q=b1
        while q>0 and s[q-1]==-1: q-=1
        sl=sum(1 for u in range(q) if s[u]==-1)-sum(1 for u in range(q) if E[u])
        out.append((len(run)-r0,q,sl))
    # also runs starting at first: prefix runs
    return run,out,[ (b,[t for t in range(b) if win(t,b)]) for b in run]
for w in sys.argv[1:]:
    run,out,st=analyze(w); print(w); print(' run',run); print(' (r from tail,q*,slack)',out); print(' starts',st)
