import itertools
def walk(s):
    F=[0]
    for ch in s: F.append(F[-1]+(1 if ch=='A' else -1))
    return F
def endables(s,D=2):
    n=len(s); F=walk(s); G=[0]
    for u in range(1,n+1): G.append(G[-1]+F[u])
    out=[]
    for b in range(n):
        if s[b]!='A': continue
        t=None
        for tt in range(b-3,-1,-4):
            if F[b]==F[tt]+1 and G[b]-G[tt]==(b-tt)*F[tt]: t=tt;break
        if t is None: continue
        h=F[t]
        if h-min(F[t:b+1])>D: continue
        a=0; r=None
        for u in range(t+1,b):
            a+=F[u]-h
            if F[u]==h and a>0: r=u
        q=None
        if r is not None:
            q=max(c for c in range(t,r) if s[c]=='S' and F[c]==h+1)
        out.append(dict(b=b,t=t,h=h,r=r,q=q,clean=r is None))
    return F,out
def deepforced(s,k=None):
    F=walk(s); n=len(s) if k is None else k
    W={}
    for c in range(n):
        if s[c]!='S': continue
        for w in range(c+1,n+1):
            if F[w]==F[c]+1: break
            if F[w]==F[c]-3: W[c]=w;break
    return W
def show(s):
    F,E=endables(s); W=deepforced(s)
    print(s); print(' '.join(f"{i}:{c}{F[i]}{'*' if i in W else ''}" for i,c in enumerate(s)))
    for e in E: print('  ',e, s[e['t']:e['b']])
    print('   deepforced(c:witness):',W)
