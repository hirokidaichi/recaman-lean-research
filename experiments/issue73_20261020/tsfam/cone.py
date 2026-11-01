import sys
DM,QM=7,20; NQ=2*QM+1; NS=(2*DM+1)*NQ
b=open(sys.argv[1],'rb').read(); o=2*NS*NS
def inw(x): return -DM<=x[0]<=DM and -QM<=x[1]<=QM
def sid(D,Q): return (D+DM)*NQ+(Q+QM)
V={}  # node -> value ; nodes: ('P',c,x,y) ('S',c,x)
def init(n):
    if n[0]=='P': return b[n[1]*NS*NS+sid(*n[2])*NS+sid(*n[3])]
    return b[o+n[1]*NS+sid(*n[2])]
def pr(c,x): return (x[0]-1,x[1]-2*x[0]+1) if c else (x[0]+1,x[1])
def deps(n):
    # returns list of alternatives; each alternative = (list of (kind,args) whose max ... ) we evaluate via function
    pass
def val(n):
    if n not in V: V[n]=init(n); todo.append(n)
    return V[n]
def sany(x):
    if not inw(x): return 0,None
    if x==(0,0): return 0,None
    return min((max(val(('S',0,x)),0),('S',0,x)),(val(('S',1,x)),('S',1,x)))
def pany(x,y):
    if not inw(x): return 0,None
    if not inw(y): return sany(x)
    best=None
    for c in (0,1):
        v=max(val(('P',c,x,y)),sany(x)[0] if False else val(('S',c,x)) if x!=(0,0) else 0)
        if best is None or v<best[0]: best=(v,('P',c,x,y))
    return best
def J1(c,x):
    a=pr(c,x)
    if not c: v,w=sany(a); return v+1,[('S-step',w)]
    v,w=sany(a); alts=[(v,('A-nonend',w))]
    p,w2=pany(a,(1,0)); alts.append((max(v,p)-1,('A-end-other',w,w2)))
    if a==(1,0): alts.append((v-1,('A-end-self',w)))
    m=min(alts,key=lambda z:z[0]); return max(m[0],0),m[1]
def J2(c,x,y):
    alts=[]
    if y==(0,0): v,w=J1(c,x); alts.append((v,('fresh',w)))
    a=pr(c,x); e=pr(c,y)
    P,w=pany(a,e)
    if not c: alts.append((P+1,('S',w)))
    else:
        alts.append((P,('A-nonend',w)))
        q,w2=pany(a,(1,0)); alts.append((max(P,q)-1,('A-end-other',w,w2)))
        if a==(1,0) or e==(1,0): alts.append((P-1,('A-end-in',w)))
    m=min(alts,key=lambda z:z[0]); v=max(m[0],0)
    if not c: v=max(v,1)
    return v,m[1]
todo=[]
seed=('P',1,(1,0),(0,-1))
val(seed)
# fixpoint by worklist (recompute all until stable), building cone lazily
it=0
while True:
    ch=0; nodes=list(V.keys())
    for n in nodes:
        if n[0]=='P':
            if not(inw(n[2]) and inw(n[3])): continue
            v,_=J2(n[1],n[2],n[3])
        else:
            if n[2]==(0,0): continue
            v,_=J1(n[1],n[2])
        if v<V[n]: V[n]=v; ch+=1
    it+=1; print("iter",it,"nodes",len(V),"changes",ch,"seed",V[seed]); sys.stdout.flush()
    if ch==0 and len(nodes)==len(V): break
    if it>40: break
# trace
n=seed
for k in range(25):
    if n is None: break
    if n[0]=='P': v,why=J2(n[1],n[2],n[3])
    else: v,why=J1(n[1],n[2])
    print(n,"V=",V[n],"why",why)
    nxt=[w for w in why[1:] if isinstance(w,tuple) and w and w[0] in('P','S')]
    # choose the dependency with minimal value
    n=min(nxt,key=lambda z:V.get(z,99)) if nxt else None
