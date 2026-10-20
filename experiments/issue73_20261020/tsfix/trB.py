import sys
DM,QM,R=5,14,2; NQ=2*QM+1; NS=(2*DM+1)*NQ
T=open(sys.argv[1],'rb').read()
def inw(x): return -DM<=x[0]<=DM and -QM<=x[1]<=QM
def sid(x): return (x[0]+DM)*NQ+(x[1]+QM)
def t(c,r,x,y,z): return T[((((c*(R+1)+r)*NS+sid(x))*NS+sid(y))*NS)+sid(z)]
def pr(c,x): return (x[0]-1,x[1]-2*x[0]+1) if c else (x[0]+1,x[1])
def L(r,a,es):
    if not inw(a): return max(0,-a[0]),None
    es=[e if (e is not None and inw(e)) else (0,0) for e in es]
    best=None
    for c in (0,1):
        v=t(c,r,a,es[0],es[1])
        if best is None or v<best[0]: best=(v,(c,r,a,es[0],es[1]))
    if all(e==(0,0) for e in es) and a==(0,0) and r==0: return 0,'BASE'
    return best
key=(1,0,(1,0),(0,-1),(0,0))
for step in range(30):
    c,r,x,y,z=key; V=t(*key); print("t-%d"%step,"c=%s r=%d old=%s n1=%s n2=%s V=%d"%("SA"[c],r,x,y,z,V))
    alts=[]
    for fy in ([False,True] if y==(0,0) else [False]):
      for fz in ([False,True] if z==(0,0) else [False]):
        a=pr(c,x); e1=None if fy else pr(c,y); e2=None if fz else pr(c,z)
        if c==0: v,k=L(r,a,[e1,e2]); alts.append((v+1,k,'S'))
        elif r==0:
            if (1,0) in (a,e1,e2): continue
            for rp in range(R+1): v,k=L(rp,a,[e1,e2]); alts.append((v,k,'A-nonend'))
        else:
            for rp in range(r-1,(R if r==R else r-1)+1):
                P,k=L(rp,a,[e1,e2]); W1,k1=L(rp,a,[e1,(1,0)]); W2,k2=L(rp,a,[e2,(1,0)])
                if (1,0) in (a,e1,e2): alts.append((P-1,k,'A-end-tracked'))
                m=max(P,W1,W2); kk=[kk for vv,kk in ((P,k),(W1,k1),(W2,k2)) if vv==m][0]
                alts.append((m-1,kk,'A-end-witness'))
    v,k,why=min(alts,key=lambda z:z[0]); print("    via",why,"value",max(v,0))
    if k is None or k=='BASE': print("    ->",k,"(out of window older / base)"); break
    key=k
