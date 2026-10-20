import sys
DM,QM=7,20; NQ=2*QM+1; NS=(2*DM+1)*NQ
b=open(sys.argv[1],'rb').read(); o=2*NS*NS
def sid(D,Q): return (D+DM)*NQ+(Q+QM)
def phi(c,x,y): return b[c*NS*NS+sid(*x)*NS+sid(*y)]
def psi(c,x): return b[o+c*NS+sid(*x)]
def pany(x,y): return min(max(phi(c,x,y),psi(c,x)) for c in (0,1))
def sany(x): return min(psi(c,x) for c in (0,1))
for x,y in [((1,0),(0,-1)),((0,-1),(-1,0)),((0,-1),(1,0)),((-1,0),(0,-1)),((1,0),(1,-3)),((0,-1),(0,-4))]:
  print(x,y,"phiA",phi(1,x,y),"phiS",phi(0,x,y),"psiA(x)",psi(1,x),"psiS(x)",psi(0,x))
