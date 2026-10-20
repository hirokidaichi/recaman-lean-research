import sys
DM,QM=7,20; NQ=2*QM+1; NS=(2*DM+1)*NQ
def load(fn):
    b=open(fn,'rb').read(); o=2*NS*NS
    return (lambda c,x,y: b[c*NS*NS+x*NS+y]), (lambda c,x: b[o+c*NS+x])
def sid(D,Q): return (D+DM)*NQ+(Q+QM)
f0,g0=load(sys.argv[1]); f1,g1=load(sys.argv[2])
for c in (1,0):
  print("singles c=",'SA'[c],"data/fix  rows D=-2..4, Q=-6..6")
  for D in range(-2,5):
    print(" D=%2d "%D+" ".join("%d/%d"%(g0(c,sid(D,Q)),g1(c,sid(D,Q))) for Q in range(-6,7)))
