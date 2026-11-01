import sys
DM,QM,R=7,20,4; NQ=2*QM+1; NS=(2*DM+1)*NQ
b=open(sys.argv[1],'rb').read(); o=2*(R+1)*NS*NS
def sid(D,Q): return (D+DM)*NQ+(Q+QM)
def phi(c,r,x,y): return b[(c*(R+1)+r)*NS*NS+sid(*x)*NS+sid(*y)]
def psi(c,r,x): return b[o+(c*(R+1)+r)*NS+sid(*x)]
for c,r,x,y in [(1,0,(1,0),(0,-1)),(1,4,(0,-1),(-1,0)),(0,4,(-1,0),(-2,3)),(1,4,(0,0),(-1,3)),(0,4,(-1,1),(-2,6)),(1,4,(0,1),(-1,6)),(1,4,(0,3),(-1,12)),(1,4,(0,5),(-1,18))]:
    print(c,r,x,y,"phi",[phi(c,rr,x,y) for rr in range(R+1)],"psi",[psi(c,rr,x) for rr in range(R+1)])
