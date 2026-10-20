import sys
DM,QM=6,16; ND,NQ=2*DM+1,2*QM+1; NS=ND*NQ
class M:
    def __init__(s,b,off,shape): s.b=b; s.off=off
def load(fn):
    b=open(fn,'rb').read()
    def mn(last,i,j): return b[last*NS*NS+i*NS+j]
    o=2*NS*NS
    def mn1(last,i): return b[o+last*NS+i]
    return mn,mn1
def sid(D,Q): return (D+DM)*NQ+(Q+QM)
def dq(i): return (i//NQ-DM, i%NQ-QM)
