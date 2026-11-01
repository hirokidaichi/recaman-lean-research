# backward walk view of minimal P2 words: y0=1, A:-1, S:+1, area before step
from itertools import product
def walk(w):
    y=[1]; a=[0]
    for b in w:
        a.append(a[-1]+y[-1]); y.append(y[-1]+(-1 if b else 1))
    return y,a
def mins(L):
    out=[]
    def rec(w,y,ar):
        d=len(w)
        if d>0 and y==0 and ar==0:
            if d==L: out.append(tuple(w))
            return
        if d==L: return
        # pruning: remaining steps r: need reach y=0; |y|<=r
        r=L-d
        if abs(y)>r: return
        for b in (True,False):
            rec(w+[b], y+(-1 if b else 1), ar+y)
    rec([],1,0)
    return out
def s(w): return ''.join('A' if b else 'S' for b in w)
if __name__=='__main__':
    for L in (3,7,11,15,19,23):
        ws=mins(L); print(L,len(ws))
