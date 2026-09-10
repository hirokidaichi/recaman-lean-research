#!/usr/bin/env python3
"""H-20260910-16: frozen full-block collision-lag falsifier."""
import hashlib, itertools, json, pathlib, subprocess

def stats(w): return sum(w),sum((i+1)*x for i,x in enumerate(w))
def main():
    print('protocol=H-20260910-16',flush=True)
    print('source_revision='+subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),flush=True)
    print('source_sha256='+hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),flush=True)
    for p in range(1,11):
        count=collisions=free=expanded=0
        tails=[(r,v,*stats(v)) for r in range(p) for v in itertools.product((-1,1),repeat=r)]
        for b in itertools.product((-1,1),repeat=p):
            S,B=stats(b)
            if S<1:continue
            for r,v,s,C in tails:
                for q in range(4*p+6):
                    count+=1;d=q*p+r;m=q*S+s;M=q*B+p*S*q*(q-1)//2+q*p*s+C
                    if p<=5:
                        assert stats(b*q+v)==(m,M);expanded+=1
                    if m==1:
                        if M==0:
                            assert q<4*p+4;free+=1
                    elif M%(m-1)==0 and M//(m-1)>d:
                        assert q<4*p+4,(p,b,v,q,M//(m-1));collisions+=1
        print(('DISCOVERY=' if p<=7 else 'HOLDOUT=')+json.dumps(dict(p=p,tests=count,collision_clocks=collisions,all_clock_P2=free,expanded_crosschecks=expanded)),flush=True)
    for q in (1,10,100):
        w=(1,1,1,-1,-1,-1)*q;m,M=stats(w);n=9*q
        assert M==n*(m-1) and n>len(w)
        print('ZERO_DRIFT_CONTROL='+json.dumps(dict(q=q,length=len(w),clock=n,mass=m,moment=M)),flush=True)
    print('PASS: positive-period lag bound; zero-drift premise control',flush=True)
if __name__=='__main__':main()
