#!/usr/bin/env python3
import itertools,json,hashlib,pathlib,subprocess

def main():
 print('protocol=H-20260910-18',flush=True)
 print('source_revision='+subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),flush=True)
 print('source_sha256='+hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),flush=True)
 for p in range(1,13):
  supplied=0;windows=0
  for b in itertools.product((-1,1),repeat=p):
   if sum(b)<=0:continue
   for t in range(p):
    m=M=0
    for d in range(1,p*(p+1)+p+1):
     s=b[(t-d)%p];m+=s;M+=d*s;windows+=1
     if m==1 and M==0:assert d<p*(p+1);supplied+=1
  print(('DISCOVERY=' if p<=8 else 'HOLDOUT=')+json.dumps(dict(p=p,windows=windows,P2=supplied)),flush=True)
 for q in range(65):
  w=(1,1,-1,-1)*q+(1,1,-1)
  assert sum(w)==1 and sum((i+1)*s for i,s in enumerate(w))==0
 print('BALANCED_CONTROL='+json.dumps(dict(q_range=[0,64],lags=[3,259],period=4)),flush=True)
 count=0
 for p in range(1,9):
  for N in range(7):
   for b in itertools.product((-1,1),repeat=p):
    def f(n):return (-1 if n%2 else 1) if n<N else b[(n-N)%p]
    def e(t):return f(N+(t-N)%p)
    for t in range(-2*p,N+4*p+1):
     assert e(t+p)==e(t)
     if t>=N:assert e(t)==f(t)
     count+=1
 print('EXTENSION='+json.dumps(dict(checks=count)),flush=True)
 print('PASS: cutoff and exact natural/integer periodic-tail representation',flush=True)
if __name__=='__main__':main()
