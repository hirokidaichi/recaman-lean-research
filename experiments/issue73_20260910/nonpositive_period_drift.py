#!/usr/bin/env python3
import itertools,json,hashlib,pathlib,subprocess

def main():
 print('protocol=H-20260910-20',flush=True)
 print('source_revision='+subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),flush=True)
 print('source_sha256='+hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),flush=True)
 for p in range(1,13):
  count=balanced=poly=0
  for b in itertools.product((-1,1),repeat=p):
   S=sum(b)
   if S>0:continue
   count+=1;B=[sum(i*b[(t-i)%p] for i in range(1,p+1)) for t in range(p)]
   assert 2*sum(B)==S*p*(p+1)
   for t in range(p):
    assert B[(t+1)%p]-B[t]==S-p*b[t]
    for q in range(5):
     direct=sum((t+i+1)*b[(t+i)%p] for i in range(q*p))
     formula=q*((t+1)*S-B[t])+p*S*q*(q+1)//2
     assert direct==formula;poly+=1
   if S==0:
    balanced+=1;t=next(t for t in range(p) if B[t]>0)
    for x0 in (0,7,100):assert x0-(x0+1)*B[t]<0
   else:
    for t in range(p):
     for x0 in (0,7,100):
      q=2*x0+2*abs(B[t])+4
      x=x0+q*((t+1)*S-B[t])+p*S*q*(q+1)//2
      assert x<0
  print(('DISCOVERY=' if p<=8 else 'HOLDOUT=')+json.dumps(dict(p=p,words=count,balanced=balanced,polynomial_crosschecks=poly)),flush=True)
 print('PASS: exact value-drift identities and nonpositive-drift controls',flush=True)
if __name__=='__main__':main()
