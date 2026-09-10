#!/usr/bin/env python3
import json,hashlib,pathlib,subprocess

def main():
 print('protocol=H-20260910-21',flush=True)
 print('source_revision='+subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),flush=True)
 print('source_sha256='+hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),flush=True)
 for b in (0,1,5,100):
  transitions=windows=seed_blocks=generated_blocks=nonpositive=0
  for v in (0,1,7,100):
   for seed in ([],[0],[0,v],[1,3,9]):
    x=[v];seen=list(seed);signs=[]
    for j in range(256):
     n=b+j+1;c=x[-1]-n;A=c<=0 or c in seen;s=1 if A else -1
     if A:
      if c<=0:nonpositive+=1
      elif c in seed:seed_blocks+=1
      else:assert c in x[1:];generated_blocks+=1
     assert all(z in seed or z in x[1:] for z in seen)
     signs.append(s);x.append(x[-1]+n*s);seen.append(x[-1]);transitions+=1
     assert x[-1]>=0 and x[-1]-x[-2]==n*s
     for d in range(min(j+1,16)+1):
      w=list(reversed(signs[-d:])) if d else []
      m=sum(w);M=sum((i+1)*s for i,s in enumerate(w))
      assert x[-1]-x[j+1-d]==(n+1)*m-M;windows+=1
  print(('DISCOVERY=' if b<=1 else 'HOLDOUT=')+json.dumps(dict(base=b,transitions=transitions,windows=windows,seed_blockers=seed_blocks,generated_blockers=generated_blocks,nonpositive=nonpositive)),flush=True)
 print('PASS: exact seeded history and absolute-clock window semantics',flush=True)
if __name__=='__main__':main()
