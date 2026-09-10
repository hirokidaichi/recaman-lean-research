#!/usr/bin/env python3
import json,hashlib,pathlib,subprocess

def w(k):return (-1,1)*k+(-1,1,1,1,1,-1,-1)+(1,-1)*(3*k)
def hits(v):
 m=M=0;out=[]
 for d,s in enumerate(v,1):
  m+=s;M+=d*s
  if m==1 and M==0:out.append(d)
 return out
def main():
 print('protocol=H-20260910-23',flush=True)
 print('source_revision='+subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),flush=True)
 print('source_sha256='+hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),flush=True)
 for k in range(257):
  v=w(k);assert len(v)==8*k+7 and hits(v)==[len(v)]
  assert [i for i in range(len(v)-1) if v[i:i+2]==(-1,-1)]==[2*k+5]
  assert all(v[i:i+4]!=(-1,1,1,-1) for i in range(len(v)-3))
 print('FAMILIES='+json.dumps(dict(discovery=[0,32],holdout=[33,256],max_minimum_lag=2055)),flush=True)
 for K in list(range(33))+[64,128,256]:
  history=(1,)+w(K);positions=[]
  for k in range(K+1):
   s=2*(K-k);assert history[s]==1
   assert history[s+1:s+1+len(w(k))]==w(k)
   assert s+1+(2*k+5)==2*K+6
   positions.append(s)
  assert len(set(positions))==K+1
  print('EMBEDDING='+json.dumps(dict(K=K,current_A_sources=K+1,shared_SS_indices=[2*K+6,2*K+7])),flush=True)
 print('PASS: unbounded multiplicity in one finite no-SAAS history; no canonical claim',flush=True)
if __name__=='__main__':main()
