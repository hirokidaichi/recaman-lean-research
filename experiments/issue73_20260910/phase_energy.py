#!/usr/bin/env python3
import itertools,json,hashlib,pathlib,subprocess

def calc(b):
 p=len(b);S=sum(b);P=[0];W=[0]
 for t,s in enumerate(b):P.append(P[-1]+s);W.append(W[-1]+t*s)
 A=2*W[p]-p*S
 H=[2*S*W[t]-p*P[t]**2-A*P[t] for t in range(p)]
 D=[2*(S*t-p*P[t])+p-A for t in range(p)]
 return P,W,H,D

def p2(b,t):
 m=M=0;out=[];p=len(b)
 for d in range(1,p*(p+1)+1):
  s=b[(t-d)%p];m+=s;M+=d*s
  if m==1 and M==0:out.append(d)
 return out

def main():
 print('protocol=H-20260910-19',flush=True)
 print('source_revision='+subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),flush=True)
 print('source_sha256='+hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),flush=True)
 for p in range(1,19):
  count=checks=0
  for b in itertools.product((-1,1),repeat=p):
   if sum(b)<=0:continue
   count+=1;P,W,H,D=calc(b);A=[t for t in range(p) if b[t]==1]
   if p<=8:
    for t in range(p):
     for d in p2(b,t):assert H[(t-d)%p]==H[t]-D[t];checks+=1
   if all(H[t]-D[t] in H for t in A):
    out=dict(p=p,word=''.join('A' if x==1 else 'S' for x in b),S=sum(b),P=P,W=W,H=H,D=D,
     A=[dict(t=t,target=H[t]-D[t],energy_phases=[u for u in range(p) if H[u]==H[t]-D[t]],P2=p2(b,t)) for t in A])
    print('REFUTED='+json.dumps(out),flush=True)
    print('STOPPED: raw energy support is too weak; no holdout or congruence repair',flush=True);return
  print(('DISCOVERY=' if p<=14 else 'HOLDOUT=')+json.dumps(dict(p=p,positive_words=count,P2_identity_checks=checks)),flush=True)
 print('COMPUTED: all declared ranges pass; universal obstruction remains unproved',flush=True)
if __name__=='__main__':main()
