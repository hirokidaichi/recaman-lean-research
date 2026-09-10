#!/usr/bin/env python3
import itertools,json,hashlib,pathlib,subprocess

def word(g):
 out=[]
 for i,a in enumerate(g):
  if i:out.append(-1)
  out.extend([1]*a)
 return tuple(out)
def p2s(w):
 m=M=0;out=[]
 for i,s in enumerate(w,1):
  m+=s;M+=i*s
  if m==1 and M==0:out.append(i)
 return out
def gap(w):
 g=[0]
 for s in w:
  if s==1:g[-1]+=1
  else:g.append(0)
 return g
def classify(g):
 n=len(g)-1;zeros=[i for i in range(1,n) if g[i]==0];large=[i for i in range(1,n) if g[i]>1]
 if len(zeros)!=1 or len(large)!=1:return None
 z=zeros[0];j=large[0]
 if g[0]==g[-1]==0 and g[j]==4 and n==6*j-2*z+1:return 'A'
 if g[0]==1 and g[-1]==0 and g[j]==3 and n==4*j-2*z+1:return 'B'
 return None

def main():
 print('protocol=H-20260910-22',flush=True)
 print('source_revision='+subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),flush=True)
 print('source_sha256='+hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),flush=True)
 groups={name:dict(P2=0,minimal_A=0,minimal_B=0,earlier_AAS=0,earlier_clean=0) for name in ('DISCOVERY','HOLDOUT')}
 generated=set()
 for n in range(3,258):
  group=groups['DISCOVERY' if n<=63 else 'HOLDOUT']
  shapes=[(a,3-a,0,None) for a in range(4)]+[(a,1-a,2,j) for a in (0,1) for j in range(1,n)]+[(0,0,3,j) for j in range(1,n)]
  for a,last,h,j in shapes:
   # Solve the exact integer moment equation for z; independent construction follows.
   numer=(2*h*j if j is not None else 0)+1-n*(2*a+2*h-5)
   if numer%2:continue
   z=numer//2
   if not(1<=z<n) or z==j:continue
   g=[a]+[1]*(n-1)+[last];g[z]=0
   if j is not None:g[j]=h+1
   w=word(g);hits=p2s(w)
   assert len(w)==2*n+1 and hits[-1]==len(w)
   assert sum(w[i:i+2]==(-1,-1) for i in range(len(w)-1))==1
   assert all(w[i:i+4]!=(-1,1,1,-1) for i in range(len(w)-3))
   f=classify(g);minimal=hits[0]==len(w)
   assert minimal==(f is not None),(n,g,hits,f)
   group['P2']+=1
   if f:group['minimal_'+f]+=1
   elif a==2:assert hits[0]==3;group['earlier_AAS']+=1
   else:assert a==0 and h==2 and hits[0]==8*j+3;group['earlier_clean']+=1
   if len(w)<=17:generated.add(w)
 for name,data in groups.items():print(name+'='+json.dumps(data),flush=True)
 raw=set();raw_min=0
 for d in range(1,18):
  for w in itertools.product((-1,1),repeat=d):
   if sum(w)!=1:continue
   if sum((i+1)*s for i,s in enumerate(w)):continue
   if sum(w[i:i+2]==(-1,-1) for i in range(d-1))!=1:continue
   if any(w[i:i+4]==(-1,1,1,-1) for i in range(d-3)):continue
   raw.add(w);f=classify(gap(w));assert (p2s(w)[0]==d)==(f is not None);raw_min+=bool(f)
 assert raw==generated
 control=tuple(1 if c=='A' else -1 for c in 'SASAAAASSASASAS')
 assert classify(gap(control))=='A' and p2s(control)==[15]
 print('RAW_BINARY='+json.dumps(dict(max_length=17,P2_words=len(raw),minimal=raw_min,generator_exact=True)),flush=True)
 print('E112_CONTROL='+json.dumps(dict(word='SASAAAASSASASAS',family='A',gaps=gap(control))),flush=True)
 print('PASS: both classification directions and minimality; no capacity claim',flush=True)
if __name__=='__main__':main()
