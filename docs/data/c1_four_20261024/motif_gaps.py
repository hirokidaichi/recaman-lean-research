"""Fixed six-word finite validation of the known five-supply motif."""
from pathlib import Path
import hashlib,json,resource
resource.setrlimit(resource.RLIMIT_CPU,(5,6))
def local(w):
 a=m=0
 for k,c in enumerate(reversed(w),1):
  d=1 if c=='A' else -1;a+=d;m+=k*d
  if a==1 and m==0:return True
 return False
def old(w):
 f=ar=0
 for c in w:f+=1 if c=='A' else -1;ar+=f
 r=1-f;b=-ar-len(w)*r
 return r>=1 and b>=1 and r*(r+1)<=2*b+2 and 4*b<=5*r*r-11*r+16 and (r!=1 or b==1),r,b
w='S'*5+'A'*3+'S'*4+'A'*2
nodes=[w]
for gap in [0,0,1,0,0]:w+='S'*gap+'A';nodes.append(w)
ans=[]
for i,w in enumerate(nodes):
 raw=[];coherent=[]
 for j in range(2*w.count('A')):
  v=w+'S'*j;le=local(v);oe,r,b=old(v)
  if le or oe:raw.append(dict(j=j,local=le,old=oe,mass=r,area=b))
  if le or oe and not(r==3 and b==5):coherent.append(j)
 ans.append(dict(node=i,word=w,raw=raw,with_area7_prefix=coherent))
out=dict(nodes=ans,expected=[0,0,1,0,0,None],source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
Path(__file__).with_name('motif-gaps.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
