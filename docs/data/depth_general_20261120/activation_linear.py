import json,sys,hashlib
from pathlib import Path
W='SSAAASSSSAAAASAS'
mode=sys.argv[1]
params=[('linear_m1',8,35,75),('linear_m3',20,85,185)]
def audit(w):
 H=[0];B=[0]
 for c in w:H.append(H[-1]+(1 if c=='A' else -1));B.append(B[-1]+H[-1])
 src=[];free=[];E=0;S=0;defs=[]
 for q,c in enumerate(w):
  direct=[u for u in range(q) if H[q]==H[u]+1 and B[q]-B[u]-(q-u)*H[u]==0] if c=='A' else []
  rev=[]
  if c=='A':
   mass=0;moment=0
   for k in range(1,q+1):
    mass+=(1 if w[q-k]=='A' else -1);moment+=k*(1 if w[q-k]=='A' else -1)
    if mass==1 and moment==0:rev.append(q-k)
  assert direct==sorted(rev),(q,direct,rev)
  src.append(direct)
  if c=='A':
   if direct:E+=1
   else:free.append(q)
  else:S+=1
  defs.append(S-E)
 return {'word':w,'H':H,'B':B,'sources':src,'free':free,'deficits':defs}
rows=[]
for tag,N,z,U in params:
 h=2;r=U-h;a=U+z;j=z-1
 w='S'*h+'A'*a+W*N+'S'*j+'A';q=len(w)-1
 f=audit(w);g=audit('S'*r+w)
 row={'tag':tag,'N':N,'z':z,'U':U,'r':r,'q':q,'prior_free':len([x for x in f['free'] if x<q]),'conjectured_lower':2*r+2,'upper_from_local_sources':a-1+4*N,'original_positive_through_q':min(f['deficits'][:q])>=1,'target_original_sources':f['sources'][q],'target_padded_sources':g['sources'][r+q],'root_area':g['B'][r+q],'root_height':g['H'][r+q],'f':f,'g':g}
 assert U*U==z*z+N*(16*z-10)
 assert row['original_positive_through_q'] and f['sources'][q]==[]
 assert g['sources'][r+q]==[0] and row['root_area']==0 and row['root_height']==1
 assert row['prior_free']<=a-1+4*N<2*r+2
 rows.append(row)
Path(sys.argv[2]).write_text(json.dumps({'mode':mode,'rows':rows},indent=2)+'\n')
print(json.dumps([{k:v for k,v in x.items() if k not in ['f','g']}for x in rows]))
