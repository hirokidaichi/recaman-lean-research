from pathlib import Path
import json,hashlib
P=Path(__file__).resolve().parent
def audit(w):
 H=[0];B=[0];E=F=S=0;ss={};defs=[]
 for q,c in enumerate(w):
  src=[];m=b=0
  for k,z in enumerate(reversed(w[:q]),1):
   a=1 if z=='A'else-1;m+=a;b+=k*a
   if m==1 and b==0:src.append(q-k)
  if c=='A':ss[q]=sorted(src);E+=bool(src);F+=not bool(src)
  else:S+=1
  H.append(H[-1]+(1 if c=='A'else-1));B.append(B[-1]+H[-1]);defs.append(S-E)
 return H,B,ss,defs
rows=[]
for label,rs in [('discovery',[1,2]),('holdout',[7,13])]:
 for r in rs:
  q=3*r+7;prefix='SS'+'A'*(2*(r+2))+'S'*(r+1);f=prefix+'A'
  assert len(prefix)==q
  H,B,fs,fd=audit(f)
  assert min(fd)>=1 and [t for t,z in fs.items()if z]==[4] and fs[q]==[]
  priorfree=sum(not z for t,z in fs.items()if t<q);assert priorfree==2*r+3
  assert H[q]==r+1 and 2*B[q]==r*(2*q+r+1)
  ds=[]
  for d in range(r+3):
   g='S'*d+f;Gh,Gb,gs,gd=audit(g)
   assert min(gd)>=1
   gains=[]
   for t,c in enumerate(f):
    old=bool(fs.get(t,[]));new=bool(gs.get(d+t,[]))
    predicted=old or(c=='A'and 2<=H[t]<=d+1 and 2*B[t]==(H[t]-1)*(2*t+H[t]))
    assert new==predicted
    if new and not old:gains.append(t)
   assert gains==([q]if d>=r else[])
   if d>=r:assert gs[d+q]==[d-r]
   ds.append({'d':d,'gains':gains,'all_positive':True})
  rows.append({'split':label,'r':r,'q':q,'prior_original_free':priorfree,'target_sources_f':fs[q],'all_d_spectrum_verified':ds,'canonical_orbit_reachability':False,'f_word_sha256':hashlib.sha256(f.encode()).hexdigest()})
(P/'head-depth-rank-summary.json').write_text(json.dumps({'rows':rows,'scope':'COMPUTED finite parameters, all original source sets reverse-exhausted; ALL-r proof is separate PAPER'},indent=2)+'\n');print(json.dumps(rows))
