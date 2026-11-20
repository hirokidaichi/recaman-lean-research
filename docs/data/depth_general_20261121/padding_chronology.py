import json, sys
from pathlib import Path
cfg=json.loads(Path(sys.argv[1]).read_text())
def ledger(w):
 H=[0];B=[0]
 for c in w:H.append(H[-1]+(1 if c=='A' else -1));B.append(B[-1]+H[-1])
 sources={};free=[];E=S=0;positive=True
 for q,c in enumerate(w):
  if c=='S':S+=1
  else:
   src=[u for u in range(q)if H[q]==H[u]+1 and B[q]-B[u]==(q-u)*H[u]]
   m=a=0;rev=[]
   for u in range(q-1,-1,-1):
    z=1 if w[u]=='A' else -1;m+=z;a+=(q-u)*z
    if m==1 and a==0:rev.append(u)
   assert src==sorted(rev);sources[q]=src
   if src:E+=1
   else:free.append(q)
  positive &= S>=E+1
 col=[]
 for v in range(1,len(w)+1):
  if w[v-1]!='S':continue
  for u in range(v):
   if H[u]==H[v] and B[v]-B[u]==(v-u)*H[v]:col.append(['I',u,v])
  for q in range(v):
   if w[q]=='A' and H[q]-1==H[v] and B[v]-B[q]==(v-q)*H[v]:col.append(['II',q,v])
 return dict(word=w,H=H,B=B,sources=sources,free=free,positive=bool(positive),collisions=col)
rows=[]
for r in cfg['discovery_r']+cfg['parameter_controls_r']:
 f=ledger('SS'+'A'*(2*r+4)+'S'*(r+2));assert not f['collisions']
 activation=[]
 for q,c in enumerate(f['word']):
  a=f['H'][q]-1
  if c=='S' and a>=1 and 2*f['B'][q]==a*(2*q+a+1):activation.append([q,a])
 assert activation==[[len(f['word'])-1,r]]
 for d in sorted({0,r-1,r,r+1,2*r+3}):
  z=ledger('S'*d+f['word']);assert z['positive'] and len(z['free'])==2*r+3
  assert z['free']==[q+d for q in f['free']]
  assert len([q for q in z['free']if z['H'][q]<=1-(d+2)])==2
  assert all(z['sources'][q+d]==[u+d for u in src]for q,src in f['sources'].items())
  expected=[] if d<r else [['I',d-r,len(z['word'])]]
  assert z['collisions']==expected,(r,d,z['collisions'])
  n=len(z['word'])+1;b=100*n*n;x=100*(b+n)*n
  seed={0,x}|{x+(b+q+1)*(z['H'][q]-1)-z['B'][q]for q in z['free']}
  cur=x;seen=set(seed);mismatch=[]
  for q,c in enumerate(z['word']):
   clock=b+q+1;cand=cur-clock;A=cand<=0 or cand in seen
   if A!=(c=='A'):mismatch.append(q)
   cur=cur+clock if A else cand;seen.add(cur)
  assert mismatch==([] if d<r else [len(z['word'])-1]),(r,d,mismatch)
  rows.append(dict(r=r,d=d,word=z['word'],sources=z['sources'],free=z['free'],positive=z['positive'],low_free=2,
                   collisions=z['collisions'],actual_replay_first_mismatch=mismatch,base=b,current=x,seed=sorted(seed)))
Path(sys.argv[2]).write_text(json.dumps({'rows':rows,'scope':'NEW S-side threshold predicate and all-source preservation on known hill geometry; finite controls, not an all-r proof or canonical reachability'},indent=2)+'\n')
print(json.dumps({'PASS':True,'rows':len(rows),'r_controls':cfg['discovery_r']+cfg['parameter_controls_r'],'source_tags_and_low_free_preserved':True,'coherent_execution_iff_d_less_r':True,'first_mismatch_only_last_S':True}))
