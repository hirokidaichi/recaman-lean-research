import json,sys
from pathlib import Path
def run(b,x,seed,Q):
 seen=set(seed);cur=x;H=[0];values=[x];events=[]
 for q in range(Q):
  n=b+q+1;c=cur-n;A=not(c>0 and c not in seen);cur=cur+n if A else c;seen.add(cur);H.append(H[-1]+(1 if A else-1));values.append(cur);events.append({'q':q,'n':n,'candidate':c,'A':A})
 suffix=[0]*(Q+1);suffix[Q]=H[Q]
 for q in range(Q-1,-1,-1):suffix[q]=min(H[q],suffix[q+1])
 groups={};late={};Ygroups={Y:{}for Y in[0,1,2,3,6,10,20,50]}
 for e in events:
  if not e['A']:continue
  q=e['q'];y=e['candidate'];n=e['n'];k=H[q]
  if y<=n+6:assert suffix[q]>=k-1,(b,x,'future floor',e,H,suffix[q])
  if y>=0:
   key=(y,k);groups[key]=groups.get(key,0)+1;assert groups[key]<=1+max(y-3,0),(b,x,'capacity',key,groups[key])
   if n>=y-6:
    if y in late:assert k>late[y],(b,x,'late equal candidate height',e,k,late[y])
    late[y]=k
   for Y,g in Ygroups.items():
    if y<=Y and n>=max(1,Y-6):
     if k in g:assert y<=g[k]-3,(b,x,'same-height candidate drop',Y,e,g[k])
     g[k]=y
 assert min(H)>=-(x//(b+1))
 return {'b':b,'x':x,'H':H,'values':values,'events':events,'signs':''.join('A'if e['A']else'S'for e in events),'stock':sorted(seed)}
sharp=[]
for n in[2,3,17,29]:
 y=n+7;x=2*n+7;r=run(n-1,x,{0,y,x},4);assert r['signs']=='ASSS'and r['values'][-1]==1 and r['H'][-1]==-2;sharp.append(r)
count=[]
for Y in[0,1,2,3,4,5,6,7,10,17,50]:
 n=Y+2;x=2*Y+2;m=Y//3;seed={0,x}|{Y-3*j for j in range(m+1)};r=run(n-1,x,seed,2*m+1);assert r['signs']=='AS'*m+'A';assert[r['events'][2*j]['candidate']for j in range(m+1)]==[Y-3*j for j in range(m+1)];count.append(r)
oldseen={251,10,130,373,496,620,745,871,998,1126,1255,151,0};oldseen.add(131);r=run(120,131,oldseen,24);assert r['events'][0]['candidate']==r['events'][21]['candidate']==10 and r['H'][21]==1
reg=[run(0,0,{0},500),r,run(10,100,{0,100,77,88},100),run(200,1000,{0,1000,799,800,998},100)]
Path(sys.argv[1]).write_text(json.dumps({'sharp_threshold':sharp,'sharp_count':count,'regressions':reg,'scope':'PAPER theorem controls; canonical prefix/old sqrt6 seed are old histories, not fresh holdout'},indent=2)+'\n')
print(json.dumps({'sharp_threshold_n':[2,3,17,29],'sharp_count_Y':[0,1,2,3,4,5,6,7,10,17,50],'old_sqrt6_control':{'candidate':10,'uses':[0,21],'H':[0,r['H'][21]]},'regression_steps':sum(len(z['events'])for z in reg),'all_predicates_pass':True}))
