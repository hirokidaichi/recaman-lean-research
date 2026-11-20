import itertools, json, sys
from pathlib import Path

cfg=json.loads(Path(sys.argv[1]).read_text())
def hb(w):
 H=[0]; B=[0]
 for c in w:
  H.append(H[-1]+(1 if c=='A' else -1)); B.append(B[-1]+H[-1])
 return H,B
def valleys(length,area):
 out=[]
 for aa in itertools.combinations(range(length),length//2):
  a=set(aa);w=''.join('A' if i in a else 'S' for i in range(length));H,B=hb(w)
  if H[-1]==0 and max(H[1:-1])<0 and B[-1]==-area:out.append(w)
 return out
def audit(w):
 H,B=hb(w); sources={}; rev={}; free=[]; actual=0; S=0; positive=True
 for p,c in enumerate(w):
  if c=='A':
   src=[u for u in range(p) if H[p]==H[u]+1 and B[p]-B[u]==(p-u)*H[u]]
   mass=area=0;other=[]
   for u in range(p-1,-1,-1):
    mass+=1 if w[u]=='A' else -1;area+=(p-u)*(1 if w[u]=='A' else -1)
    if mass==1 and area==0:other.append(u)
   assert src==sorted(other)
   sources[p]=src
   if src:actual+=1
   else:free.append(p)
  else:S+=1
  positive &= S>=actual+1
 collisions=[]
 for v in range(1,len(w)+1):
  if w[v-1]!='S':continue
  for u in range(v):
   if H[u]==H[v] and B[v]-B[u]==(v-u)*H[v]:collisions.append(['I',u,v])
  for q in range(v):
   if w[q]=='A' and H[q]-1==H[v] and B[v]-B[q]==(v-q)*H[v]:collisions.append(['II',q,v])
 return {'word':w,'H':H,'B':B,'sources':sources,'free':free,'positive':bool(positive),'collisions':collisions}
first=valleys(12,18);second=valleys(10,17);rows=[];counters=[]
for v1 in first:
 for v2 in second:
  J='S'+'A'*7+'S'*3+'AS'*9+'S'*6
  w='SS'+'AS'+J+v1+'A'+v2+'AAA'+'ASSSSAAA'+'A'
  r=audit(w);p=65;q=73;u=2
  assert len(w)==74 and r['H'][-1]==0
  assert u in r['sources'][p] and u in r['sources'][q]
  middle_low=[k for k in r['free'] if p<k<q and r['H'][k]<=-1]
  rows.append({'v1':v1,'v2':v2,'positive':r['positive'],'middle_low_free':middle_low,'collision_count':len(r['collisions']),'first_collisions':r['collisions'][:4]})
  if r['positive'] and not middle_low and not r['collisions']:
   n=len(w)+1;b=100*n*n;x=100*(b+n)*n
   seed={0,x}|{x+(b+k+1)*(r['H'][k]-1)-r['B'][k] for k in r['free']}
   seen=set(seed);cur=x
   for k,c in enumerate(w):
    clock=b+k+1;cand=cur-clock;A=cand<=0 or cand in seen
    assert A==(c=='A');cur=cur+clock if A else cand;seen.add(cur)
   r.update(base=b,current=x,seed=sorted(seed),u=u,p=p,q=q,h=2,T=74,middle_low_free=middle_low);counters.append(r)
out={'first_valley_count':len(first),'second_valley_count':len(second),'pairs':rows,'counterexamples':counters,'scope':'Frozen new chronology predicate on a NEW compact two-source reservoir class; not old E715/table rerun, no absence theorem beyond this finite class'}
Path(sys.argv[2]).write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'pairs':len(rows),'chronological_counter_count':len(counters),'first_valleys':len(first),'second_valleys':len(second),'failures_by_collision':sum(bool(x['collision_count']) for x in rows),'output':sys.argv[2]}))
