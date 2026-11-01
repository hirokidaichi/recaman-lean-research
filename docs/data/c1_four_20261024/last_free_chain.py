"""Frozen zero-free suffix query on an existing graph, with actual all-start realization checks."""
from functools import lru_cache
from pathlib import Path
import datetime,hashlib,json,resource,time
resource.setrlimit(resource.RLIMIT_CPU,(8,9))
base=Path(__file__).parent;start=time.monotonic()
data=json.loads((base/'macro-certificate.json').read_text());rows=data['rows']
@lru_cache(None)
def dp(i):
 if time.monotonic()-start>10:raise TimeoutError('wall guard')
 best=[]
 for edge,t in enumerate(rows[i]['edges']):
  if t is None or rows[t]['state'][3]!=4:continue
  assert rows[t]['state'][1]==rows[i]['state'][1]+1
  path=[(edge,t)]+dp(t)
  if len(path)>len(best):best=path
 return best
parent={0:None}
for i,row in enumerate(rows):
 for edge,t in enumerate(row['edges']):
  if t is not None and t not in parent:parent[t]=(i,edge)
def rootpath(i):
 ans=[]
 while i:
  old,edge=parent[i];ans.append((edge,i));i=old
 return list(reversed(ans))
def ledger(word):
 F=[0];G=[0];tags=[];sup=[]
 for b,c in enumerate(word):
  witnesses=[]
  if c=='A':
   witnesses=[t for t in range(b) if F[b]-F[t]==1 and G[b]-G[t]-(b-t)*F[t]==0]
  tags.append(c=='A' and bool(witnesses));sup.append(witnesses)
  F.append(F[-1]+(1 if c=='A' else -1));G.append(G[-1]+F[-1])
 return tags,sup
candidates=[];maximum=0
for i,row in enumerate(rows):
 if row['state'][3]!=3:continue
 for edge,t in enumerate(row['edges']):
  if t is not None and row['state'][3]==3 and rows[t]['state'][3]==4:
   k=len(dp(t));maximum=max(maximum,k)
   if k>2 and len(candidates)<64:
    path=rootpath(i)+[(edge,t)]+dp(t)
    tail=''.join('S'*(e//2)+'A' for e,node in path);expected=[bool(e%2) for e,node in path]
    candidates.append(dict(source=i,edge=edge,target=t,supplied_after_last_free=k,path=path,tail=tail,expected_tags=expected))
prefixes=['ASAAA','AASAAA','SAAASAAA','SSAAAASAAA'];actual=[]
for ordinal,cand in enumerate(candidates):
 for p in prefixes:
  tags,sup=ledger(p+cand['tail']);d=0;prefix_d=None;free=0;last_free=None;tailds=[]
  for k,c in enumerate(p+cand['tail']):
   d+=(c=='S')-tags[k]
   if k==len(p)-1:prefix_d=d
   if k>=len(p):
    tailds.append(d)
    if c=='A' and not tags[k]:free+=1;last_free=k
  actual_tags=[tags[len(p)+k] for k,c in enumerate(cand['tail']) if c=='A']
  after=sum(c=='A' for c in (p+cand['tail'])[last_free+1:]) if last_free is not None else 0
  if prefix_d==0 and min(tailds)>0 and free==4 and after>2 and actual_tags==cand['expected_tags']:
   actual.append(dict(ordinal=ordinal,range='discovery' if ordinal<32 else 'holdout',prefix=p,tail=cand['tail'],free=free,A_after_last_free=after,final_deficit=d,min_tail_deficit=min(tailds),suppliers=sup,actual_tags=actual_tags))
result=dict(max_model_suffix=maximum,candidates=candidates,actual=actual,graph_kernel_verified=False,
 elapsed_seconds=time.monotonic()-start,source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
(base/'last-free-result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(max_model_suffix=maximum,candidates=len(candidates),actual=len(actual),first=actual[:1],elapsed_seconds=result['elapsed_seconds'])))
