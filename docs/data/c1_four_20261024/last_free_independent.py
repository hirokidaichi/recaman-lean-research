"""Independent all-lag mass/moment witness check and iterative longest-path accounting."""
from pathlib import Path
import hashlib,json,resource,time
resource.setrlimit(resource.RLIMIT_CPU,(8,9))
base=Path(__file__).parent;start=time.monotonic()
query=json.loads((base/'last-free-result.json').read_text());data=json.loads((base/'macro-certificate.json').read_text());rows=data['rows']
rank={}
for i in sorted((i for i,r in enumerate(rows) if r['state'][3]==4),key=lambda i:rows[i]['state'][1],reverse=True):
 rank[i]=max([1+rank[t] for t in rows[i]['edges'] if t is not None]+[0])
maximum=max([rank[t] for r in rows if r['state'][3]==3 for t in r['edges'] if t is not None and rows[t]['state'][3]==4]+[0])
assert maximum==query['max_model_suffix']
def end(word,b):
 if word[b]!='A':return False
 m=v=0
 for k,c in enumerate(reversed(word[:b]),1):
  sign=1 if c=='A' else -1;m+=sign;v+=k*sign
  if m==1 and v==0:return True
 return False
verified=[]
for q in query['actual']:
 word=q['prefix']+q['tail'];tags=[end(word,b) for b in range(len(word))]
 d=0;free=[];ds=[]
 for k,c in enumerate(word):
  d+=(c=='S')-tags[k];ds.append(d)
  if k>=len(q['prefix']) and c=='A' and not tags[k]:free.append(k)
 assert ds[len(q['prefix'])-1]==0 and min(ds)>=0 and min(ds[len(q['prefix']):])>=1
 assert len(free)==4
 after=sum(c=='A' for c in word[free[-1]+1:]);assert after==q['A_after_last_free']>2
 assert [tags[len(q['prefix'])+k] for k,c in enumerate(q['tail']) if c=='A']==q['actual_tags']
 verified.append(dict(prefix=q['prefix'],tail=q['tail'],A_after_last_free=after,prefix_nonnegative=True,tail_positive=True))
result=dict(all_actual_witnesses_verified=True,actual_pairs=len(verified),max_model_suffix=maximum,
 max_actual_suffix=max(v['A_after_last_free'] for v in verified),holdout_candidates=0 if len(query['candidates'])<=32 else len(query['candidates'])-32,
 note='Only26 candidates existed under the frozen rule, so no holdout shard was populated. Exact reverse-moment verification refutes the auxiliary; no unseen-range generalization is claimed.',
 verified=verified,elapsed_seconds=time.monotonic()-start,source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
(base/'last-free-independent.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='verified'}))
