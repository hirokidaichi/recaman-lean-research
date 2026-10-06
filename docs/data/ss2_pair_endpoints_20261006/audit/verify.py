import json,sys,hashlib
from pathlib import Path
root=Path(sys.argv[1]); base=root/'docs/data/ss2_pair_endpoints_20261006'
rows=[json.loads(x) for f in ['discovery.jsonl','holdout.jsonl'] for x in (base/f).read_text().splitlines()]
pairs={(r['p'],r['mask'],*(q['phase'] for q in r['donors'])):r for r in rows if r['kind']=='pair'}
summaries={r['p']:r for r in rows if r['kind']=='summary'}
seen=set(); pseen=set()
for line in Path('/tmp/ss2-pair-next-audit-20261006/independent.out').read_text().splitlines():
 tag,*parts=line.split();v=list(map(int,parts))
 if tag=='pair':
  p,m,a,b,E,nb,free,n,wit=v;key=(p,m,a,b);r=pairs[key];seen.add(key)
  assert (E,nb,free,n,wit)==(r['endpoint_mask'],r['donor_union_mask'],r['uncovered_mask'],r['uncovered_count'],len(r['all_lowSS_Sended_witnesses']))
 else:
  p,reps,weighted,low,two,wrap,mg,np,unused,unused2=v;pseen.add(p)
  assert reps==summaries[p]['representatives'] and np==summaries[p]['pairs']
assert seen==set(pairs) and pseen==set(range(1,23))
# Independent p33 exact control, no new census range.
period='SASASSSAAAASASASASASASASASASASAAA';p=len(period)
assert p==33 and period.count('A')-period.count('S')==3
assert all(''.join(period[(t+j)%p] for j in range(4))!='SAAS' for t in range(p))
results=[]
for t,d in [(10,11),(31,31)]:
 assert period[t]=='A';w=''.join(period[(t-j)%p] for j in range(1,d+1))
 m=M=0;hits=[]
 for j,x in enumerate(w,1):
  a=1 if x=='A' else -1;m+=a;M+=j*a
  if m==1 and M==0:hits.append(j)
 ss=sum(x==y=='S' for x,y in zip(w,w[1:]));old=max(j for j,x in enumerate(w,1) if x=='S')
 assert hits==[d] and ss==2 and (t-old)%p==0
 results.append({'phase':t,'lag':d,'word':w,'P2_prefixes':hits,'SS':ss,'oldest_offset':old})
assert period[32]=='A' and ''.join(period[(32-j)%p] for j in [1,2,3])=='AAS'
print(json.dumps({'status':'PASS','period_summaries':22,'all_pair_endpoint_sets':len(seen),'minimum_uncovered':min(r['uncovered_count'] for r in pairs.values()),'NoSAAS_pairs_p1_22':sum(r['nosaas'] for r in pairs.values()),'p33':{'period':period,'mass':3,'cyclic_NoSAAS':True,'donors':results,'distinct_clean_source':32}},indent=2))
