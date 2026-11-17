import itertools,json,time
from pathlib import Path
from functools import lru_cache
P=Path(__file__).resolve().parent;start=time.process_time()

def walk(w,initial=0):
 H=[initial];B=[0]
 for x in w:H.append(H[-1]+(1 if x=='A' else -1));B.append(B[-1]+H[-1])
 return H,B

def sources(w):
 H,B=walk(w);q=len(w)
 return [u for u in range(q) if H[q]==H[u]+1 and B[q]-B[u]==(q-u)*H[u]]

@lru_cache(None)
def bridge_areas(j,r):
 ans=set();n=2*r+j
 for aa in itertools.combinations(range(n),r):
  aset=set(aa);w=''.join('A' if t in aset else 'S' for t in range(n));H,B=walk(w,j)
  if min(H)<0:continue
  assert H[-1]==0
  C=B[-1]-j*n;ax=sum(H[t] for t in aa);tri=j*(j+1)//2
  assert C==-tri+r*(1-2*j)+2*ax
  assert -tri+r*(1-2*j)<=C<=r*r-tri and (C-r+tri)%2==0
  ans.add(C)
 return frozenset(ans)

def permitted(p,j):
 if j<0:return set()
 if p<=2:return set().union(*(bridge_areas(j,r) for r in range(p+1)))
 ws=['S'*j]
 if j>=2:ws.append('A'+'S'*(j+1))
 if j>=1:ws.append('AA'+'S'*(j+2))
 ws+=['S'*s+'AAA'+'S'*(j+3-s) for s in range(j+1)]
 return {walk(w,j)[1][-1]-j*len(w) for w in ws}

counts={}
for split,js,rs in [('discovery',range(4),range(3)),('holdout',range(4,7),range(4))]:
 pairs=vals=0
 for j in js:
  for r in rs:vals+=len(bridge_areas(j,r));pairs+=1
 counts[split]=dict(parameter_pairs=pairs,distinct_bridge_areas=vals)

old=json.loads((P/'first-rise-forest.json').read_text());checked=0
for row in old['nodes']:
 root=old['roots'][row['root']];w=root['word'];v=len(w);full=w+row['tail'];H,B=walk(full);q=len(full)
 for u in sources(full):
  if u>=v:continue
  j=H[u]-H[v];C=B[v]-B[u]-(v-u)*H[u]
  assert C in permitted(root['p'],j)
  assert C==(H[q]-H[v]-1)*(q-v)-(B[q]-B[v]-(q-v)*H[v])
  checked+=1

forest=json.loads((P/'old-area-spectrum-forest.json').read_text());nodes=forest['nodes'];reach=set(forest['root_ids'])
assert len(forest['root_ids'])==4
for p,i in enumerate(forest['root_ids']):
 n=nodes[i];assert (n['p'],n['tail'],n['height'],n['paid'])==(p,'',0,(0,1,2,2)[p])
for i,n in enumerate(nodes):
 assert i in reach
 w=n['tail'];H,B=walk(w);h=H[-1];p=n['p'];a=n['paid'];j=h-1;C=j*len(w)-B[-1]
 assert (n['height'],n['area'])==(h,B[-1]) and h<7
 ss=sources(w);oo=C in permitted(p,j)
 assert n['local_sources']==ss and n['old_allowed']==oo
 for x in 'SA':
  hh=h+(1 if x=='A' else -1);aa=a+(x=='A' and not (ss or oo));valid=hh>0 and aa<=4
  assert valid==(x in n['children'])
  if valid:
   assert hh<7
   k=n['children'][x];ch=nodes[k];assert(ch['tail'],ch['p'],ch['height'],ch['paid'])==(w+x,p,hh,aa);reach.add(k)
assert len(reach)==len(nodes)
out=dict(result='PASS',bridge_ranges=counts,original_old_sources_admitted=checked,relaxed_nodes_verified=len(nodes),
         all_branches_checked=True,cpu_seconds=time.process_time()-start,evidence='COMPUTED independent forward/spectrum audit, not a proof by finite absence')
(P/'old-area-spectrum-audit-summary.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
