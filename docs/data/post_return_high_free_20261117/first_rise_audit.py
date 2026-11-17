import json
from pathlib import Path
P=Path(__file__).resolve().parent

def evaluate(w):
 H=[0];B=[0];sources={};free=[]
 for x in w:H.append(H[-1]+(1 if x=='A' else -1));B.append(B[-1]+H[-1])
 for q,x in enumerate(w):
  if x!='A':continue
  ss=[u for u in range(q) if H[q]==H[u]+1 and B[q]-B[u]-(q-u)*H[u]==0]
  sources[q]=ss
  if not ss:free.append(q)
 return H,B,sources,free

forest=json.loads((P/'first-rise-forest.json').read_text());roots=forest['roots'];nodes=forest['nodes'];root_ids=forest['root_ids']
assert len(roots)==len(root_ids)==49
seen=set();todo=list(root_ids);edges=0;maxheight=0
for r,i in enumerate(root_ids):assert nodes[i]['root']==r and nodes[i]['tail']==''
while todo:
 i=todo.pop();assert i not in seen;seen.add(i);n=nodes[i];root=roots[n['root']];w=root['word']+n['tail']
 H,B,src,free=evaluate(w+'A');q=len(w)
 assert H[q]+8==n['height'] and len([u for u in free if u<q])==n['free']
 assert src[q]==n['A_sources']
 allowed={}
 for x in 'SA':
  hh=n['height']+(1 if x=='A' else -1);ff=n['free']+int(x=='A' and not src[q])
  if hh<=0 or ff>4:continue
  assert hh<7,(i,x)
  allowed[x]=(hh,ff)
 assert set(allowed)==set(n['children']),i
 for x,(hh,ff) in allowed.items():
  j=n['children'][x];assert isinstance(j,int) and 0<=j<len(nodes)
  child=nodes[j];assert child['root']==n['root'] and child['tail']==n['tail']+x and child['height']==hh and child['free']==ff
  edges+=1;maxheight=max(maxheight,hh);todo.append(j)
assert len(seen)==len(nodes)

cases=[(1,x,None) for x in [0,1,5,6,7,13]]+[(2,x,y) for x,y in [(0,0),(1,2),(5,6),(6,2),(9,2),(9,7),(13,14)]]+[(3,x,None) for x in [0,1,5,6,9,17]]
tails=['AAASAAAA','AAAASA','AASAAASAAA'];profile_rows=[];compared=0
for p,x,y in cases:
 L=max(8,x+4);xx=min(x,6);yy=min(y,6) if y is not None else None
 if p==1:old='S'*(L-x)+'A'+'S'*(x+1)
 elif p==2:old='S'*(L-x)+'A'+'S'*(x+1-y)+'A'+'S'*(y+1)
 else:old='S'*(L-x)+'AAA'+'S'*(x+3)
 root=next(r for r in roots if r['p']==p and r['x']==xx and r['y']==yy);can=root['word']
 for tail in tails:
  H,B,src,ff=evaluate(old+tail);HH,BB,ss,FFF=evaluate(can+tail)
  checked=[]
  for k,z in enumerate(tail):
   height=H[len(old)+k]+L
   if height<0 or height>7:break
   if z!='A' or height>6:continue
   lhs=[u-len(old) for u in src[len(old)+k]];rhs=[u-len(can) for u in ss[len(can)+k]]
   assert lhs==rhs,(p,x,y,tail,k,lhs,rhs)
   compared+=1;checked.append({'tail_clock':k,'height':height,'relative_all_sources':lhs})
  profile_rows.append({'p':p,'x':x,'y':y,'old_word':old,'canonical_word':can,'tail':tail,'checked':checked})
(P/'first-rise-profile-certificates.json').write_text(json.dumps(profile_rows,indent=2)+'\n')
out={'result':'PASS','roots':49,'nodes':len(nodes),'edges':edges,'all_nodes_reachable':True,'max_future_height':maxheight,'no_valid_missing_edge':True,'profile_cases':len(cases),'profile_all_source_comparisons':compared,'evidence':'COMPUTED independent forward-area verification; not a Lean theorem or an unbounded profile proof'}
(P/'first-rise-audit-summary.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
