import json,sys
from pathlib import Path
P=Path(__file__).resolve().parent
rows=[]
for fname,tags in [('ACTIVATION_DISCOVERY.json',None),('ACTIVATION_LINEAR.json',None)]:
 for old in json.loads((P/fname).read_text())['rows']:
  w=old['f']['word'];H=old['f']['H'];B=old['f']['B'];Q=len(w);b=100*(Q+1)**2;x=100*(b+Q+1)*(Q+1)
  X=[x+(b+i+1)*H[i]-B[i] for i in range(Q+1)]
  C=[X[i]-(b+i+1)for i in range(Q)]
  free=old['f']['free'];initial={x}|{C[i]for i in free};seen=set(initial);cur=x;steps=[]
  for i,ch in enumerate(w):
   assert cur==X[i]
   c=cur-(b+i+1);takeS=c>0 and c not in seen;actual='S'if takeS else'A'
   if actual!=ch:
    print(json.dumps({'FAILED':True,'tag':old['tag'],'i':i,'expected':ch,'actual':actual,'candidate':c,'seed_matches':[q for q in free if C[q]==c],'prior_value_matches':[q for q in range(i+1)if X[q]==c]}));raise SystemExit(2)
   cur=c if takeS else cur+(b+i+1);seen.add(cur);steps.append({'i':i,'sign':actual,'value':cur,'candidate':c,'new_subtraction':takeS})
  assert cur==X[-1]
  rows.append({'tag':old['tag'],'Q':Q,'clock':b,'current':x,'initial_stock_size':len(initial),'initial_stock':sorted(initial),'steps':steps,'status':'greedy all signs reproduced; canonical prehistory NOT supplied','source_scope':'raw original EndN/free determines which positive candidates require preload; actual numeric history checked independently'})
Path(sys.argv[1]).write_text(json.dumps({'rows':rows},indent=2)+'\n')
print(json.dumps([{k:v for k,v in r.items()if k not in['initial_stock','steps']}for r in rows]))
