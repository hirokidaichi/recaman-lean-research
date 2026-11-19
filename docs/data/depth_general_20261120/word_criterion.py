from pathlib import Path
import itertools,json,sys
def test(w):
 Q=len(w);H=[0];B=[0]
 for ch in w:H.append(H[-1]+(1 if ch=='A'else-1));B.append(B[-1]+H[-1])
 badI=[];badII=[]
 for v in range(1,Q+1):
  if w[v-1]!='S':continue
  for u in range(v):
   if H[u]==H[v] and B[v]-B[u]==(v-u)*H[v]:badI.append([u,v])
  for q in range(v):
   if w[q]=='A'and H[q]-1==H[v] and B[v]-B[q]==(v-q)*H[v]:badII.append([q,v])
 valid=not badI and not badII
 src=[[]for _ in w]
 for q,ch in enumerate(w):
  if ch=='A':src[q]=[u for u in range(q)if H[q]==H[u]+1 and B[q]-B[u]==(q-u)*H[u]]
 n=Q+1;b=100*n*n;x=100*(b+n)*n;X=[x+(b+i+1)*H[i]-B[i]for i in range(Q+1)]
 C=[X[q]-(b+q+1)for q in range(Q)];free=[q for q in range(Q)if w[q]=='A'and not src[q]]
 seed={0,x}|{C[q]for q in free};seen=set(seed);cur=x;got='';fail=None
 for q,ch in enumerate(w):
  candidate=cur-(b+q+1);sgn='S'if candidate>0 and candidate not in seen else'A';got+=sgn
  if sgn!=ch:fail=q;break
  cur=candidate if sgn=='S'else cur+b+q+1;seen.add(cur)
 assert valid==(fail is None),(w,badI,badII,got,fail)
 if valid:assert cur==X[-1]and len(seed)<=len(free)+2 and min(X+C)>0 if Q else cur==x
 return {'word':w,'valid':valid,'badI':badI,'badII':badII,'got':got,'seed_size':len(seed),'F':len(free),'clock':b,'current':x}
rows=[]
for Q in range(8):
 for bits in itertools.product('SA',repeat=Q):rows.append(test(''.join(bits)))
for w in ['SAAS','ASSSSAAAS','SSAAASSSSAAAASAS','SSAAASSSSAAAASASA','SS'+'A'*30+'SSAAASSSSAAAASAS'*2+'S'*9+'A']:rows.append(test(w))
cur=100;seen={77,88};got='';vals=[cur]
for q in range(4):
 c=cur-(11+q);sgn='S'if c>0 and c not in seen else'A';got+=sgn;cur=c if sgn=='S'else cur+11+q;seen.add(cur);vals.append(cur)
assert got=='SAAS' and vals==[100,89,101,114,100]
Path(sys.argv[1]).write_text(json.dumps({'controls':rows,'incoherent_v0_counter':{'clock':10,'current':100,'seen':[77,88],'word':got,'values':vals},'scope':'finite discovery controls only, not all words or fresh holdout'},indent=2)+'\n')
print(json.dumps({'controls':len(rows),'valid':sum(r['valid']for r in rows),'invalid':sum(not r['valid']for r in rows),'specials':rows[-5:],'v0_values':vals}))
