from pathlib import Path
import itertools,json,sys,time,hashlib
OUT=Path(__file__).resolve().parent

def forward(w):
 H=[0];B=[0];bank={};src=[];free=[];S=E=0;positive=True
 for q,c in enumerate(w):
  ss=list(bank.get((H[q]-1,B[q]-q*(H[q]-1)),[])) if c=='A' else []
  src.append(ss)
  if c=='A':
   E+=bool(ss)
   if not ss:free.append(q)
  else:S+=1
  positive=positive and S-E>=1
  bank.setdefault((H[q],B[q]-q*H[q]),[]).append(q)
  H.append(H[-1]+(1 if c=='A' else -1));B.append(B[-1]+H[-1])
 return H,B,src,free,positive

def reverse(w,q):
 mass=area=0;out=[]
 for k,c in enumerate(reversed(w[:q]),1):
  mass+=1 if c=='A' else -1;area+=k*(1 if c=='A' else -1)
  if mass==1 and area==0:out.append(q-k)
 return sorted(out) if w[q]=='A' else []

mode=sys.argv[1];lengths=range(1,13) if mode=='discovery' else [15,16]
start=time.process_time();checked=eligible=tests=0;counter=None
for n in lengths:
 for tail in itertools.product('SA',repeat=n-1):
  w='S'+''.join(tail);checked+=1
  H,B,src,free,positive=forward(w)
  if not positive:continue
  eligible+=1;visits={}
  for h in H[:-1]:visits[h]=visits.get(h,0)+1
  for l,left in sorted(visits.items()):
   if H[-1]<=l:continue
   tests+=1;wallet=[q for q in free if l-2<H[q]<=l]
   lower=[q for q in range(n) if H[q]==l-2]
   if left>len(lower)+len(wallet):
    for q,c in enumerate(w):
     if c=='A':assert src[q]==reverse(w,q)
    counter={'word':w,'T':n,'l':l,'H':H,'B':B,'source_sets':src,'free':free,'visits':[q for q in range(n) if H[q]==l],'lower_visits':lower,'band_free':wallet,'lhs':left,'rhs':len(lower)+len(wallet),'all_A_reverse_checked':True,'word_sha256':hashlib.sha256(w.encode()).hexdigest()};break
  if counter:break
 if counter:break
result={'mode':mode,'frozen_lengths':list(lengths),'checked':checked,'eligible':eligible,'tests':tests,'counter':counter,'complete_frozen_range':counter is None,'stop':'first_counter' if counter else 'frozen_range_complete','cpu_seconds':time.process_time()-start}
(OUT/('two-level-'+mode+'-summary.json')).write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
