import itertools,json,sys,time
from pathlib import Path
P=Path(__file__).resolve().parent
split=sys.argv[1]; assert split in ('discovery','holdout')
lengths=range(10) if split=='discovery' else [10]
start=time.process_time(); words=checks=comparisons=0; bad={}

def table(w):
 H=[0];B=[0];A=[0]
 for x in w:
  H.append(H[-1]+(1 if x=='A' else -1)); B.append(B[-1]+H[-1]); A.append(A[-1]+(x=='A'))
 return H,B,A

def src(H,B,q):
 return [u for u in range(q) if H[q]==H[u]+1 and B[q]-B[u]==(q-u)*H[u]]

for n in lengths:
 for bits in itertools.product('SA',repeat=n):
  w=''.join(bits);words+=1;H,B,A=table(w);cache={}
  for q in range(n+1):
   ss=src(H,B,q)
   for v in range(q+1):
    p=A[v]
    for b in range(4):
     if H[q]>H[v]+b+1:
      for u in ss:
       if u<v and v-u>2*p+b and 'height_omitted' not in bad:
        bad['height_omitted']=dict(word=w,u=u,v=v,q=q,p=p,b=b,sources=ss)
      continue
     checks+=1;s=max(0,v-2*p-b)
     for u in ss:
      assert u>=s
      if u<v:
       assert v-u<=2*p+b
       for name,bound in [('coefficient_one',p+b),('radius_minus_one',2*p+b-1)]:
        if v-u>bound and name not in bad:bad[name]=dict(word=w,u=u,v=v,q=q,p=p,b=b,sources=ss)
     key=(s,q)
     if key not in cache:
      HH,BB,_=table(w[s:q]);cache[key]=[s+u for u in src(HH,BB,q-s)]
     assert ss==cache[key];comparisons+=1
  if time.process_time()-start>2.5:raise RuntimeError('cooperative2.5CPU cap')
out=dict(split=split,words=words,eligible_conditions=checks,all_source_comparisons=comparisons,
         invalid_variant_counters=bad,cpu_seconds=time.process_time()-start,evidence='COMPUTED; no proof from finite absence')
(P/('old-source-radius-'+split+'-summary.json')).write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out),flush=True)
