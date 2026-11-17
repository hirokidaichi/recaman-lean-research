import gzip,hashlib,json,sys,time
from pathlib import Path
from collections import defaultdict
P=Path(__file__).resolve().parent;start=time.process_time();m=int(sys.argv[1]);assert m in (6,8)
word='S'*(m+1)+'A'*(2*m+2)+'S'*m
for i in range(1,m):word='AS'*len(word)+'S'+word+'A'
q=len(word);assert q==(4*m+4)*3**(m-1)-1
h=(word+'A').count('A')+1;R=h+q-(2*m-1);T=h+q+1
w='S'*h+word+'A';assert len(w)==T
H=[0];B=[0];idx=defaultdict(list);sources={};free=[];E=S=0
for t,x in enumerate(w):
 if x=='A':
  ss=list(idx[(H[t]-1,B[t]-t*(H[t]-1))]);sources[str(t)]=ss
  if ss:E+=1
  else:free.append(t)
 else:S+=1
 assert E+1<=S
 idx[(H[t],B[t]-t*H[t])].append(t)
 H.append(H[-1]+(1 if x=='A' else -1));B.append(B[-1]+H[-1])
 if t%4096==0 and time.process_time()-start>2.5:raise RuntimeError('cooperative2.5CPU cap')
d=2-h;mn=min(H);v=max(i for i,x in enumerate(H) if x==mn)
assert H[R]==H[T]==d and mn==-h-2*m
assert next(i for i in range(v+1,T+1) if H[i]==d)==R
assert w[R:T]=='S'*m+'A'*m and all(sources[str(i)] for i in range(R+m,T))
assert not [i for i in free if R<=i<T]
keys=[]
for e in (3,4):
 u=R+e;c=d-e;off=B[u]-c*u-(B[T]-c*T)
 assert H[u]==c and off==(m-e)**2-e*(e+1)//2
 keys.append(dict(e=e,u=u,c=c,offset=off))
out=dict(m=m,h=h,R=R,T=T,d=d,v=v,min_height=mn,word_sha256=hashlib.sha256(w.encode()).hexdigest(),
         prefix_positive=True,first_return_R=True,all_A_count=len(sources),all_actual_count=E,all_free_count=len(free),
         low_free_before_R=sum(H[i]<d for i in free if i<R),free_after_R=0,keys=keys,
         tail_sources={str(i):sources[str(i)] for i in range(R+m,T)},cpu_seconds=time.process_time()-start,
         evidence='COMPUTED original G0 counter; low4 parent NOT refuted')
assert out['low_free_before_R']>4
with gzip.open(P/f'g0-m{m}-full.json.gz','wt') as fp:json.dump(dict(word=w,H=H,B=B,all_sources=sources,all_free=free,summary=out),fp)
(P/f'g0-m{m}-summary.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out),flush=True)
