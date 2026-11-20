"""New generic optimum seed predicate and new all-N reuse-family controls."""
import itertools,json,sys,hashlib
from pathlib import Path
cfg=json.loads(Path(sys.argv[1]).read_text())
def ledger(w):
 H=[0];B=[0];states={(0,0):[0]};Akeys={};free=[];col=[]
 for q,c in enumerate(w):
  h=H[-1];area=B[-1]
  if c=='A':
   key=(h-1,area-q*(h-1))
   if key not in states:free.append(q)
   Akeys.setdefault(key,[]).append(q)
  nh=h+(1 if c=='A'else-1);nb=area+nh;v=q+1;key=(nh,nb-v*nh)
  if c=='S':col += [('I',u,v)for u in states.get(key,[])]+[('II',u,v)for u in Akeys.get(key,[])]
  states.setdefault(key,[]).append(v);H.append(nh);B.append(nb)
 C={q:(H[q]-1,(q+1)*(H[q]-1)-B[q])for q in free}
 O=[(H[u],(u+1)*H[u]-B[u])for u in range(len(w)+1)]
 return H,B,free,C,O,col
def replay(w,b,x,V):
 cur=x;seen=set(V)
 for q,c in enumerate(w):
  n=b+q+1;A=cur-n<=0 or cur-n in seen
  if A!=(c=='A'):return q
  cur=cur+n if A else cur-n;seen.add(cur)
  assert cur>0
 return None
short=[];count=removals=sharing=0
for n in cfg['discovery_lengths']+cfg['parameter_control_lengths']:
 for chars in itertools.product('AS',repeat=n):
  w=''.join(chars);H,B,free,C,O,col=ledger(w)
  if col:continue
  aff=sorted(set(O+list(C.values())));E=set()
  for i,(h,k)in enumerate(aff):
   for hh,kk in aff[:i]:
    if h!=hh:
     b,r=divmod(kk-k,h-hh)
     if r==0 and b>=0:E.add(b)
  b0=0
  while b0 in E:b0+=1
  bases=sorted({b0,max(E,default=0)+1})
  K=len(set(C.values()));sharing+=K<len(free)
  for b in bases:
   x=1-min(b*h+k for h,k in aff)
   vals={x+b*h+k for h,k in C.values()};V={x}|vals
   assert len(V)==K+1 and replay(w,b,x,V)is None
   for value in vals:
    q=min(q for q,pair in C.items()if x+b*pair[0]+pair[1]==value)
    assert replay(w,b,x,V-{value})==q;removals+=1
   count+=1
  short.append(dict(word=w,free=len(free),classes=K,exceptional_bases=sorted(E),generic_bases=bases))
family=[]
for N in cfg['reuse_N']:
 ss=[1];L=8
 for j in range(1,N):ss.append(4*(L+1));L+=4*ss[-1]+4
 P=ss[-1]+3;h=L//2+2;a=h+P
 w='S'*h+'A'*a;selected=[]
 for s in ss:selected.append(len(w));w+='A'*s+'S'*(2*s+2)+'A'*(s+2)
 selected.append(len(w));w+='A'
 H,B,free,C,O,col=ledger(w);assert not col
 assert all(q in C for q in selected)and len({C[q]for q in selected})==1
 Ecount=S=0;free_set=set(free)
 for q,c in enumerate(w):
  if c=='S':S+=1
  elif q not in free_set:Ecount+=1
  assert S-Ecount>=1
 n=len(w)+1;b=100*n*n;x=100*(b+n)*n
 vals={x+b*t+k for t,k in C.values()};V={0,x}|vals
 assert len(V)==len(set(C.values()))+2
 assert replay(w,b,x,V)is None
 pair=C[selected[0]];value=x+b*pair[0]+pair[1]
 assert all(x+b*pair[0]+pair[1]==value for q in selected)
 assert all(x+b*t+k!=value for t,k in O)
 family.append(dict(N=N,s_values=ss,cycle_length=L,h=h,a=a,P=P,total_length=len(w),selected_original_free=selected,same_affine_candidate=list(pair),shared_seed_blocker=value,actual_replay_steps=len(w),original_free=len(free),distinct_free_candidate_classes=len(set(C.values())),base=b,current=x,seed=sorted(V),word_sha256=hashlib.sha256(w.encode()).hexdigest()))
out=dict(PASS=True,coherent_short_words=len(short),generic_realizations=count,necessary_blocker_removals=removals,short_words_with_candidate_sharing=sharing,short_word_certificates=short,reuse_family=family,scope='All short controls NEW generic-minimum predicate and new N1/2/3 reuse construction; all-N proofs separate; no canonical/infinite orbit')
Path(sys.argv[2]).write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(PASS=True,coherent_short_words=len(short),generic_realizations=count,necessary_blocker_removals=removals,short_words_with_candidate_sharing=sharing,reuse=[{k:r[k]for k in ['N','total_length','selected_original_free','original_free','distinct_free_candidate_classes','shared_seed_blocker']}for r in family])))
