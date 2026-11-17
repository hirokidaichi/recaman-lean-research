import json,sys,time,hashlib
from pathlib import Path
from collections import defaultdict
P=Path(__file__).resolve().parent;ROOT=P.parents[2];START=time.process_time()

def evaluate(w):
 H=[0];B=[0];idx=defaultdict(list);src={};free=[];positive=[True];E=S=0
 for q,x in enumerate(w):
  if x=='A':
   src[str(q)]=list(idx[(H[q]-1,B[q]-q*(H[q]-1))])
   if src[str(q)]:E+=1
   else:free.append(q)
  else:S+=1
  positive.append(positive[-1] and E+1<=S)
  idx[(H[q],B[q]-q*H[q])].append(q)
  H.append(H[-1]+(1 if x=='A' else -1));B.append(B[-1]+H[-1])
 return H,B,src,free,positive

mode=sys.argv[1]
if mode=='discovery':
 corpus=[('high5','SS'+'A'*5+'S'*3),('high31','S'*5+'A'*31+'S'*29),
         ('old_tail_head2','SS'+'ASAAA'+'S'*5+'A'*3+'S'*4+'A'*4+'S'+'A'*3),
         ('old_tail_head10','S'*10+'ASAAA'+'S'*5+'A'*3+'S'*4+'A'*4+'S'+'A'*3)]
 files=['deep-discovery-best-M4','deep-discovery-best-M5']
elif mode=='holdout':
 corpus=[('high13','S'*3+'A'*13+'S'*11),('high37','S'*7+'A'*37+'S'*35)];files=['deep-holdout-best-M6','deep-holdout-best-M8']
else:raise ValueError(mode)
for name in files:corpus.append((name,json.loads((ROOT/'docs/data/prehistory_cost_20261117'/f'{name}.json').read_text())['word']))
counts={'words_started':0,'positive_endpoints':0,'eligible_pairs':0,'eligible_initialS_low4_pairs':0,'useful_key_violations':0,'PC5_counter':0};counter=None
for name,w in corpus:
 counts['words_started']+=1
 H,B,src,free,pos=evaluate(w);F=set(free)
 for T in range(1,len(w)+1):
  if time.process_time()-START>3.5:raise RuntimeError('cooperative3.5CPU stop')
  if not pos[T]:continue
  counts['positive_endpoints']+=1;d=H[T];levels=(d-4,d-3);h=2-d
  low=[q for q in free if q<T and H[q]<d];initial=h>=1 and w.startswith('S'*h) and T>=h
  useful=[]
  for R in range(T-1,-1,-1):
   if R in F and H[R]<d:break
   if H[R] in levels:
    offset=B[R]-H[R]*R-(B[T]-H[R]*T)
    if offset>0:useful.append({'clock':R,'height':H[R],'key_offset':offset})
   if H[R]!=d:continue
   counts['eligible_pairs']+=1
   if initial and len(low)<=4:counts['eligible_initialS_low4_pairs']+=1
   if not useful:continue
   m=min(H[:T+1]);v=max(q for q in range(T+1) if H[q]==m)
   actualR=next((q for q in range(v+1,T+1) if H[q]==d),None)
   full=w[:T]+'ASSSSAAA'*5+'A';HH,BB,SS,FF,PP=evaluate(full)
   parent=initial and len(low)<=4 and PP[-1] and all(SS[str(q)] for q in range(T,len(full)) if full[q]=='A') and all(SS[str(T+8*j)]==[h-1] for j in range(6))
   counts['useful_key_violations']+=1;counts['PC5_counter']+=parent
   counter={'input_name':name,'full_input_word':w,'prefix_word':w[:T],'R':R,'T':T,'d':d,'h_candidate':h,'initialS':initial,'low_free':low,'H':H,'B':B,'all_original_sources':src,'all_original_free':free,'positive_through_T':pos[T],'high_free_after_R':[q for q in free if R<=q<T and H[q]>=d],'useful_late_sources':list(reversed(useful)),'min_height':m,'last_minimum':v,'actual_first_return':actualR,'R_is_actual_first_return':R==actualR,'PC5_counter':parent,'appended_word':full,'appended_sources':SS,'appended_positive':PP[-1]}
   break
  if counter:break
 if counter:break
if counter:(P/(mode+'-counter.json')).write_text(json.dumps(counter,indent=2)+'\n')
out={'mode':mode,'counts':counts,'counterexample_G0':counter is not None,'cpu_seconds':time.process_time()-START,'scope':'COMPUTED exact corpus query; general G0 violation is not automatically a PC5 counter'}
(P/(mode+'-summary.json')).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
