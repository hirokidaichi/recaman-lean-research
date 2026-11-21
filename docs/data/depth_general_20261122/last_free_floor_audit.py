"""New prefix floor producer and lower-closed free-class capacity audit."""
from itertools import product
import json,time
from collections import Counter
t0=time.process_time();stats=Counter()
def data(w):
 H=[0];B=[0];free=[];C={};sup={}
 for q,e in enumerate(w):
  if e==1:
   sources=[]
   for u in range(q):
    seg=w[u:q]
    if sum(seg)==1 and sum(sum(seg[:j]) for j in range(1,len(seg)+1))==0:sources.append(u)
   sup[q]=sources
   if not sources:free.append(q);C[q]=(H[-1]-1,(q+1)*(H[-1]-1)-B[-1])
  H.append(H[-1]+e);B.append(B[-1]+H[-1])
 return H,B,free,C,sup
for L in range(11):
 for w in product([-1,1],repeat=L):
  H,B,free,C,sup=data(w)
  for R in range(min(H)-1,max(H)+2):
   selected=[q for q in free if H[q]<=R]
   if not selected:stats['empty_selections']+=1;continue
   qlast=selected[-1];ell=min(H[q] for q in selected);M=max(H[q] for q in selected)
   assert min(H[:qlast+2])==ell
   Hp,Bp,fp,Cp,sp=data(w[:qlast+1])
   assert [q for q in fp if Hp[q]<=R]==selected
   assert all(sp[q]==s for q,s in sup.items() if q<=qlast)
   assert [Cp[q] for q in selected]==[C[q] for q in selected]
   K=len({C[q] for q in selected});F=len(selected);W=M-ell;b=[K,K]
   for j in range(2,W+1):b.append((K+1+b[-1]+b[-2])*(1+b[-2]))
   assert F==K if W<=1 else F<=K*(1+b[W-2])
   stats['prefix_floor_source_class_capacity_checks']+=1
  stats['words']+=1;stats['discovery' if L<=7 else 'parameter_controls']+=1
  if stats['words']%128==0 and time.process_time()-t0>.65:
   print(json.dumps({'completed_predicates_pass':True,'range_complete':False,'counts':dict(stats),'stop':'prefix audit cap, no extension'}));raise SystemExit(0)
# Two OLD/simple controls separate the lower-closed set and prefix scope.
wtail=[1]+[-1]*4;Ht,Bt,ft,Ct,st=data(wtail)
assert ft==[0] and min(Ht)==-3 and min(Ht[:2])==0
wold=[-1]*7+[1]+[-1]*4+[1]*5;Ho,Bo,fo,Co,so=data(wold)
assert 7 in fo and 15 in fo and Co[7]==Co[15] and Ho[7]==Ho[15]==-7
assert min(Ho[:17])==-10
print(json.dumps({'all_pass':True,'counts':dict(stats),'tail_S_scope_negative':{'word':'ASSSS','selected_class_min':0,'full_word_min':-3,'last_selected_prefix_min':0},'arbitrary_subfamily_negative':{'OLD_word':'S7 AS4 A5','chosen_only':[7,15],'classes':1,'free_clocks':2,'chosen_height_span':0,'full_prefix_min':-10,'chosen_min_height':-7,'reason':'lower free mass omitted; lower-closed selection premise essential'},'worker_internal_cpu_seconds':time.process_time()-t0},indent=2))
