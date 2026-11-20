"""New odd-cycle LOWfree reuse, with main return and complete old-head audit."""
import json,sys
from pathlib import Path
cfg=json.loads(Path(sys.argv[1]).read_text());rows=[]
for N in cfg['discovery_N']+cfg['parameter_controls_N']:
 ss=[1];L=8
 for j in range(1,N):ss.append(4*(L+1)+1);L+=4*ss[-1]+4
 h=L//2+3;w='S'*h;selected=[];head_certs=[];prior=0
 for s in ss:
  assert s%2==1 and prior%4==0
  selected.append(len(w));w+='A'*s+'S'*(2*s+2)+'A'*(s+2)
  for r in range(1,min(h,s-1)+1):
   expr=s*s-prior-r*(2*s+prior);assert expr%2==1
   head_certs.append([s,prior,r,expr])
  prior+=4*s+4
 selected.append(len(w));w+='AA'
 H=[0];B=[0];states={(0,0):[0]};Akeys={};free=[];col=[];S=E=0
 for q,c in enumerate(w):
  hh=H[-1];area=B[-1]
  if c=='A':
   key=(hh-1,area-q*(hh-1))
   if key not in states:free.append(q)
   else:E+=1
   Akeys.setdefault(key,[]).append(q)
  else:S+=1
  assert S-E>=1
  nh=hh+(1 if c=='A'else-1);nb=area+nh;v=q+1;key=(nh,nb-v*nh)
  if c=='S':col += [('I',u,v)for u in states.get(key,[])]+[('II',u,v)for u in Akeys.get(key,[])]
  states.setdefault(key,[]).append(v);H.append(nh);B.append(nb)
 assert not col and H[-1]==2-h and min(H)==-h-ss[-1]-2
 C={q:(H[q]-1,(q+1)*(H[q]-1)-B[q])for q in free}
 assert all(q in C and H[q]==-h and H[q]<=1-h for q in selected)
 assert len({C[q]for q in selected})==1
 # Independently compare every possible new-head collision area to the odd certificate.
 offset=h;prior=0
 for s in ss:
  for k in range(1,2*s+3):
   r=s-k
   if 1<=r<=h:
    v=offset+s+k;u=h-r
    area=B[v]-B[u]-(v-u)*H[u]
    assert area==s*s-prior-r*(2*s+prior) and area%2==1
  offset+=4*s+4;prior+=4*s+4
 n=len(w)+1;b=100*n*n;x=100*(b+n)*n
 seed={0,x}|{x+b*t+k for t,k in C.values()};cur=x;seen=set(seed)
 for q,c in enumerate(w):
  nclock=b+q+1;A=cur-nclock<=0 or cur-nclock in seen
  assert A==(c=='A'),(N,q,c)
  cur=cur+nclock if A else cur-nclock;seen.add(cur);assert cur>0
 low=[q for q in free if H[q]<=1-h]
 pair=C[selected[0]];value=x+b*pair[0]+pair[1]
 assert all(x+(b+u+1)*H[u]-B[u]!=value for u in range(len(H)))
 rows.append(dict(N=N,s_values=ss,L=L,h=h,length=len(w),selected_LOWfree=selected,all_original_LOWfree=low,total_LOWfree=len(low),total_original_free=len(free),minimum_H=min(H),return_H=H[-1],depth_below_initial=ss[-1]+2,finite_C1_floor_violation=(min(H)<-h-len(low)),head_parity_checks=len(head_certs),all_I_II_collisions=[],same_candidate_pair=list(pair),shared_seed_value=value,base=b,current=x,seed=sorted(seed),actual_replay_steps=len(w)))
out=dict(PASS=True,rows=rows,scope='NEW odd-cycle LOWfree seed-load no-go controls, main-shaped return retained; total LOW census and C1 comparison explicitly reported, no canonical prehistory')
Path(sys.argv[2]).write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(PASS=True,rows=[{k:r[k]for k in ['N','length','selected_LOWfree','total_LOWfree','depth_below_initial','finite_C1_floor_violation','head_parity_checks']}for r in rows])))
