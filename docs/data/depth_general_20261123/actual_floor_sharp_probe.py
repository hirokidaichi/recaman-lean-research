"""Frozen actual two-floor sharpness family: complete stock and literal clock cuts."""
import json,time
t0=time.process_time();records=[]
for label,bs in [('discovery',range(1,41)),('parameter_holdout',[61,97,257,1021]),('boundary',[0])]:
 for b in bs:
  w=[1]+[z for j in range(b) for z in (1,-1)]+[1]
  X=[1];H=[0];seen={0,1};checks=[]
  for q,e in enumerate(w):
   n=b+q+1;c=X[-1]-n;got=-1 if c>0 and c not in seen else 1
   assert got==e,(b,q,c,got,e)
   y=X[-1]+e*n;assert y>0
   if e==-1:assert y==b+1-(q-2)//2 and y not in seen
   else:assert c<=0
   seen.add(y);X.append(y);H.append(H[-1]+e)
  v0=max(t for t,h in enumerate(H) if h==0);c1=v0+1
  v1=max(t for t,h in enumerate(H) if t>=c1 and h==1);c2=v1+1
  P=[b+2,b+c1+2*X[c1],b+c2+2*X[c2]]
  assert min(H)==0 and H[-1]==2 and c1==1 and c2==2*b+2
  assert P==[b+2,3*b+5,9*b+10]
  assert P[1]==3*P[0]-1 and P[2]==9*P[0]-8
  assert P[2]<=3*P[1]-1
  rec={'label':label,'b':b,'length':len(w),'c1':c1,'c2':c2,'P0_P1_P2':P,'coherent_initial_stock':[0,1],'all_actual_signs_pass':True,'upper_bound_9P0_minus4':9*P[0]-4}
  if b in [0,1,7]:rec.update(word=''.join('A' if e==1 else 'S' for e in w),outputs=X,H=H)
  records.append(rec)
print(json.dumps({'all_pass':True,'records':records,'count':len(records),'scope':'finite exact parameter controls, unbounded sharpness requires paper proof; arbitrary finite State, not canonical/initialS/original-positive','worker_internal_cpu_seconds':time.process_time()-t0},indent=2))
