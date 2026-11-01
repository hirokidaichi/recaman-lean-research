import math,json,time
start=time.process_time();seed='S'*5+'A'*3+'S'*4+'A'*4+'S'+'A'*3
rows=[];pairs=set()
for t in range(len(seed)):
 z=seed[t:];m=a=0
 for c in z:m+=1 if c=='A' else -1;a+=m
 key=2*a-m*(m+1);d=m*m+(key+2)//2
 roots=[]
 if d>=0 and math.isqrt(d)**2==d:
  for v in sorted(set([m-math.isqrt(d),m+math.isqrt(d)])):
   i=1-m+v
   if v>=1 and i>=0:roots.append([v,i]);pairs.add((v,i))
 rows.append({'t':t,'suffix':z,'mass':m,'area':a,'key':key,'discriminant':d,'roots_v_i':roots})
checks=0
for v in range(17,33):
 for i in range(65):
  assert time.process_time()-start<.7
  w=seed+'S'*v+'A'*i;actual=False
  mass=area=0
  for t in range(len(w)-1,-1,-1):
   s=1 if w[t]=='A' else -1;mass+=s;area+=(len(w)-t)*s
   if mass==1 and area==0:actual=True
  expected=(i==2 or (v,i) in pairs)
  assert actual==expected,(v,i,actual,expected)
  checks+=1
print(json.dumps({'seed':seed,'rows':rows,'finite_algebraic_pairs':sorted(pairs),'independent_backward_literal_holdout_checks':checks,'holdout_gaps':[17,32],'algorithm_cpu_seconds':time.process_time()-start,'scope':'finite certificate generation and literal validation; arbitrary v/i only after Lean proof'},indent=2))
