import json
A='AAASSSASASA';C=A[:-1];X='AS'*10+'A';S=X+C
# Period phases 0..30 are the reverse donor, 31 is its current A, 32 is older A.
p=S[::-1]+'AA'
def stats(w):
 m=M=q=0; hits=[]
 for i,b in enumerate(w,1):
  v=1 if b=='A' else -1;m+=v;M+=i*v
  q+=i>1 and w[i-2:i]=='SS'
  if m==1 and M==0:hits.append(i)
 return dict(word=w,length=len(w),mass=m,moment=M,ss=q,p2_prefixes=hits,oldest_offset=max((i for i,b in enumerate(w,1) if b=='S'),default=0))
def past(t,d):return ''.join(p[(t-i)%len(p)] for i in range(1,d+1))
print(json.dumps(dict(period=p,p=len(p),period_mass=p.count('A')-p.count('S'),circular_NoSAAS='SAAS' not in p*2,current_A=p[10],current_S=p[31],donor_A=stats(past(10,11)),donor_S=stats(past(31,31)),X=stats(X),sigma_A=(10-10)%len(p),sigma_S=(31-31)%len(p)),sort_keys=True))
