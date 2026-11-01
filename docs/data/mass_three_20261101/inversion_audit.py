import sys,json
mode=sys.argv[1]
def mass(w): return sum(1 if c else -1 for c in w)
def area(w): return sum((len(w)-k)*(1 if c else -1) for k,c in enumerate(w))
def sources(w,i):
    u=w+[True]*i
    return [t for t in range(len(w)) if mass(u[t:])==1 and area(u[t:])==0]
def reverse_sources(w,i):
    acc=0; moment=0; out=[]
    u=w+[True]*i
    for k in range(len(u)-1,-1,-1):
        sign=1 if u[k] else -1
        acc+=sign;moment+=(len(u)-k)*sign
        if k<len(w) and acc==1 and moment==0:out.append(k)
    return sorted(out)
def tuples(cap):
    for M in range(1,cap//2+1):
      for m in range(1,cap):
       for s in range(1,cap):
        rem=cap-M*(m+s)
        if rem<s:continue
        for L in range(1,rem//s+1):yield M,m,L,s
count=0; maxcount=0; boundary=None
if mode=='discovery':
 for M,m,L,s in tuples(14):
  I=M*(m+s)+L*s
  for h in range(0,6):
   w=[False]*h+[True]*M+[False]*m+[True]*L+[False]*s
   clocks=[i for i in range(6) if sources(w,i)]
   assert len(clocks)<=2,(h,M,m,L,s,I,clocks)
   count+=1;maxcount=max(maxcount,len(clocks))
 print(json.dumps(dict(mode=mode,cases=count,max_local=maxcount,I_cap=14,h_range=[0,5],clock_range=[0,5])))
elif mode=='holdout':
 for M,m,L,s in tuples(14):
  w=[False]*17+[True]*M+[False]*m+[True]*L+[False]*s
  clocks=[i for i in range(19) if reverse_sources(w,i)]
  assert len(clocks)<=2,(17,M,m,L,s,clocks)
  count+=1;maxcount=max(maxcount,len(clocks))
 print(json.dumps(dict(mode=mode,cases=count,max_local=maxcount,I_cap=14,h=17,clock_range=[0,18],independent_reverse=True)))
else: raise ValueError(mode)
