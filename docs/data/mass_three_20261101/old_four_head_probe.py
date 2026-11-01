import sys,json
mode=sys.argv[1]
oldwords=['AAAA','AASAAA','ASAAAA','SAAAAA','SAAASAAA','SSAAAASAAA']
prefix='' if mode=='discovery' else 'SSAAAASAAA'
def word(s):return [x=='A' for x in s]
def mass(z):return sum(1 if x else -1 for x in z)
def area(z):return sum((len(z)-i)*(1 if x else -1) for i,x in enumerate(z))
def supplied(w):
 p=q=0;seen=set();out=[]
 for b,x in enumerate(w):
  out.append(bool(x and (p-1,q-b) in seen))
  seen.add((p,q));sign=1 if x else -1;p+=sign;q+=b*sign
 return out
tested=positive=0;minimum=100;example=None;violations=0
for S in range(11,15):
 for m in range(1,S-1):
  for s in range(1,S-m):
   h=S-m-s
   for M in range(1,S-1):
    for L in range(1,S-M):
     U=S-M-L;I=M*(m+s)+L*s;B=S*S-2*I
     for old in oldwords:
      u=word(old);a4=area(u)
      for k in range(3):
       v=3+k
       if B!=8*S+a4+(7 if k==1 else 6):continue
       z=[False]*h+[True]*M+[False]*m+[True]*L+[False]*s+[True]*U
       w=word(prefix+old);n=len(w);H=len(z);f=w+z+[False]*v+[True]*(k+1)
       source=len(prefix)
       assert mass(f[source:n+H+v+k])==1 and area(f[source:n+H+v+k])==0
       sup=supplied(f);tested+=1
       if sum(sup[:n])!=sum(not x for x in w):continue
       deficit=0;ok=True
       for b in range(n,n+H):
        deficit+=(not f[b])-sup[b]
        if deficit<1:ok=False;break
       if not ok:continue
       positive+=1;free=sum(f[b] and not sup[b] for b in range(n,n+H))
       if free<5:violations+=1
       if free<minimum:
        minimum=free;example=dict(old=prefix+old,supplier_source=source,head=[h,M,m,L,s,U],S=S,I=I,B=B,v=v,k=k,headfree=free)
print(json.dumps(dict(mode=mode,tested=tested,positive=positive,min_headfree=minimum,violations_headfree5=violations,example=example),sort_keys=True))
