import json
old=[False]+[True]*7
z=[False]*13+[True]+[False]+[True]*3+[False]+[True]*11
v=7;k=2;K=3;n=len(old);H=len(z)
word=old+z+[False]*v+[True]*K
def mass(w):return sum(1 if x else -1 for x in w)
def area(w):return sum((len(w)-i)*(1 if x else -1) for i,x in enumerate(w))
def wins(b):return [t for t in range(b) if mass(word[t:b])==1 and area(word[t:b])==0]
sup=[bool(word[b] and wins(b)) for b in range(len(word))]
positive=[sum(not x for x in word[n:n+j])-sum(sup[n:n+j]) for j in range(1,H+v+K+1)]
headfree=sum(word[b] and not sup[b] for b in range(n,n+H))
assert mass(z)==0 and mass(old)==6 and 0 in wins(n+H+v+k)
assert sum(sup[:n])==sum(not x for x in old) and min(positive)>=1 and headfree>=5
print(json.dumps(dict(old='SAAAAAAA',head=[13,1,1,3,1,11],head_S=15,B=-area(z),supplier_clock=k,supplier_mass=mass(old),supplier_sources=wins(n+H+v+k),headfree=headfree,min_positive=min(positive),zero=True)))
