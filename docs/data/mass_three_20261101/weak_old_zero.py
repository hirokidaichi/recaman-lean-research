import json
def w(s):return [x=='A' for x in s]
def mass(z):return sum(1 if x else -1 for x in z)
def area(z):return sum((len(z)-i)*(1 if x else -1) for i,x in enumerate(z))
def backward(z):
 a=b=0
 for i,x in enumerate(reversed(z)):a+=(1 if x else -1);b+=(i+1)*(1 if x else -1)
 return a,b
u=w('SSAAAA');z=w('SSSSAAAA');tail=[False];r=w('SSAAAA')+tail
whole=u+z+tail
assert mass(u)==2 and 2*area(u)-mass(u)*(mass(u)+1)==-8
assert mass(z)==0 and mass(whole)==1 and area(whole)==0
assert mass(r)==1 and area(r)==0 and backward(whole)==(1,0) and backward(r)==(1,0)
print(json.dumps(dict(weak_old='SSAAAA',head='SSSSAAAA',v=1,clock=0,initial_q=2,old_key=-8,both_windows=True,scope='weakened BlockWord premise only, not actual C1 counterexample')))
