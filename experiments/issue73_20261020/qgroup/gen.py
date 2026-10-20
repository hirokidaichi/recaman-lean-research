import random,sys
random.seed(int(sys.argv[1])); N=int(sys.argv[2]); L=int(sys.argv[3]) if len(sys.argv)>3 else 120
blocks=['SA','AS','S','A','SA','SA','AASS','SSAA','SAAA','SSSA']
def rnd():
    out=''
    while len(out)<L:
        r=random.random()
        if r<0.25: k=random.randint(1,5); out+='A'*k+'S'*k
        elif r<0.45: j=random.randint(0,6); out+='S'+'SA'*j+'A'
        elif r<0.6: out+='SA'*random.randint(1,8)
        elif r<0.7: out+='AS'*random.randint(1,4)
        else: out+=random.choice(blocks)
    i=random.randrange(0,max(1,len(out)-L+1)); return out[:L]
for _ in range(N): print(rnd())
