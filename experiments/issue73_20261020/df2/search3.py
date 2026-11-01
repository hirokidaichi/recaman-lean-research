import random,sys
from phi2 import phi2
from phi import phi
from lib import endables
from collections import Counter
random.seed(int(sys.argv[1])); tested=0; phifails=0
def score(s):
    F,E=endables(s); U=[e for e in E if not e['clean']]
    g={}
    for e in U: g.setdefault(e['q'],[]).append(e['t'])
    nest=sum(1 for q in g for q2 in g if q<q2 and min(g[q2])<q)
    return nest*5+sum(len(v)-1 for v in g.values())*3+len(U)
for rnd in range(int(sys.argv[2])):
    n=random.randint(30,80); s=''.join(random.choice(['AS','SA','A','S','AASS','SSAA','SAAA','SSSA']) for _ in range(n))[:n]
    sc=score(s)
    for it in range(300):
        i=random.randrange(len(s)); j=min(len(s),i+random.randint(1,4))
        t=s[:i]+''.join(random.choice('AS') for _ in range(j-i))+s[j:]
        if random.random()<0.2: t=t[:i]+random.choice(['AS','SA','AASS'])+t[i:]
        if len(t)>110: continue
        sc2=score(t)
        if sc2>=sc: s,sc=t,sc2
        tg,err=phi2(t); tested+=1
        if phi(t)[1] is not None: phifails+=1
        if err: print('FAIL',t,err,flush=True); sys.exit()
print('tested',tested,'phi(original) fails',phifails)
