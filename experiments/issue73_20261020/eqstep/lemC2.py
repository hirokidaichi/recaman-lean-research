# Lemma C check: w' in B*, x='S'+w'. For every A position b of x that is NOT a member of w' (block parse),
# with [0,b-1] a P2 window: report (b, x[:b+1]) and whether x in B*.
import sys,re
N=int(sys.argv[1])
blocks=['SAAA','SSAAAASAAA','A']; memoff={'SAAA':[3],'SSAAAASAAA':[4,7,9],'A':[]}
blk=re.compile(r'^(SAAA|SSAAAASAAA|A)*$')
words={():''};fr=[()]
allw=[]
def gen(parse,w):
    allw.append((parse,w))
    for B in blocks:
        if len(w)+len(B)<=N: gen(parse+(B,),w+B)
gen((),'')
from collections import Counter
res=Counter(); bad=0
for parse,w in allw:
    mem=set(); pos=1
    for B in parse:
        for o in memoff[B]: mem.add(pos+o)
        pos+=len(B)
    x='S'+w
    F=[0]
    for ch in x: F.append(F[-1]+(1 if ch=='A' else -1))
    G=[0]
    for u in range(1,len(F)): G.append(G[-1]+F[u])
    for b in range(3,len(x),4):
        if x[b]=='A' and b not in mem and F[b]==1 and G[b]==0:
            res[(b,x[:b+1],bool(blk.match(x)))]+=1
print(len(allw),sorted(res.items()))
