# Lemma BW: for every block word w (len<=N), with A^j tail allowed via A-blocks, endables from 0 are exactly
# the members, and tau(member) = its block-window start (so tau is a bijection members -> S clocks).
import sys
N=int(sys.argv[1])
blocks=['SAAA','SSAAAASAAA','A']; memoff={'SAAA':[(3,0)],'SSAAAASAAA':[(4,1),(7,0),(9,6)],'A':[]}
bad=0;cnt=0
def chk(parse):
    global bad,cnt
    w=''.join(parse); cnt+=1
    mem={};pos=0
    for B in parse:
        for o,t in memoff[B]: mem[pos+o]=pos+t
        pos+=len(B)
    F=[0]
    for ch in w: F.append(F[-1]+(1 if ch=='A' else -1))
    G=[0]
    for u in range(1,len(F)): G.append(G[-1]+F[u])
    tau={}
    for b in range(len(w)):
        if w[b]!='A': continue
        for t in range(b-3,-1,-4):
            if F[b]==F[t]+1 and G[b]-G[t]==(b-t)*F[t]: tau[b]=t;break
    if tau!=mem: bad+=1; print(w,tau,mem) if bad<5 else None
def gen(parse,l):
    chk(parse)
    for B in blocks:
        if l+len(B)<=N: gen(parse+[B],l+len(B))
gen([],0); print("checked",cnt,"bad",bad)
