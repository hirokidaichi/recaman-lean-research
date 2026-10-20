# j=4 branch of Short-z: prefix w ends with SAAA (block word), z = SSSSAAAA S ..., explore continuations of z
# with a_z=2 used (k1+4,k1+5), check every A before first return to F(k1)+1: list possible window starts (any t in w-part allowed generically via D/area constraints).
import itertools
# enumerate full strings: w = random block words ending SAAA? Use brute: w in B* of length <= 14 ending with SAAA
B=['SAAA','SSAAAASAAA','A']
def bw(n):
    res=set([''])
    out=set()
    frontier=['']
    while frontier:
        nf=[]
        for x in frontier:
            for b in B:
                y=x+b
                if len(y)<=n: nf.append(y); out.add(y)
        frontier=list(set(nf))
    return out
def endable_from(s,b,p=0):
    F=[0]
    for ch in s: F.append(F[-1]+(1 if ch=='A' else -1))
    res=[]
    for t in range(b-3,p-1,-4):
        if F[b]==F[t]+1 and sum(F[u]-F[t] for u in range(t+1,b+1))==0: res.append(t)
    return res
ws=[w for w in bw(16) if w.endswith('SAAA')]
bad=0; tot=0
for w in ws:
    k1=len(w)
    for L in range(0,12):
        for tail in itertools.product('SA',repeat=L):
            z='SSSSAAAA'+''.join(tail)
            s=w+z
            F=[0]
            for ch in s: F.append(F[-1]+(1 if ch=='A' else -1))
            # require: first return to F(k1)+1 happens exactly at end, all A after k1+5 endable, d>=1 maintained (skip)
            if F[-1]!=F[k1]+1 or any(F[u]==F[k1]+1 for u in range(k1+1,len(s))): continue
            ok=True
            for b in range(k1+6,len(s)):
                if s[b]=='A' and not endable_from(s,b): ok=False;break
            tot+=1
            if ok:
                bad+=1; print("SURVIVOR",w,'|',z)
print("checked",tot,"survivors",bad)
