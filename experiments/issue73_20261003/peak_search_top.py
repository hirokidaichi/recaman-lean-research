#!/usr/bin/env python3
"""Peak search for TOP (H-20261003-01): is there a finite closed configuration whose walk maximum K over
[x, y] is attained at an S clock tau (taken as the LAST visit, so F < K on (tau, y]) with F(y+1) <= K?
Clock 0 = tau, sigma(0) = S, F(0) = 0 (= K).  Constraints checked on the known contiguous interval
[lo, hi] (hi = newest placed member): F(c) <= 0 for c in [lo, hi], F(c) <= -1 for c in (0, hi-1].
Every real counterexample to TOP satisfies them at every node (sound).  Search = E-356 rules (M1, owner
not already a member, owner clock not S, window bits consistent, M2 for every S in a member window),
MRV need order, owners = minimal words of lag <= Lown with any S offset.  No v is fixed: the root need
is the S at clock 0."""
import sys
sys.path.insert(0, __import__('os').path.dirname(__file__))
from walk import mins, s
Lown=int(sys.argv[1]); memberCap=int(sys.argv[2]) if len(sys.argv)>2 else 40; nodeCap=int(sys.argv[3]) if len(sys.argv)>3 else 2000000
OWN=[w for L in range(3,Lown+1,4) for w in mins(L)]
SOFF={w:[i+1 for i,b in enumerate(w) if not b] for w in OWN}
PL=[(w,k) for w in OWN for k in SOFF[w]]
def walk_ok(bits, members):
    lo=min(bits); hi=max(bits)
    # F(0)=0; F(c+1)=F(c)+sign(c)
    F={0:0}
    for c in range(0,hi):
        if c not in bits: return True  # unknown gap (should not happen: interval is contiguous)
        F[c+1]=F[c]+(1 if bits[c] else -1)
    for c in range(-1,lo-1,-1):
        F[c]=F[c+1]-(1 if bits[c] else -1)
    hm=max(members) if members else 0
    for c,f in F.items():
        if c<lo or c>hi: continue
        if f>0: return False
        if 0<c<=hm-1 and f>-1: return False
    return True
def consistent(bits, members, w, k, sc):
    u=sc+k
    if u in members or bits.get(u,True) is not True: return None
    new={u:True}
    for i,b in enumerate(w):
        c=u-(i+1); x=bits.get(c)
        if x is None: new[c]=b
        elif x!=b: return None
    # contiguity: the new window must touch the known interval (it contains sc, which is known)
    return new
class S_:
    nodes=0; found=None; cap=False
st=S_()
def rec(bits, members, owned, need):
    st.nodes+=1
    if st.nodes>nodeCap: st.cap=True; return
    if not need:
        st.found=(dict(members),dict(owned)); return
    if len(members)>=memberCap: st.cap=True; return
    best=None
    for scx in need:
        opts=[]
        for w,k in PL:
            new=consistent(bits,members,w,k,scx)
            if new is None: continue
            b2=dict(bits); b2.update(new); m2=dict(members); m2[scx+k]=w
            if not walk_ok(b2,m2): continue
            opts.append((w,k,new))
        if best is None or len(opts)<len(best[1]): best=(scx,opts)
        if not opts: break
    sc,opts=best
    rest=[c for c in need if c!=sc]
    for w,k,new in opts:
        u=sc+k
        b2=dict(bits); b2.update(new); m2=dict(members); m2[u]=w; o2=dict(owned); o2[sc]=u
        nn=[u-kk for kk in SOFF[w] if (u-kk) not in o2]
        rec(b2,m2,o2,rest+[c for c in nn if c not in rest])
        if st.found or st.cap: return
rec({0:False},{},{},[0])
print(f'peak search, owners lag <= {Lown} ({len(OWN)} words, {len(PL)} placements): nodes {st.nodes}, cap {st.cap}')
if st.found:
    m,o=st.found
    print('FOUND closure:',' '.join(f'{u}:{s(w)}' for u,w in sorted(m.items())),' own:',o)
else:
    print('no closure' if not st.cap else 'undecided (cap)')
