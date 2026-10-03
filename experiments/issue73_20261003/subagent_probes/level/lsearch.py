#!/usr/bin/env python3
"""Copy of matching_closure_search (M1 + M2 + injectivity via 'u not already member' and 'owned' map), with options:
  --level      : every ownership edge is a LEVEL edge: owner w owns an S whose top level equals h_w
                 (i.e. only S offsets k with relative height H=0 at that S).  Applies to v too.
  --vlevel     : only v's own edge is level-restricted.
  --owners=L   : owner lag bound.  --all : enumerate all closures.  --v=WORD.
Prints per-v result and node counts.  No LA-AAS pruning (keeps the argument minimal)."""
import sys, time
from mwords import minimal_words, s, parse, heights
flags=[a for a in sys.argv[1:] if a.startswith('--')]
args=[a for a in sys.argv[1:] if not a.startswith('--')]
def flag(name, default=None):
    for f in flags:
        if f==name: return True
        if f.startswith(name+'='): return f[len(name)+1:]
    return default
LEVEL=flag('--level',False); VLEVEL=flag('--vlevel',False) or LEVEL; ALL=flag('--all',False)
LOWN=flag('--owners'); VSEL=flag('--v'); QUIET=flag('--quiet',False)
Lv=int(args[0]); memberCap=int(args[1]) if len(args)>1 else 40; nodeCap=int(args[2]) if len(args)>2 else 2000000
LOWN=int(LOWN) if LOWN else Lv
def s_offsets(w): return [i+1 for i,b in enumerate(w) if not b]
def level_offsets(w):
    L=len(w); H=heights(w)
    # offset k <-> clock b-k = t+(L-k); top level rel = H[L-k]
    return [k for k in s_offsets(w) if H[L-k]==0]
OWNERS=[w for L in range(3,LOWN+1,4) for w in minimal_words(L)]
REL=flag('--rel')
def rel_ok(w,k):
    L=len(w); H=heights(w); r=H[L-k]
    return REL is None or (REL=='ge0' and r>=0) or (REL=='le0' and r<=0) or (REL=='eq0' and r==0) or (REL=='le1' and r<=1) or (REL=='m1to1' and -1<=r<=1)
PLACEMENTS=[(w,k) for w in OWNERS for k in (level_offsets(w) if LEVEL else s_offsets(w)) if rel_ok(w,k)]
NEWEST=flag('--newest',False)
def consistent(bits, members, w, k, sc):
    u=sc+k
    if NEWEST and u>0: return None
    if u in members or bits.get(u,True) is not True: return None
    new={u:True}
    for i,b in enumerate(w):
        c=u-(i+1); x=bits.get(c)
        if x is None: new[c]=b
        elif x!=b: return None
    return new
class Search:
    def __init__(s_): s_.nodes=0; s_.found=[]; s_.cap=False
    def rec(s_, bits, members, owned, need):
        s_.nodes+=1
        if s_.nodes>nodeCap: s_.cap=True; return
        if not need: s_.found.append((dict(members),dict(owned),dict(bits))); return
        if len(members)>=memberCap: s_.cap=True; return
        best=None
        for scx in need:
            opts=[]
            for w,k in PLACEMENTS:
                new=consistent(bits,members,w,k,scx)
                if new is not None: opts.append((w,k,new))
            if best is None or len(opts)<len(best[1]): best=(scx,opts)
            if not opts: break
        sc,opts=best
        rest=[c for c in need if c!=sc]
        for w,k,new in opts:
            u=sc+k
            bits2=dict(bits); bits2.update(new)
            members2=dict(members); members2[u]=w
            owned2=dict(owned); owned2[sc]=u
            newneed=[u-kk for kk in s_offsets(w) if (u-kk) not in owned2]
            need2=rest+[c for c in newneed if c not in rest]
            s_.rec(bits2,members2,owned2,need2)
            if (s_.found or s_.cap) and not ALL: return
V=minimal_words(Lv)
if VSEL: V=[parse(VSEL)]
print(f"lag {Lv}: {len(V)} v, owners<= {LOWN}: {len(OWNERS)} words, {len(PLACEMENTS)} placements, level={'all' if LEVEL else ('v' if VLEVEL else 'off')}")
t0=time.time(); tot={'excl':0,'cons':0,'cap':0}; maxn=0; sumn=0
for v in V:
    bits={0:True}
    for i,b in enumerate(v): bits[-(i+1)]=b
    srch=Search(); res=[]
    for k0 in [k for k in (level_offsets(v) if VLEVEL else s_offsets(v)) if rel_ok(v,k)]:
        srch.found=[]; srch.cap=False; n0=srch.nodes
        owned={-k0:0}
        need=[-k for k in s_offsets(v) if k!=k0]
        srch.rec(bits,{0:v},owned,need)
        if srch.found: res.append(('CONS',k0,srch.found))
        elif srch.cap: res.append(('CAP',k0,None))
    maxn=max(maxn,srch.nodes); sumn+=srch.nodes
    tag='CONS' if any(r[0]=='CONS' for r in res) else ('CAP' if res else 'excl')
    tot[{'CONS':'cons','CAP':'cap','excl':'excl'}[tag]]+=1
    if tag!='excl' or not QUIET:
        print(f"  {s(v)}: {tag} nodes={srch.nodes}")
        for r in res:
            if r[0]=='CONS':
                for (m,o,b) in r[2]:
                    print(f"     own offset {r[1]}: "+' '.join(f"{u}:{s(w)}" for u,w in sorted(m.items()))+"  owned "+str(sorted(o.items())))
print(f"=> {tot}  max nodes/v={maxn} total nodes={sumn} time={time.time()-t0:.1f}s")
