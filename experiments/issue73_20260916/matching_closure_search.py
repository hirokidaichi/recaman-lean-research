#!/usr/bin/env python3
"""Matching-closure search (no OS assumption), bit-level, no periodicity.  Registry E-356.

Setting (E-345/E-349): U = additions with a minimal P2 window, N([b]) = subtraction clocks inside b's window,
B ⊆ U tight (|N(B)| = |B|) in a word where Hall holds on U.  Hall's theorem gives a bijection own : B -> N(B)
with own(b) ∈ N([b]).  The search uses only its two one-sided halves:
  (M1) every member owns exactly one subtraction of its own window (own is a function, any offset);
  (M2) every subtraction inside any member's window is owned by some member (own is onto N(B)).
Lifted to the line (members b + jp, own(b + jp) = own(b) + jp) both halves survive, so a contradiction on the
line with no periodicity assumption is a contradiction in every positive-sum periodic Hall-OK word.
Injectivity of own is NOT used.  This replaces the OS assumption of E-354 (owner places its OLDEST S) by the
matching itself (owner places ANY of its S's on the owned clock).

Search: v (minimal P2 word of lag Lv, assumed the largest lag in B) at clock 0.  Branch on which S v owns (M1).
Every unowned S inside a placed window needs an owner (M2): a word w of lag <= Lv (or <= --owners) and an S
offset k of w, placed at u = s + k; rejected if u is already a member (M1: it owns another S), if u is a known
S bit, or if any window bit disagrees with an already placed bit.  Optional LA-AAS pruning (Hall augmentation,
E-351): a visible AAS at x whose S is in N(B) must be a member owning that S.  Need order: --mrv picks the
unowned S with the fewest consistent placements (smallest trees); default FIFO.
Result per v: excluded (every branch conflicts), CONSISTENT (a finite closed configuration; the check cannot
exclude v), or cap.  --emit-cert writes the MRV search trees as Lean certificates (coordinates shifted by 64).
Usage: mcs2.py Lv [memberCap] [nodeCap] [--owners=L] [--mrv] [--noaas] [--trace] [--v=WORD] [--all] [--emit-cert=FILE]"""
import sys
from itertools import product
from functools import lru_cache
sys.setrecursionlimit(10000)
def mass(w): return sum(1 if b else -1 for b in w)
def moment(w): return sum((i+1)*(1 if b else -1) for i,b in enumerate(w))
def p2(w): return mass(w)==1 and moment(w)==0
def minimal(w): return p2(w) and not any(p2(w[:d]) for d in range(1,len(w)))
def bit_words(n):
    """Same enumeration order as Lean `bitWords` (TwoSSEndpoint): bitWords (n+1) = flatMap (w => [false::w, true::w])."""
    ws=[()]
    for _ in range(n): ws=[(b,)+w for w in ws for b in (False,True)]
    return ws
@lru_cache(None)
def minimal_words(L): return [w for w in bit_words(L) if minimal(w)]
def s(w): return ''.join('A' if b else 'S' for b in w)
def parse(t): return tuple(c=='A' for c in t)
def s_offsets(w): return [i+1 for i,b in enumerate(w) if not b]
AAS=(True,True,False)

flags=[a for a in sys.argv[1:] if a.startswith('--')]
args=[a for a in sys.argv[1:] if not a.startswith('--')]
def flag(name, default=None):
    for f in flags:
        if f==name: return True
        if f.startswith(name+'='): return f[len(name)+1:]
    return default
TRACE=flag('--trace',False); NOAAS=flag('--noaas',False); MRV=flag('--mrv',False); ALL=flag('--all',False)
LOWN=flag('--owners'); LOWN=int(LOWN) if LOWN else None
VSEL=flag('--v'); EMIT=flag('--emit-cert')
SH=flag('--shard'); SHARD=tuple(int(x) for x in SH.split('/')) if SH else (0,1)
Lv=int(args[0]); memberCap=int(args[1]) if len(args)>1 else 14; nodeCap=int(args[2]) if len(args)>2 else 2000000
OWNERS=[w for L in range(3,(LOWN or Lv)+1,4) for w in minimal_words(L)]
PLACEMENTS=[(i,w,k) for i,w in enumerate(OWNERS) for k in s_offsets(w)]
R=64  # coordinate shift for certificates

class Search:
    def __init__(self): self.nodes=0; self.found=[]; self.capHit=False; self.capConfig=None; self.span=(0,0)
    def run(self, v, ownIdx):
        bits={0:True}
        for i,b in enumerate(v): bits[-(i+1)]=b
        members={0:v}; owned={-s_offsets(v)[ownIdx]:0}
        need=[-k for k in s_offsets(v) if -k not in owned]
        self.nodes=0; self.found=[]; self.capHit=False
        tree=self.rec(bits, members, owned, need)
        return self.found, self.capHit, self.nodes, tree
    def consistent(self, bits, members, w, k, sc):
        u=sc+k
        if u in members: return None, 'member'
        if bits.get(u,True) is not True: return None, 'u is S'
        new={u:True}
        for i,b in enumerate(w):
            c=u-(i+1)
            if c in bits:
                if bits[c]!=b: return None, f'conflict at {c}'
            else: new[c]=b
        return new, None
    def rec(self, bits, members, owned, need):
        """Returns a certificate tree (sc, [(i,k,subtree),...]) when every branch is excluded, else None."""
        self.nodes+=1
        self.span=(min(self.span[0],min(bits)),max(self.span[1],max(bits)))
        if self.nodes>nodeCap: self.capHit=True; return None
        if not need:
            self.found.append(dict(members)); return None
        if len(members)>=memberCap:
            self.capHit=True
            if self.capConfig is None: self.capConfig=(dict(members), list(need))
            return None
        if MRV:
            def ncons(scx): return sum(1 for _,w,k in PLACEMENTS if self.consistent(bits,members,w,k,scx)[0] is not None)
            sc=min(need,key=ncons)
        else: sc=need[0]
        rest=[c for c in need if c!=sc]; depth=len(members)-1
        if TRACE: print('  '*(depth+1)+f'need owner for S at clock {sc} (owned: {sorted(owned)})')
        forced=None
        if not NOAAS:
            x=sc+3
            if bits.get(x) is True and bits.get(x-1) is True and bits.get(x-2) is True: forced=x
        kids=[]; allExcluded=True
        for i,w,k in PLACEMENTS:
            u=sc+k
            if forced is not None and (w!=AAS or u!=forced):
                continue   # LA-AAS: only the forced AAS may own sc
            new,why=self.consistent(bits,members,w,k,sc)
            if new is None:
                if TRACE: print('  '*(depth+2)+f'{s(w)}@{u} (offset {k}): {why}')
                continue
            bits2=dict(bits); bits2.update(new)
            members2=dict(members); members2[u]=w
            owned2=dict(owned); owned2[sc]=u
            if not NOAAS:
                bad=None
                covered=set(m-kk for m,ww in members2.items() for kk in s_offsets(ww))
                for c in covered:
                    x=c+3
                    if bits2.get(x) is True and bits2.get(x-1) is True and bits2.get(x-2) is True:
                        if c in owned2 and owned2[c]!=x: bad=f'AAS at {x} must own {c} (owner {owned2[c]})'; break
                        if x in members2 and members2[x]!=AAS: bad=f'AAS at {x} but member word differs'; break
                if bad:
                    if TRACE: print('  '*(depth+2)+f'{s(w)}@{u} (offset {k}): {bad}')
                    continue
            if TRACE: print('  '*(depth+2)+f'{s(w)}@{u} (offset {k}): placed')
            newneed=[u-kk for kk in s_offsets(w) if (u-kk) not in owned2]
            need2=rest+[c for c in newneed if c not in rest]
            sub=self.rec(bits2, members2, owned2, need2)
            if sub is None: allExcluded=False
            else: kids.append((i,k,sub))
            if (self.found or self.capHit) and not ALL: return None
        return (sc,kids) if allExcluded else None

def cert_lean(tree):
    sc,kids=tree
    inner=', '.join(f'({i}, {k}, {cert_lean(sub)})' for i,k,sub in kids)
    return f'.node {sc+R} [{inner}]'

V=[w for idx,w in enumerate(minimal_words(Lv)) if idx%SHARD[1]==SHARD[0]]
if VSEL: V=[parse(VSEL)]
print(f"lag-max {Lv}: {len(V)} words v, {len(OWNERS)} owner words (lag <= {LOWN or Lv}), {len(PLACEMENTS)} placements, memberCap={memberCap}, nodeCap={nodeCap}, LA-AAS={'off' if NOAAS else 'on'}, order={'MRV' if MRV else 'FIFO'}")
excluded=0; open_=0; capped=0; certs=[]
for v in V:
    res=[]; anyfound=False; anycap=False; tot=0; trees=[]; srch=Search()
    for oi,k0 in enumerate(s_offsets(v)):
        found,cap,nodes,tree=srch.run(v,oi); tot+=nodes
        if found and not cap:
            anyfound=True
            for f in found: res.append(f"own offset {k0}: CONSISTENT ({len(f)} members, {nodes} nodes): "+' '.join(f"{u}:{s(w)}" for u,w in sorted(f.items())))
        elif cap:
            anycap=True; res.append(f"own offset {k0}: cap ({nodes} nodes)")
            if srch.capConfig: m,n=srch.capConfig; res.append('        cap config: '+' '.join(f'{u}:{s(w)}' for u,w in sorted(m.items()))+f' | need {sorted(n)}')
        else:
            res.append(f"own offset {k0}: excluded ({nodes} nodes)"); trees.append((k0,tree))
    if anyfound: open_+=1; tag='CONSISTENT'
    elif anycap: capped+=1; tag='CAP'
    else: excluded+=1; tag='excluded'; certs.append((v,trees))
    print(f"  {s(v)}: {tag} (total {tot} nodes, span {srch.span[0]}..{srch.span[1]})")
    if tag!='excluded' or TRACE or ALL:
        for r in res: print('     '+r)
print(f"=> excluded {excluded}/{len(V)}, consistent closure {open_}, cap hit {capped}")
if EMIT:
    with open(EMIT,'w') as f:
        f.write(f"-- generated by mcs2.py {' '.join(sys.argv[1:])}: owner words in Lean `ownerWords` order, coordinates shifted by {R}\n")
        f.write("-- ownerWords: "+' '.join(f'{i}:{s(w)}' for i,w in enumerate(OWNERS))+"\n")
        for v,trees in certs:
            body=', '.join(f'({k0}, {cert_lean(t)})' for k0,t in trees)
            f.write(f"/-- Certificate for `{s(v)}`: one search tree per subtraction that `v` may own. -/\ndef cert_{s(v)} : List (Nat × Cert) := [{body}]\n\n")
