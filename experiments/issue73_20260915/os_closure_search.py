#!/usr/bin/env python3
"""Closure search for chain step 3 (H-20260915-21), bit-level, no periodicity.

Model: OS (E-349) says that in a tight B every subtraction clock s covered by a member is the oldest
subtraction of exactly one member ("owner"), and every member of B has all its subtractions covered.
Start from a member v (minimal P2 word of lag Lv) placed at clock 0, assume v has the LARGEST lag in B,
and close under "every S needs an owner of lag <= Lv whose window is bit-consistent with what is already
placed".  Owners are placed with their oldest S on the S to be owned (u = s + oldestOffset(w)).  Distinct
members have distinct oldest S (OS injectivity).  Success = a consistent closed finite configuration
exists (this check cannot exclude v); failure on all branches = under OS no tight B has lag-max member v.
Periodicity would only add constraints, so failure here is failure in every periodic word.
Usage: os_closure_search.py Lv [memberCap] [nodeCap] [--trace] [--shard=i/n]"""
import sys
from itertools import product
from functools import lru_cache
sys.setrecursionlimit(10000)
def mass(w): return sum(1 if b else -1 for b in w)
def moment(w): return sum((i+1)*(1 if b else -1) for i,b in enumerate(w))
def p2(w): return mass(w)==1 and moment(w)==0
def minimal(w): return p2(w) and not any(p2(w[:d]) for d in range(1,len(w)))
@lru_cache(None)
def minimal_words(L): return [w for w in product([True,False],repeat=L) if minimal(w)]
def s(w): return ''.join('A' if b else 'S' for b in w)
def oldest_offset(w): return max(i for i,b in enumerate(w) if not b)+1

TRACE = '--trace' in sys.argv; sys.argv=[a for a in sys.argv if a!='--trace']
SHARD=(0,1)
for a in list(sys.argv):
    if a.startswith('--shard='):
        i,n=a[8:].split('/'); SHARD=(int(i),int(n)); sys.argv.remove(a)
LOWN=None
for a in list(sys.argv):
    if a.startswith('--owners='): LOWN=int(a[9:]); sys.argv.remove(a)
Lv = int(sys.argv[1]); memberCap = int(sys.argv[2]) if len(sys.argv)>2 else 12; nodeCap = int(sys.argv[3]) if len(sys.argv)>3 else 300000
OWNERS = [w for L in range(3, (LOWN or Lv)+1, 4) for w in minimal_words(L)]
OWNERS_BY_PAIRED = {True: [w for w in OWNERS if oldest_offset(w)>=2 and not w[oldest_offset(w)-2]],
                    False: [w for w in OWNERS if not (oldest_offset(w)>=2 and not w[oldest_offset(w)-2])]}

class Search:
    def __init__(self):
        self.nodes=0; self.found=None; self.capHit=False
    def run(self, v):
        bits={0:True}
        for i,b in enumerate(v): bits[-(i+1)]=b
        members={0: v}                      # clock -> word
        owned={ -oldest_offset(v): 0 }      # S clock -> owner clock
        need=[-(i+1) for i,b in enumerate(v) if not b and -(i+1) not in owned]
        self.nodes=0; self.found=None; self.capHit=False; self.vS=set(c for c,b in bits.items() if b is False); self.maxOwnedV=0
        self.rec(bits, members, owned, need)
        return self.found, self.capHit, self.nodes
    def rec(self, bits, members, owned, need):
        self.nodes+=1
        self.maxOwnedV=max(self.maxOwnedV, len([c for c in owned if c in self.vS]))
        if self.nodes>nodeCap: self.capHit=True; return True
        if not need:
            self.found=dict(members); return True
        if len(members)>=memberCap: self.capHit=True; return True
        sc = need[0]; rest = need[1:]
        depth=len(members)-1
        if TRACE: print('  '*(depth+1)+f'need S at clock {sc} (owned so far: {sorted(owned)})')
        for w in OWNERS:                 # every owner word; bit consistency decides (sc+1 may be unset)
            kw = oldest_offset(w); u = sc + kw
            if u in members:
                if TRACE: print('  '*(depth+2)+f'{s(w)} at u={u}: clock already a member'); 
                continue
            # consistency
            new = {}
            ok = bits.get(u, True) is True
            if not ok:
                if TRACE: print('  '*(depth+2)+f'{s(w)} at u={u}: u is an S bit')
                continue
            new[u]=True
            why=None
            for i,b in enumerate(w):
                c=u-(i+1)
                if c in bits:
                    if bits[c]!=b: ok=False; why=f'conflict at clock {c} (needs {"A" if b else "S"}, has {"A" if bits[c] else "S"})'; break
                else: new[c]=b
            if not ok:
                if TRACE: print('  '*(depth+2)+f'{s(w)} at u={u}: {why}')
                continue
            if TRACE: print('  '*(depth+2)+f'{s(w)} at u={u}: placed')
            # the owner's oldest S must be sc and sc must not be owned already (it is not, by construction)
            # OS injectivity: no other member may have oldest S = sc (true since sc unowned)
            bits2=dict(bits); bits2.update(new)
            members2=dict(members); members2[u]=w
            owned2=dict(owned); owned2[sc]=u
            newneed=[u-(i+1) for i,b in enumerate(w) if not b and (u-(i+1)) not in owned2]
            # a newly placed S might coincide with a clock already S in bits but unowned -> it is in need already or new
            need2 = rest + [c for c in newneed if c not in rest]
            # also: previously placed A bits may now have become... no, bits are fixed; but an S already in bits owned? fine
            if self.rec(bits2, members2, owned2, need2): return True
        return False

V = [w for idx,w in enumerate(minimal_words(Lv)) if idx % SHARD[1] == SHARD[0]]
print(f"lag-max {Lv}: {len(V)} words v, {len(OWNERS)} owner words (lag <= {LOWN or Lv}), memberCap={memberCap}, nodeCap={nodeCap}")
excluded=0; open_=0; capped=0
for v in V:
    srch=Search(); found, cap, nodes = srch.run(v)
    nS=sum(1 for b in v if not b); depthinfo=f"ownedS(v) max {srch.maxOwnedV}/{nS}"
    if found is not None and not cap:
        open_+=1
        desc = ' '.join(f"{u}:{s(w)}" for u,w in sorted(found.items()))
        print(f"  {s(v)}: CONSISTENT CLOSURE ({len(found)} members, {nodes} nodes): {desc}")
    elif cap:
        capped+=1; print(f"  {s(v)}: cap hit ({nodes} nodes)")
    else:
        excluded+=1; print(f"  {s(v)}: excluded ({nodes} nodes, {depthinfo})")
print(f"=> excluded {excluded}/{len(V)}, consistent closure {open_}, cap hit {capped}")
