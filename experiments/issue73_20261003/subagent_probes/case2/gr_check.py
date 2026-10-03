#!/usr/bin/env python3
"""GR = generalized Theorem R (sink extension), finite part.
Setting: M closed, r in M (any position, NOT assumed newest), own(r) private (in no other member's window),
M' = M minus r decomposes into pieces: isolated AAS ('I',x) and w1 triples ('T',b) = {b-3:AAS owns b-6, b:w1 owns b-7,
b+2:AAS owns b-1}; pieces are private in M' (no member's window contains an S owned by another piece).
Then every non-own S s of W_r is owned by a piece member: I@s+3, T@b=s+6 (bottom AAS), T@b=s+1 (top AAS), T@b=s+7 (w1).
Enumerate all (word r, own(r), piece sets) consistent at bit level; claim: only r=AAS, or r=w1 owning its oldest S
with pieces {I@-3, I@+2} (which then merge with r into a triple).
Usage: gr_check.py L [L ...]"""
import sys
from mwords import minimal_words, s
AAS='AAS'
def piece(kind,a):
    """returns (members: {clock:(word, owned S)}, bits:{clock:bool})"""
    if kind=='I':
        x=a; mem={x:('AAS',x-3)}; bits={x:True,x-1:True,x-2:True,x-3:False}
    else:
        b=a; mem={b-3:('AAS',b-6), b:('SAAAASS',b-7), b+2:('AAS',b-1)}
        bits={b-7:False,b-6:False,b-5:True,b-4:True,b-3:True,b-2:True,b-1:False,b:True,b+1:True,b+2:True}
    return mem,bits
def window(u,word): return range(u-len(word),u)
def check(L):
    out=[]
    for w in minimal_words(L):
        base={0:True}
        for i,b in enumerate(w): base[-(i+1)]=b
        S=[-(i+1) for i,b in enumerate(w) if not b]
        for own in S:
            rest=sorted([c for c in S if c!=own],reverse=True)
            def rec(i,bits,pieces,members,owned):
                # skip S already owned by chosen pieces
                while i<len(rest) and rest[i] in owned: i+=1
                if i==len(rest):
                    out.append((s(w),-own,sorted(pieces))); return
                sc=rest[i]
                for kind,a in (('I',sc+3),('T',sc+6),('T',sc+1),('T',sc+7)):
                    if (kind,a) in pieces: continue
                    mem,pb=piece(kind,a)
                    if 0 in mem: continue
                    if any(c in members for c in mem): continue
                    ok=True; b2=dict(bits)
                    for c,v in pb.items():
                        if c in b2 and b2[c]!=v: ok=False; break
                        b2[c]=v
                    if not ok: continue
                    newowned={o:u for u,(ww,o) in mem.items()}
                    if any(o in owned for o in newowned) or own in newowned: continue
                    # own(r) private: not in any piece member window
                    if any(own in window(u,ww) for u,(ww,o) in mem.items()): continue
                    # D-privacy between pieces: new members' windows vs old owned S, old members' windows vs new owned S
                    if any(o in window(u,ww) for u,(ww,_) in mem.items() for o in owned): continue
                    if any(o in window(u,ww) for u,(ww,_) in members.items() for o in newowned): continue
                    # pieces must own S's of W_r only if those S's are non-own S's of W_r (consistent with r's window bits) - bits already checked
                    m2=dict(members); m2.update(mem); o2=dict(owned); o2.update(newowned)
                    rec(i+1,b2,pieces|{(kind,a)},m2,o2)
            rec(0,base,frozenset(),{},{})
    return out
for L in map(int,sys.argv[1:]):
    res=check(L)
    print(f'L={L}: {len(minimal_words(L))} words, surviving (word, own offset, pieces): {len(res)}')
    for r in res[:20]: print('   ',r)
