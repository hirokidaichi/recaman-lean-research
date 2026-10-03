#!/usr/bin/env python3
"""Independent checker for a CONSISTENT closure printed by mcs (C++).
Input lines (from the mcs output):  'own offset K: CONSISTENT (...): u1:W1 u2:W2 ...'  followed by
'own map (S->owner): s1->u1 s2->u2 ...'.  Checks bit consistency, minimality of every member window
(recomputed from the assembled bits), M1 (own(b) in N([b])), M1' (own injective), M2 (every S in every
member window is owned)."""
import sys, re

def p2(ws):
    mass = sum(1 if c == 'A' else -1 for c in ws)
    mom = sum((i + 1) * (1 if c == 'A' else -1) for i, c in enumerate(ws))
    return mass == 1 and mom == 0

def min_window(bits, b):
    """shortest P2 prefix of the backward word at b, from the assembled bits (None if it runs off the known bits)"""
    ws = ''
    d = 1
    while (b - d) in bits:
        ws += bits[b - d]
        if p2(ws): return ws
        d += 1
    return None

def check(members, own):
    errs = []
    bits = {}
    def put(c, x):
        if c in bits and bits[c] != x: errs.append(f'bit conflict at {c}')
        bits[c] = x
    for u, w in members.items():
        put(u, 'A')
        for i, c in enumerate(w): put(u - (i + 1), c)
    for u, w in members.items():
        mw = min_window(bits, u)
        if mw != w: errs.append(f'member {u}: minimal window from bits is {mw}, claimed {w}')
        if not p2(w) or any(p2(w[:d]) for d in range(1, len(w))): errs.append(f'member {u}: {w} not minimal P2')
    N = {u: {u - (i + 1) for i, c in enumerate(w) if c == 'S'} for u, w in members.items()}
    owner_of = {}
    for s, u in own.items():
        if u not in members: errs.append(f'owner {u} of {s} is not a member')
        elif s not in N[u]: errs.append(f'M1: own({u})={s} not in N([{u}])')
        owner_of.setdefault(u, []).append(s)
    for u in members:
        if len(owner_of.get(u, [])) != 1: errs.append(f'M1: member {u} owns {owner_of.get(u, [])}')
    if len(set(own.values())) != len(own): errs.append("M1': own not injective")
    allS = set().union(*N.values()) if N else set()
    for s in sorted(allS):
        if s not in own: errs.append(f'M2: S at {s} not owned')
    return errs

if __name__ == '__main__':
    txt = open(sys.argv[1]).read().splitlines()
    n = 0; bad = 0
    for i, line in enumerate(txt):
        m = re.search(r'CONSISTENT \((\d+) members, \d+ nodes\): (.*)$', line)
        if not m: continue
        members = {int(a): b for a, b in (t.split(':') for t in m.group(2).split())}
        om = re.search(r'own map \(S->owner\):(.*)$', txt[i + 1])
        own = {int(a): int(b) for a, b in (t.split('->') for t in om.group(1).split())}
        errs = check(members, own); n += 1
        print(('OK   ' if not errs else 'FAIL ') + line.strip()[:120] + ('' if not errs else '  ' + '; '.join(errs)))
        bad += bool(errs)
    print(f'checked {n} closures, {bad} failed')
