#!/usr/bin/env python3
"""Independent checker (written separately from enc.py; uses only the definitions in the briefing).

check(sigma, members) where sigma is a string over {A,S} indexed by clock 0.., members a list of
(b, t, own).  Returns dict with validity and diagnostics: P2 of each window via the walk F, M1, M1', M2,
coverage counts, Claim-P status (exists S covered once), SC status (own == t for all), lags.
Also: brute(N, LMAX) enumerates all (sigma, member/window set) closures with a window starting at 0 by
brute force (for cross-validation of enc.py counts).
"""
import sys, json, itertools

def walk(sig):
    F = [0]
    for ch in sig:
        F.append(F[-1] + (1 if ch == 'A' else -1))
    return F

def is_p2(F, sig, t, b):
    L = b - t
    if L < 1 or sig[b] != 'A':
        return False
    h = F[t]
    if F[b] != h + 1:
        return False
    return sum(F[u] - h for u in range(t + 1, b + 1)) == 0

def check(sig, members):
    F = walk(sig)
    res = {'ok': True, 'errors': []}
    def err(e):
        res['ok'] = False; res['errors'].append(e)
    bs = [b for b, t, o in members]
    if len(set(bs)) != len(bs):
        err('duplicate member')
    for b, t, o in members:
        if not is_p2(F, sig, t, b):
            err(f'window [{t},{b-1}] of {b} not P2')
        if not (t <= o <= b - 1) or sig[o] != 'S':
            err(f'own({b})={o} invalid')
    owns = [o for b, t, o in members]
    if len(set(owns)) != len(owns):
        err('own not injective')
    cov = {}
    for b, t, o in members:
        for c in range(t, b):
            cov[c] = cov.get(c, 0) + 1
    coveredS = sorted(c for c in cov if sig[c] == 'S')
    for c in coveredS:
        if c not in owns:
            err(f'covered S {c} unowned')
    res['coveredS'] = coveredS
    res['cov'] = {c: cov[c] for c in coveredS}
    res['claimP_holds'] = any(cov[c] == 1 for c in coveredS)
    res['SC_holds'] = all(o == t for b, t, o in members)
    res['lags'] = sorted(b - t for b, t, o in members)
    res['F'] = F
    return res

def has_matching(sig, wins):
    """wins: list of (b,t). Is there an injective own map hitting every covered S (M1,M1',M2)?
    Since every covered S must be owned and |owners| = |members|, need perfect matching members <-> covered S."""
    cov = set()
    for b, t in wins:
        cov.update(c for c in range(t, b) if sig[c] == 'S')
    if len(cov) != len(wins):
        return False
    cov = sorted(cov)
    idx = {c: i for i, c in enumerate(cov)}
    match = {}
    def aug(i, seen):
        b, t = wins[i]
        for c in range(t, b):
            if sig[c] == 'S' and c not in seen:
                seen.add(c)
                if c not in match or aug(match[c], seen):
                    match[c] = i
                    return True
        return False
    return all(aug(i, set()) for i in range(len(wins)))

def brute(N, LMAX):
    cnt = 0
    sols = []
    for bits in range(1 << N):
        sig = ''.join('A' if (bits >> c) & 1 else 'S' for c in range(N))
        F = walk(sig)
        cand = {}
        for b in range(N):
            for L in range(3, LMAX + 1, 4):
                if b - L >= 0 and is_p2(F, sig, b - L, b):
                    cand.setdefault(b, []).append(b - L)
        keys = sorted(cand)
        # choose for each candidate member either absent or one of its windows
        opts = [[None] + cand[b] for b in keys]
        for ch in itertools.product(*opts):
            wins = [(b, t) for b, t in zip(keys, ch) if t is not None]
            if not wins or min(t for b, t in wins) != 0:
                continue
            if has_matching(sig, wins):
                cnt += 1
                sols.append((sig, tuple(wins)))
    return cnt, sols

if __name__ == '__main__':
    if sys.argv[1] == 'brute':
        N, LMAX = int(sys.argv[2]), int(sys.argv[3])
        cnt, sols = brute(N, LMAX)
        print('brute count', cnt)
        if len(sys.argv) > 4:
            json.dump(sols, open(sys.argv[4], 'w'))
    else:
        d = json.load(open(sys.argv[1]))
        mem = [(m['b'], m['t'], m['own']) for m in d['members']]
        r = check(d['sigma'], mem)
        r.pop('F')
        print(json.dumps(r))
