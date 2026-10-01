#!/usr/bin/env python3
"""H-20260915-19, part 1 (bit-level, no periodicity): which minimal lag-7 P2 windows can cover the
oldest subtraction s* of a minimal SS=2 lag-11 donor window?  Direct enumeration over all 2^11 and
2^7 words; convention past e u d = [e(u-1), ..., e(u-d)], True = A.  Registry E-347."""
import itertools

def p2(w):
    S = sum(1 if b else -1 for b in w); M = sum((i + 1) * (1 if b else -1) for i, b in enumerate(w))
    return S == 1 and M == 0
def minimal(w): return p2(w) and not any(p2(w[:d]) for d in range(1, len(w)))
def ss(w): return sum(1 for i in range(len(w) - 1) if not w[i] and not w[i + 1])
def txt(w): return ''.join('A' if b else 'S' for b in w)

donors = [w for w in itertools.product([True, False], repeat=11) if minimal(w) and ss(w) == 2]
lag7 = [w for w in itertools.product([True, False], repeat=7) if minimal(w)]
print('minimal lag-11 ss=2 donor words:', [txt(w) for w in donors])
print('minimal lag-7 words:', [txt(w) for w in lag7])

def bit(w, pos):            # donor occupies pos in [-11,-1] relative to u0: e(u0-1-j) = w[j]
    j = -pos - 1
    return w[j] if 0 <= j <= 10 else None

total = 0
for w in donors:
    off = max(j + 1 for j in range(11) if not w[j])      # oldest subtraction offset
    sstar = -off
    hits = []
    for v in lag7:
        for k in range(7):                                # v[k] = e(u-1-k) covers s*  =>  u = s*+1+k
            if v[k]:
                continue
            u = sstar + 1 + k
            ok = bit(w, u) is not False                   # u must be an addition phase
            for m in range(7):
                b = bit(w, u - 1 - m)
                if b is not None and b != v[m]:
                    ok = False
            if ok:
                hits.append((txt(v), u, k + 1))
    total += len(hits)
    print(f'{txt(w)} s*offset={off} covering lag-7 windows (word, u-u0, offset of s* in window): {hits}')
print('total compatible configurations:', total)
