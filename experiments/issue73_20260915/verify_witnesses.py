#!/usr/bin/env python3
"""Independent re-derivation (no shared code with the C++ census) of the two witnesses:
  (1) p=12 word AAAASAAASSSS: donor 3 (lag 11, ssCount 3) has oldest subtraction s*=4,
      and B = {2, 5, 7} is a tight avoiding subset covering s*  => oldest-S donation fails.
  (2) p=18 word AAAASSAAAASAAASASS (E-240): donor 7 (lag 11, ssCount 2), s*=14,
      B = {2, 8, 11, 13} is tight avoiding with a lag-7 member and does NOT cover s*.
Direct summation only."""
import sys

def minimal_p2(word, u):
    p = len(word); S = 0; M = 0; cover = []; ss = 0; prev = False
    for d in range(1, 2 * p * p + 1):
        j = (u - d) % p; v = 1 if word[j] == 'A' else -1
        if v < 0:
            cover.append(j); ss += 1 if prev else 0; prev = True
        else:
            prev = False
        S += v; M += d * v
        if S == 1 and M == 0:
            return d, cover, ss
    return None

def check(word, donor, B, expect_covered):
    p = len(word)
    d0, cov0, ss0 = minimal_p2(word, donor)
    sstar = (donor - d0) % p
    assert word[sstar] == 'S'
    lags = {u: minimal_p2(word, u) for u in B}
    N = set()
    for u in B:
        N |= set(lags[u][1])
    tight = len(N) == len(B)
    covered = sstar in N
    print(f"{word} p={p} donor={donor} lag={d0} ssCount={ss0} s*={sstar} B={B} lags={{ {', '.join(f'{u}:{lags[u][0]}' for u in B)} }} N(B)={sorted(N)} tight={tight} s*_covered={covered}")
    assert tight and donor not in B and covered == expect_covered
    return True

check('AAAASAAASSSS', 3, [2, 5, 7], True)
check('AAAASSAAAASAAASASS', 7, [2, 8, 11, 13], False)
print('witnesses verified')
