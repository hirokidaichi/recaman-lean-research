"""Independent check of the H-20260911-09 counterword, by direct summation.

The claim under test was the self-strengthening   |U| + c <= |D|,  where
c = |U| - |image of the oldest-S charge| is the collision excess of the E-069 rule.
This script recomputes U, D and c from the definitions with no shared code.
"""
W18 = "AAAASSAAAASAAASSSS"
W21 = "AAASASAASAAASSSAAASSS"

def analyse(word, lag_cap_factor=4):
    p = len(word)
    s = [1 if ch == 'A' else -1 for ch in word]
    sigma = sum(s)
    assert sigma > 0, "word must have positive sign sum"
    cap = p * (p + 1)                      # the derived lag bound for positive period mass
    U, image, detail = [], set(), []
    for i in range(p):
        if s[i] < 0:
            continue
        S = M = 0
        found = None
        for d in range(1, cap + 1):
            v = s[(i - d) % p]
            S += v
            M += d * v
            if S == 1 and M == 0:
                found = d
                break
        if found is None:
            continue
        U.append(i)
        oldest = max(k for k in range(1, min(found, p) + 1) if s[(i - k) % p] < 0)
        image.add((i - oldest) % p)
        detail.append((i, found, (i - oldest) % p))
    D = [i for i in range(p) if s[i] < 0]
    c = len(U) - len(image)
    return dict(p=p, sigma=sigma, U=len(U), D=len(D), c=c,
                slack=len(D) - len(U), detail=detail, Uset=U, image=sorted(image))

for w in (W18, W21):
    r = analyse(w)
    print(w)
    print(f"  p={r['p']} sigma={r['sigma']} |U|={r['U']} |D|={r['D']} "
          f"collision excess c={r['c']} slack=|D|-|U|={r['slack']}")
    print(f"  supplied phases {r['Uset']}  oldest-S image {r['image']}")
    print("  (phase, minimal lag, oldest-S target):", r['detail'])
    verdict = "slack >= c HOLDS" if r['slack'] >= r['c'] else "slack >= c FAILS"
    print(f"  => {verdict};  |U| <= |D| {'holds' if r['U'] <= r['D'] else 'FAILS'}")
    print()
