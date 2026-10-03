#!/usr/bin/env python3
"""Independent regressions for frozen E-240, E-069, and E-345 literals."""

import json


def data(word, t, d):
    p = len(word)
    w = "".join(word[(t-i) % p] for i in range(1, d+1))
    signs = [1 if c == "A" else -1 for c in w]
    return w, sum(signs), sum(i*s for i, s in enumerate(signs, 1))


def oldest(word, t, d):
    w, _, _ = data(word, t, d)
    return (t - max(i for i, c in enumerate(w, 1) if c == "S")) % len(word)


def neighbors(word, lags):
    p = len(word)
    return sorted({(u-i) % p for u, d in lags.items()
                   for i in range(1, d+1) if word[(u-i) % p] == "S"})


e240 = "AAAASSAAAASAAASASS"
b240 = {2: 3, 8: 3, 11: 7, 13: 3}
n240 = neighbors(e240, b240)
assert len(e240) == 18 and len(n240) == len(b240) == 4
assert n240 == [4, 5, 10, 17]
assert all(data(e240, u, d)[1:] == (1, 0) for u, d in b240.items())
assert data(e240, 7, 11)[1:] == (1, 0)
assert oldest(e240, 7, 11) == 14 and 14 not in n240

e069 = "SSSSAAAASAAA"
e069_lags = {}
for u in (7, 11):
    for d in range(1, len(e069)*(len(e069)+1)+1):
        if data(e069, u, d)[1:] == (1, 0):
            e069_lags[u] = d
            break
assert e069_lags == {7: 11, 11: 3}
assert oldest(e069, 7, 11) == oldest(e069, 11, 3) == 8

e345 = "AAAASAAASSSS"
b345 = {2: 3, 5: 7, 7: 3}
n345 = neighbors(e345, b345)
w345, m345, j345 = data(e345, 3, 11)
ss345 = sum(w345[i:i+2] == "SS" for i in range(len(w345)-1))
assert len(e345) == 12 and (m345, j345) == (1, 0) and ss345 == 3
assert all(data(e345, u, d)[1:] == (1, 0) for u, d in b345.items())
assert len(n345) == len(b345) and oldest(e345, 3, 11) == 4 and 4 in n345

print(json.dumps({
    "E-240": {"word": e240, "B": b240, "N": n240, "donor": 7,
              "oldest": 14, "oldest_avoided": True, "non_AAS_member": 11},
    "E-069": {"word": e069, "lags": e069_lags, "shared_oldest": 8},
    "E-345": {"word": e345, "donor": 3, "window": w345,
              "ss_count": ss345, "B": b345, "N": n345,
              "oldest": 4, "oldest_covered": True},
}, sort_keys=True))
