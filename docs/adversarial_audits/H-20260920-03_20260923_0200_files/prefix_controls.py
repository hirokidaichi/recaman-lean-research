#!/usr/bin/env python3
"""Literal entrance and negative controls for the H-03 equality."""
from independent_prefix_check import neighborhood, p2, window


def cycle(word):
    return tuple(bit == "A" for bit in word)


c = cycle("SAAA")
b = 3
short = window(c, b, 3)
long = window(c, b, 4)
n3 = neighborhood(c, [(b, 3)])
n4 = neighborhood(c, [(b, 4)])
n0 = neighborhood(c, [(b, 0)])
assert c[b] and b < len(c)
assert p2(short) and not p2(long)
assert n3 == n4 == frozenset({0}) and len(n4) == 1
assert n0 == frozenset() and n0 != n4
print("actual_lean_domain", dict(period=4, cycle="SAAA", B=[3], m=3, lag=4,
    past_m="".join("A" if x else "S" for x in short),
    past_lag="".join("A" if x else "S" for x in long),
    P2_m=p2(short), P2_lag=p2(long), N_m=sorted(n3), N_lag=sorted(n4), tight=True))
print("remove_P2_m", dict(period=4, cycle="SAAA", B=[3], m=0, lag=4,
    N_m=sorted(n0), N_lag=sorted(n4), tight=True, equality=n0 == n4))

c = cycle("AASSAAASSSSSSSS")
short = window(c, 6, 3)
long = window(c, 6, 7)
n3 = neighborhood(c, [(6, 3)])
n7 = neighborhood(c, [(6, 7)])
assert c[6] and p2(short) and p2(long)
assert n3 == frozenset({3}) and n7 == frozenset({2, 3, 14})
assert len(n7) != 1
print("remove_tightness", dict(period=15, cycle="AASSAAASSSSSSSS", B=[6], m=3, lag=7,
    P2_m=p2(short), P2_lag=p2(long), N_m=sorted(n3), N_lag=sorted(n7),
    tight=False, equality=n3 == n7))
