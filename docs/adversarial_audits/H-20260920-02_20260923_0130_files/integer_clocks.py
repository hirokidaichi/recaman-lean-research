#!/usr/bin/env python3
"""Move one nonminimal donor witness to exact negative and boundary clocks."""

import json

base = 'AASSSAAAASSSS'
p = len(base)

def sign_at(t, shift):
    return base[(t-shift) % p]

rows = []
for u0 in (-101, -1, 0, 1, 101):
    shift = u0 - 10
    B = (7 + shift) % p
    window = ''.join(sign_at(u0-j, shift) for j in range(1, 12))
    b_window = ''.join(sign_at(B-j, shift) for j in range(1,4))
    N = sorted({(B-j)%p for j in range(1,4) if sign_at(B-j, shift)=='S'})
    off = max(j for j,x in enumerate(window,1) if x=='S')
    s = (u0-off)%p
    assert window=='SAAAASSSAAS' and b_window=='AAS' and len(N)==1 and s not in N
    rows.append({'u0':u0,'cycle':''.join(sign_at(t,shift) for t in range(p)),
                 'B':[B],'N':N,'donor_window':window,'oldest_offset':off,
                 'oldest_phase':s,'current':sign_at(u0,shift)})
print(json.dumps({'kind':'exact_integer_clocks','rows':rows},sort_keys=True))
