#!/usr/bin/env python3
"""Check only the literal bit/charge collisions in the exploratory OBSERVED log."""

import json

cases = [
    ('AAASSSASASA', 'SASAAAASASS', -7, 3, 10),
    ('ASSAAAASSAS', 'AAASSASSSAA', -4, 7, 11),
    ('ASSAAASAASS', 'ASAASSAASAS', -5, 6, 11),
]

def p2(w):
    z = [1 if x=='A' else -1 for x in w]
    return sum(z)==1 and sum(i*x for i,x in enumerate(z,1))==0

rows=[]
for donor,cover,t,k,off in cases:
    donor_bits={-j:x for j,x in enumerate(donor,1)}
    cover_bits={t-j:x for j,x in enumerate(cover,1)}
    overlap={c:(donor_bits[c],cover_bits[c]) for c in donor_bits.keys() & cover_bits.keys()}
    assert p2(donor) and p2(cover)
    assert max(j for j,x in enumerate(donor,1) if x=='S')==off
    assert cover[k-1]=='S' and t-k==-off
    assert all(a==b for a,b in overlap.values())
    assert donor_bits.get(t,'A')=='A'
    rows.append({'donor':donor,'cover':cover,'clock':t,'charge_offset':k,
                 'oldest_offset':off,'overlap':overlap})
print(json.dumps({'kind':'literal_shortcut_collisions','rows':rows,
                  'limit':'does not recompute the shortOff selector choice'},sort_keys=True))
