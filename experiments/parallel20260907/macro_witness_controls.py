#!/usr/bin/env python3
"""Recorded post-holdout proof-heuristic controls, OBSERVED, not new holdout."""
import hashlib
import pathlib
import random
import subprocess
from macro_periodic_supply import signatures

print('protocol=H-20260907-07 post-holdout proof-heuristic diagnostics; OBSERVED')
print('source_revision=' + subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
print('script_sha256=' + hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest())
for spelling, phase, name in [('SSAAAASAAAAA',7,'longest_A_run_start'), ('SSSASASAAAA',3,'longest_S_run_then_A')]:
    word=tuple(1 if x=='A' else -1 for x in spelling)
    sig=dict(signatures(word))
    print('failed_selection=%s word=%s phase0=%d supplied_lags=%r' % (name,spelling,phase,sig[phase]))
    assert sig[phase]

rng=random.Random(2026090707)
checked=0
counter=None
for p in range(13,81):
    for _ in range(200):
        word=tuple(rng.choice((-1,1)) for _ in range(p))
        if sum(word)<=0:continue
        W=[sum(i*word[(t-i)%p] for i in range(1,p+1)) for t in range(p)]
        phases=[t for t in range(p) if W[t]==max(W)]
        hits={}
        for t in phases:
            assert word[t]==1
            s=m=0
            hit=[]
            for d in range(1,p*(p+1)+1):
                s+=word[(t-d)%p]; m+=d*word[(t-d)%p]
                if s==1 and m==0:hit.append(d)
            hits[t]=hit
        checked+=1
        if any(hits.values()):
            counter=(''.join('A' if e>0 else 'S' for e in word),hits,max(W))
            break
    if counter:break
print('max_W_selection_random_seed=2026090707 period_range=[13,80] samples_per_period=200 positive_words_checked=%d counter=%r' % (checked,counter))
