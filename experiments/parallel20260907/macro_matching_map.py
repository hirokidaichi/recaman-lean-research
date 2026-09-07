#!/usr/bin/env python3
"""Falsify the oldest-S/minimum-lag map fixed in H-20260907-07."""
import hashlib
import itertools
import pathlib
import subprocess
from macro_periodic_supply import signatures

print('protocol=H-20260907-07 minimum-lag oldest-S injection falsifier')
print('source_revision='+subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
print('script_sha256='+hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest())
checked=0
for p in range(1,17):
    for word in itertools.product((-1,1),repeat=p):
        if sum(word)<=0:continue
        checked+=1
        pairs=[]; images={}; collision=None
        for t, lags in signatures(word):
            if not lags:continue
            d=min(lags)
            i=max(i for i in range(1,d+1) if word[(t-i)%p]==-1)
            s=(t-i)%p
            pairs.append((t,d,i,s))
            if s in images:
                collision=(images[s],(t,d,i,s))
                break
            images[s]=(t,d,i,s)
        if collision:
            print('first_collision period=%d word=%s sum=%d checked=%d' % (p,''.join('A' if e>0 else 'S' for e in word),sum(word),checked))
            print('tuple_fields=(addition_phase0,minimum_lag,oldest_S_offset,image_phase0)')
            print('collision=%r' % (collision,))
            for t,d,i,s in collision:
                bits=[word[(t-j)%p] for j in range(1,d+1)]
                print('phase=%d backward_signs=%r sign_sum=%d moment=%d' % (t,bits,sum(bits),sum(j*e for j,e in enumerate(bits,1))))
            domains={t:sorted({(t-i)%p for i in range(1,min(ds)+1) if word[(t-i)%p]==-1}) for t,ds in signatures(word) if ds}
            owner={}
            def augment(t,seen):
                for s in domains[t]:
                    if s in seen:continue
                    seen.add(s)
                    if s not in owner or augment(owner[s],seen):
                        owner[s]=t
                        return True
                return False
            passes=all(augment(t,set()) for t in domains)
            print('full_minimum_lag_S_domains=%r' % domains)
            print('matching_on_this_counterexample=%s witness_A_to_S=%r' % (passes,sorted((t,s) for s,t in owner.items())))
            raise SystemExit(0)
    print('period=%d no_collision_so_far cumulative_words=%d' % (p,checked),flush=True)
print('no collision through period16; no all-period claim')
