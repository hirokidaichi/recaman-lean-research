#!/usr/bin/env python3
"""Verify the frozen literal H-04 countermodels without importing the discovery code."""
import itertools
import json


def verify(cycle, donor, assignments):
    period = len(cycle)
    def sign(t):
        return 1 if cycle[t % period] == "A" else -1
    def p2(t, d):
        return sum(sign(t-i) for i in range(1, d+1)) == 1 and sum(i*sign(t-i) for i in range(1, d+1)) == 0
    def neighborhood(t, d):
        return { (t-i) % period for i in range(1, d+1) if sign(t-i) < 0 }
    assert all(sign(t+period) == sign(t) for t in range(-3*period, 3*period))
    assert sum(map(sign, range(period))) > 0 and sign(donor) > 0 and p2(donor, 15)
    assert sum(sign(donor-i) < 0 and sign(donor-i-1) < 0 for i in range(1, 15)) == 2
    prefixes = [d for d in range(1, 15) if p2(donor, d)]
    assert prefixes, "The discovered witness is deliberately a nonminimal donor"
    sstar = (donor-max(i for i in range(1, 16) if sign(donor-i) < 0)) % period
    N = set()
    for u, d in assignments.items():
        assert 0 <= u < period and u != donor and sign(u) > 0
        assert d <= 11 and p2(u, d) and all(not p2(u, f) for f in range(1, d))
        N |= neighborhood(u, d)
    assert len(assignments) == len(N) and sstar in N
    assert len(assignments) > len(N-{sstar})
    full = {}
    for u in range(period):
        if sign(u) < 0:
            continue
        for d in range(1, period*(period+1)+1):
            if p2(u, d):
                full[u] = (d, neighborhood(u, d))
                break
    for size in range(len(full)+1):
        for B in itertools.combinations(full, size):
            covered = set().union(*(full[b][1] for b in B))
            assert len(B) <= len(covered), (cycle, B)
    return dict(cycle=cycle, period=period, donor=donor, proper_P2_prefixes=prefixes,
                oldest=sstar, B=assignments, N=sorted(N), deleted_N=sorted(N-{sstar}),
                all_supply={u:[d, sorted(n)] for u, (d,n) in full.items()},
                all_subsets_hall=True, result="REFUTED_LENGTH15_NONMINIMAL_DONOR")


for args in (("SAAASSSASASASAAA", 15, {3:3}),
             ("SSAAAASAAASSSASASASAAA", 21, {4:3, 7:7, 9:3})):
    print(json.dumps(verify(*args), sort_keys=True), flush=True)
