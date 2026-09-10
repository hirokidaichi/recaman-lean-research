#!/usr/bin/env python3
"""H-20260910-28 independent semantic audit; finite regression, not proof."""
import hashlib
import itertools
import json
from pathlib import Path
import subprocess


def data(w):
    mass = moment = ss = 0
    hits = []
    previous = 1
    for i, s in enumerate(w, 1):
        mass += s
        moment += i * s
        ss += s == previous == -1
        previous = s
        if mass == 1 and moment == 0:
            hits.append(i)
    return mass, moment, ss, hits


def parse(s):
    return tuple(1 if c == 'A' else -1 for c in s)


def main():
    print('protocol=H-20260910-28 independent finite-word semantic regression')
    print('source_revision=' + subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip())
    print('source_sha256=' + hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    print('command=python3 experiments/issue73_20260910/endpoint/finite_verifier.py')
    print('range=all binary words length 0..19; all masses; NoSAAS not assumed')
    total = 0
    for n in range(20):
        eligible = ended_a = p2 = shortened = zero_negative = 0
        for w in itertools.product((-1, 1), repeat=n):
            m, moment, ss, hits = data(w)
            total += 1
            if ss > 1:
                continue
            eligible += 1
            if w and w[-1] == 1:
                ended_a += 1
                assert m >= -ss, w
                assert moment + n >= 2, w
                if m == 1 and moment <= 0:
                    assert any(w[d-1] == -1 for d in hits), w
            if ss == 0 and m == 1 and moment <= 0:
                zero_negative += 1
                assert any(w[d-1] == -1 for d in hits), w
            if m == 1 and moment == 0:
                p2 += 1
                assert any(w[d-1] == -1 for d in hits), w
                assert w[hits[0]-1] == -1, w
                shortened += w[-1] == 1
        print('REGRESSION=' + json.dumps(dict(length=n, words=2**n, low_SS=eligible,
              ending_A=ended_a, P2=p2, A_ended_P2=shortened, zero_SS_nonpositive=zero_negative,
              violations=0)), flush=True)
    controls = [
        ('drop_current_A', 'AASS', 'AAS'),
        ('allow_two_SS', 'AASASASASSSA', 'AAS'),
    ]
    for name, v, u in controls:
        vm, vM, vss, _ = data(parse(v))
        nm, nM, nss, nhits = data(parse(v+u))
        assert (nm, nM) == (1, 0) and data(parse(u))[:2] == (1, 0)
        assert vm == 0 and vM == -len(v)
        print('CONTROL=' + json.dumps(dict(name=name, intervening=v, older=u,
              newer=v+u, intervening_ends_A=v[-1]=='A', SS=nss,
              newer_P2_prefixes=nhits)))
    for s, expected_ss, expected_hits in [('AASASSA', 1, [3, 7]), ('SAAASAASSSA', 2, [11])]:
        m, M, ss, hits = data(parse(s))
        assert (m, M, ss, hits) == (1, 0, expected_ss, expected_hits)
        print('END_A_CONTROL=' + json.dumps(dict(word=s, SS=ss, P2_prefixes=hits,
              NoSAAS='SAAS' not in s)))
    # Former period-13 union-map collision: the endpoint map separates it.
    s = 'SSAAASASASAAA'
    records = []
    for t in (11, 12):
        w = parse(''.join(s[(t-d) % len(s)] for d in range(1, 2*len(s)+1)))
        d = data(w)[3][0]
        records.append(dict(phase=t, minimum_lag=d, endpoint=(t-d) % len(s)))
    assert records == [dict(phase=11, minimum_lag=11, endpoint=0),
                       dict(phase=12, minimum_lag=3, endpoint=9)]
    print('OLD_COLLISION_REPAIRED=' + json.dumps(dict(period=13, word=s, sources=records)))
    print('PASS: ' + str(total) + ' finite words; original predicates, prefix normalization, and controls agree')


if __name__ == '__main__':
    main()
