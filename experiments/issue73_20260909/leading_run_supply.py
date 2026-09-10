#!/usr/bin/env python3
"""Frozen H-20260909-03 falsifier. Words and prefixes are newest-first."""
import hashlib
from itertools import combinations
import json
from pathlib import Path
import subprocess


def signature(w):
    e = [1 if c == 'A' else -1 for c in w]
    return sum(e), sum(i * c for i, c in enumerate(e, 1))


def family(m):
    return 'A' * m + 'S' * (m-1) + 'A' + 'S' * m + 'A' * (m-1)


def scan(d):
    count = active = 0
    histogram = {}
    for positions in combinations(range(1, d+1), (d+1)//2):
        if sum(positions) != d*(d+1)//4:
            continue
        count += 1
        leading = 0
        for pos in positions:
            if pos != leading+1:
                break
            leading += 1
        histogram[leading] = histogram.get(leading, 0)+1
        if leading >= 3:
            active += 1
            assert 4*leading <= d+1, (d, positions, leading)
    return {'d': d, 'P2_words': count, 'leading_ge3': active,
            'leading_histogram': histogram, 'violations': 0}


def verify_family(lo, hi):
    digest = hashlib.sha256()
    for m in range(lo, hi+1):
        w = family(m)
        assert len(w) == 4*m-1
        assert w.startswith('A'*m+'S')
        hits = []
        balance = moment = 0
        for d, ch in enumerate(w, 1):
            e = 1 if ch == 'A' else -1
            balance += e
            moment += d*e
            if (balance, moment) == (1, 0):
                hits.append(d)
        assert hits == [4*m-1], (m, hits)
        row = json.dumps({'m': m, 'word': w, 'hits': hits}, sort_keys=True)
        digest.update((row+'\n').encode())
    return {'range': [lo, hi], 'checked': hi-lo+1,
            'violations': 0, 'rows_sha256': digest.hexdigest()}


def main():
    print('protocol=H-20260909-03')
    print('source_revision='+subprocess.check_output(['git','rev-parse','HEAD'], text=True).strip())
    print('script_sha256='+hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    for w, m, sig, role in [('AAS', 2, (1,0), 'm_ge3_needed'),
                           ('AAASS', 3, (1,-3), 'moment_needed'),
                           ('AAAASSSA', 3, (2,0), 'sum_needed')]:
        assert signature(w) == sig
        assert len(w)+1 < 4*m
        print('CONTROL='+json.dumps({'word': w, 'm': m, 'signature': sig, 'role': role}))
    for d in (3,7,11,15):
        print('DISCOVERY='+json.dumps(scan(d)), flush=True)
    print('HOLDOUT='+json.dumps(scan(19)), flush=True)
    print('FAMILY_DISCOVERY='+json.dumps(verify_family(3,16)), flush=True)
    print('FAMILY_HOLDOUT='+json.dumps(verify_family(17,128)), flush=True)
    print('PASS: frozen finite checks; not a proof of the all-m claim')


if __name__ == '__main__':
    main()
