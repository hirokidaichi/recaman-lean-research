#!/usr/bin/env python3
"""H-20260910-01 frozen all-word falsifier for the signed supply gap."""
import hashlib
from itertools import combinations
import json
from pathlib import Path
import subprocess


def p2_prefixes(word):
    mass = moment = 0
    for d, bit in enumerate(word, 1):
        mass += bit
        moment += d*bit
        if mass == 1 and moment == 0:
            yield d


def p2_words(d):
    for positions in combinations(range(d), (d+1)//2):
        if sum(i+1 for i in positions) != d*(d+1)//4:
            continue
        selected = set(positions)
        yield tuple(1 if i in selected else -1 for i in range(d))


def scan(d):
    count = 0
    rows = {k: {'k': k, 'contacts': 0, 'min_slack': None, 'first': None} for k in range(1,5)}
    for word in p2_words(d):
        count += 1
        assert d in set(p2_prefixes(word))
        for k, row in rows.items():
            for newlag in p2_prefixes((1,)*k+word):
                delta = newlag-d
                slack = delta*(delta-4*k)-4*k*(d-1)
                assert slack >= 0, (d,k,newlag,word,slack)
                assert newlag < d or newlag > d+4*k
                row['contacts'] += 1
                row['min_slack'] = slack if row['min_slack'] is None else min(slack,row['min_slack'])
                if row['first'] is None:
                    row['first'] = {'new_lag': newlag, 'old_word': ''.join('A' if b==1 else 'S' for b in word)}
    return {'d': d, 'old_P2_words': count, 'by_k': list(rows.values()), 'violations': 0}


def family_check(lo, hi):
    slacks = []
    for r in range(lo,hi+1):
        m = r*r-1
        word = [1]*m+[-1]*m+[1]+[-1]*(m+1)+[1]*(m+2*r)+[-1,1]+[-1]*(2*r-1)
        old = next(p2_prefixes(word))
        new = next(p2_prefixes([1]+word))
        delta = new-old
        slack = delta*(delta-4)-4*(old-1)
        assert old == len(word) and (old,new)==(4*r*r+4*r-1,4*r*r-1)
        assert slack == 8
        slacks.append(slack)
    return {'r_range': [lo,hi], 'checked': len(slacks), 'gap_slack_set': sorted(set(slacks))}


def main():
    print('protocol=H-20260910-01')
    print('source_revision='+subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
    print('script_sha256='+hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    # k=0 tests only the non-strict inequality.
    assert 3 in set(p2_prefixes((1,1,-1)))
    assert (3-3)**2 == 4*0*(3-1)
    print('BOUNDARY_k0='+json.dumps({'d':3,'d2':3,'slack':0}))
    # Periodic SAAA, with current A at both endpoints, but an intervening S.
    continuation_newest_first = (1,1,-1,1)
    assert 3 in set(p2_prefixes(continuation_newest_first+(1,1,-1)))
    assert 0 < 4*4*(3-1)
    print('NEGATIVE_CONTROL='+json.dumps({'old_lag':3,'new_lag':3,'k':4,
          'continuation_chronological':'ASAA','signed_gap_slack':-32,'role':'A_run_needed'}))
    for d in (3,7,11,15,19,23):
        print(('DISCOVERY' if d <=15 else 'HOLDOUT')+'='+json.dumps(scan(d)),flush=True)
    print('FAMILY_DISCOVERY='+json.dumps(family_check(2,8)),flush=True)
    print('FAMILY_HOLDOUT='+json.dumps(family_check(9,64)),flush=True)
    print('PASS: non-nested finite checks and reset family; universal claim needs proof')


if __name__ == '__main__':
    main()
