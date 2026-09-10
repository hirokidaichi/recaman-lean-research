#!/usr/bin/env python3
"""Frozen H-20260909-05. Uses exact tail counts and direct word replay."""
import hashlib
from itertools import combinations
import json
from pathlib import Path
import subprocess


def sig(w):
    s = h = 0
    for i, ch in enumerate(w, 1):
        e = 1 if ch == 'A' else -1
        s += e
        h += i*e
    return s, h


def old_word(d):
    m = (d+1)//4
    return 'A'*m+'S'*(m-1)+'A'+'S'*m+'A'*(m-1)


def scan(d, k, max_tail):
    w = old_word(d)
    assert len(w) == d and sig(w) == (1,0)
    tested = contacts = 0
    smallest_tail = None
    min_slack = None
    witness = None
    for ell in range(k, max_tail+1):
        if (ell-k) % 2:
            continue
        a_count = (ell-k)//2
        for pos in combinations(range(1,ell+1), a_count):
            tested += 1
            moment = 2*sum(pos)-ell*(ell+1)//2
            if 2*moment != 2*k*(d+k)-k*(k+3):
                continue
            positions = set(pos)
            v = ''.join('A' if i in positions else 'S' for i in range(1,ell+1))
            assert sig('A'*k+w+v) == (1,0)
            contacts += 1
            delta = k+ell
            slack = delta*(delta-4*k)-4*k*(d-1)
            assert slack >= 0 and delta > 4*k, (w,k,v,slack)
            if min_slack is None or slack < min_slack:
                min_slack, witness = slack, v
            smallest_tail = ell if smallest_tail is None else min(smallest_tail,ell)
    return {'d': d, 'k': k, 'max_tail': max_tail, 'tails_tested': tested,
            'nested_P2': contacts, 'smallest_tail': smallest_tail,
            'min_slack': min_slack, 'witness_tail': witness, 'violations': 0}


def main():
    print('protocol=H-20260909-05')
    print('source_revision='+subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
    print('script_sha256='+hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    assert sig('ASA') == (1,2) and sig('A'+'ASA'+'SSA') == (1,0)
    assert sig('AAS') == (1,0) and sig('A'+'AAS'+'SSA') == (1,-2)
    print('CONTROLS=both moment assumptions independently necessary')
    for d in (3,7,11):
        for k in (1,2,3):
            print('DISCOVERY='+json.dumps(scan(d,k,15)), flush=True)
    for d in (15,19):
        for k in (1,2,3):
            print('HOLDOUT='+json.dumps(scan(d,k,19)), flush=True)
    print('PASS: exact finite nested-window checks; not the all-length proof')


if __name__ == '__main__':
    main()
