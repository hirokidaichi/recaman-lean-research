#!/usr/bin/env python3
"""Frozen local falsifier for H-20260909-06; no periodic horizon census."""
import hashlib
import json
from pathlib import Path
import subprocess
from sharp_partitions import partitions


def p2(word):
    return sum(word) == 1 and sum(i*b for i, b in enumerate(word, 1)) == 0


def check(m, limit):
    count = contacts = 0
    for parts in partitions(m):
        lam = parts+(0,)*(m-len(parts))
        apos = set(range(1, m+1)) | {3*m+i-lam[i] for i in range(m)}
        e = {-i: 1 if i in apos else -1 for i in range(1, 4*m)}
        e[0] = 1
        q = -m-2
        assert e[q] == e[q+1] == -1
        assert all(e[x] == 1 for x in range(q+2, 1))
        assert p2([e[-i] for i in range(1, 4*m)])
        pairs = []
        for j in range(1, limit+1):
            u = q+j
            if e[u] == -1:
                continue
            for d in range(1, limit+1):
                if p2([e[u-i] for i in range(1, d+1)]):
                    pairs.append((j, d))
                    assert (j, d) == (4, 3), (limit, m, parts, j, d)
                    assert u-3 == q+1
        assert pairs == [(4, 3)]
        contacts += len(pairs)
        count += 1
    return {'L': limit, 'm': m, 'sharp_words': count,
            'short_contacts': contacts, 'protected_S_collisions': 0}


def negative_control(m, future):
    w = [1]*m+[-1]*(m-1)+[1]+[-1]*m+[1]*(m-1)
    e = {-i: b for i, b in enumerate(w, 1)}
    e.update(dict(enumerate([1]+future)))
    u = len(future)
    offsets = [i for i in range(1, 12) if e[u-i] == -1]
    lags = [d for d in range(1, 12) if p2([e[u-i] for i in range(1, d+1)])]
    assert p2(w) and e[u] == 1
    assert offsets == [1, 2, 9, 10, 11] and lags == [11]
    # This exact S-offset type has charge 10 in LagElevenSupply.lean.
    assert u-10 == -m-2
    return {'m': m, 'future_after_t0': ''.join('A' if b == 1 else 'S' for b in future),
            'u': u, 'min_lag': 11, 'S_offsets': offsets, 'phi11_offset': 10,
            'collision_q': u-10}


def main():
    print('protocol=H-20260909-06')
    print('source_revision='+subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip())
    print('script_sha256='+hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    for m, future in [(4, [1, -1, -1, 1]), (5, [-1, -1, 1])]:
        print('NEGATIVE_CONTROL='+json.dumps(negative_control(m, future)))
    for limit in (11, 15):
        for m in range(limit+1, 25):
            stage = 'DISCOVERY' if m <= limit+4 else 'HOLDOUT'
            print(stage+'='+json.dumps(check(m, limit)), flush=True)
    print('PASS: only lag-3 contacts, charged to q+1; no protected-S collision')


if __name__ == '__main__':
    main()
