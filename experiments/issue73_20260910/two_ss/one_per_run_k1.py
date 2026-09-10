#!/usr/bin/env python3
"""Search a k=1 one-per-run counterexample inside min SS=2 words.

If W is min SS=2 and starts with A, the previous source in the same run
has past W[1:]. If that past's minimum P2 also has SS=2, we have two
consecutive SS=2 sources. Discovery lengths 11..19, holdout 23..27.
"""
from __future__ import annotations

import hashlib
import itertools
import json
import subprocess
from collections import Counter
from pathlib import Path


def data(w):
    mass = moment = ss = 0
    hits = []
    prev = 1
    for i, s in enumerate(w, 1):
        mass += s
        moment += i * s
        if s == prev == -1:
            ss += 1
        prev = s
        if mass == 1 and moment == 0:
            hits.append((i, ss))
    return mass, moment, ss, hits


def to_str(w):
    return ''.join('A' if s == 1 else 'S' for s in w)


def scan_length(n):
    stats = Counter()
    examples = []
    for bits in itertools.product((-1, 1), repeat=n):
        mass, moment, ss, hits = data(bits)
        if mass != 1 or moment != 0 or ss != 2 or hits[0][0] != n:
            continue
        stats['min_ss2'] += 1
        if bits[0] != 1:
            stats['start_S'] += 1
            continue
        stats['start_A'] += 1
        tail = bits[1:]
        tm, tM, tss, thits = data(tail)
        if not thits:
            stats['tail_no_P2'] += 1
            continue
        d0, ss0 = thits[0]
        stats['tail_min_ss_' + str(ss0)] += 1
        if ss0 == 2:
            stats['k1_counterexample'] += 1
            examples.append(dict(
                W=to_str(bits), tail_min_d=d0, tail_min_ss=ss0,
                tail_prefix=to_str(tail[:d0]),
            ))
    return stats, examples


def main():
    print('protocol=H-20260910-32 k=1 one-per-run word search')
    print('source_revision=' + subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip())
    print('source_sha256=' + hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    print('command=python3 experiments/issue73_20260910/two_ss/one_per_run_k1.py')
    for n in range(11, 24, 4):
        stats, examples = scan_length(n)
        print('LENGTH=' + json.dumps(dict(n=n, holdout=n >= 23, **stats),
                                     sort_keys=True), flush=True)
        for ex in examples[:8]:
            print('COUNTER=' + json.dumps(ex))


if __name__ == '__main__':
    main()
