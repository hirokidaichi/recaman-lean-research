#!/usr/bin/env python3
"""Case 5: later SS=2 window is A plus a proper prefix of an earlier SS=2 window."""
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


def min_ss2_words(n):
    out = []
    for bits in itertools.product((-1, 1), repeat=n):
        mass, moment, ss, hits = data(bits)
        if mass == 1 and moment == 0 and ss == 2 and hits and hits[0][0] == n:
            out.append(bits)
    return out


def main():
    print('protocol=H-20260910-32 case5 later=A++prefix(earlier)')
    print('source_revision=' + subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip())
    print('source_sha256=' + hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    print('command=python3 experiments/issue73_20260910/two_ss/one_per_run_k1_extend.py')
    words = {}
    for n in range(11, 24, 4):
        words[n] = min_ss2_words(n)
        print('WORDS=' + json.dumps(dict(n=n, count=len(words[n]))), flush=True)
    hits = Counter()
    examples = []
    for n, olds in words.items():
        for old in olds:
            for k in range(1, n):
                pref = old[:k]
                new = (1,) + pref
                mass, moment, ss, hs = data(new)
                if mass == 1 and moment == 0 and ss == 2 and hs and hs[0][0] == len(new):
                    hits['case5'] += 1
                    examples.append(dict(
                        old=to_str(old), new=to_str(new), k=k,
                        old_n=n, new_n=len(new),
                    ))
    print('CASE5=' + json.dumps(dict(hits=dict(hits), n_ex=len(examples))))
    for ex in examples[:12]:
        print('EX=' + json.dumps(ex))


if __name__ == '__main__':
    main()
