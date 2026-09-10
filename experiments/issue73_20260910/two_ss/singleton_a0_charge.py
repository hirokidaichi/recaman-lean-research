#!/usr/bin/env python3
"""H-20260910-31 one repair: isolated a=0 AND singleton A-run (e(t+1)=S).

Previous-S joint with all low-SS endpoints. Discovery 1..16, holdout 17..20.
"""
from __future__ import annotations

import hashlib
import itertools
import json
import subprocess
from collections import Counter
from pathlib import Path

import isolated_a0_charge as base


def scan(p):
    lag_cap = 4 * p
    kinds = Counter()
    n_sing = n_iso = n_low = 0
    examples = []
    for bits in itertools.product((1, -1), repeat=p):
        e = bits
        low_end = {}
        sing_prev = {}
        for t in range(p):
            if e[t] != 1:
                continue
            d, w, ss, _ = base.min_p2(e, t, p, lag_cap)
            if d is None:
                continue
            lead = base.leading_A(w)
            if ss <= 1:
                n_low += 1
                low_end[(t - d) % p] = (t, d, base.to_str(w))
            elif ss == 2 and lead == 0:
                n_iso += 1
                if e[(t + 1) % p] == -1:
                    n_sing += 1
                    q = (t - 1) % p
                    sing_prev[q] = (t, d, base.to_str(w))
        for q, rec in sing_prev.items():
            if q in low_end:
                kinds['singleton_hits_lowSS'] += 1
                t, d, w = rec
                t0, d0, w0 = low_end[q]
                if len(examples) < 24:
                    examples.append((p, t, t0, q, w, w0, base.to_str(e), d, d0))
    return dict(p=p, low=n_low, iso=n_iso, singleton=n_sing,
                kinds=dict(kinds), examples=examples)


def main():
    print('protocol=H-20260910-31 repair: singleton A-run isolated a=0 vs E-128')
    print('source_revision=' + subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip())
    print('source_sha256=' + hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    print('command=python3 experiments/issue73_20260910/two_ss/singleton_a0_charge.py')
    for p in range(1, 21):
        rec = scan(p)
        print('PERIOD=' + json.dumps(dict(
            p=p, holdout=p >= 17, low=rec['low'], iso=rec['iso'],
            singleton=rec['singleton'], kinds=rec['kinds'],
            n_ex=len(rec['examples']),
        ), sort_keys=True), flush=True)
        for ex in rec['examples'][:6]:
            print('COLLISION=' + json.dumps(dict(
                p=ex[0], sing_t=ex[1], low_t=ex[2], S=ex[3],
                sing_w=ex[4], low_w=ex[5], stream=ex[6],
                sing_d=ex[7], low_d=ex[8])))


if __name__ == '__main__':
    main()
