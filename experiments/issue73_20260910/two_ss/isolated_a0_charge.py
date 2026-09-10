#!/usr/bin/env python3
"""H-20260910-31: isolated a=0 previous-S vs E-128, plus a=0 shape census.

Discovery periods 1..16, holdout 17..20. Computation, not a proof.
"""
from __future__ import annotations

import hashlib
import itertools
import json
import subprocess
from collections import Counter, defaultdict
from pathlib import Path


def to_str(w):
    return ''.join('A' if s == 1 else 'S' for s in w)


def min_p2(e, t, p, lag_cap):
    mass = moment = ss = 0
    prev = 1
    w = []
    ss_pos = []
    for d in range(1, lag_cap + 1):
        s = e[(t - d) % p]
        w.append(s)
        mass += s
        moment += d * s
        if s == prev == -1:
            ss += 1
            ss_pos.append(d - 2)
        prev = s
        if mass == 1 and moment == 0:
            return d, tuple(w), ss, ss_pos
    return None, None, None, None


def data(w):
    mass = moment = ss = 0
    hits = []
    prev = 1
    ss_pos = []
    for i, s in enumerate(w, 1):
        mass += s
        moment += i * s
        if s == prev == -1:
            ss += 1
            ss_pos.append(i - 2)
        prev = s
        if mass == 1 and moment == 0:
            hits.append(i)
    return mass, moment, ss, hits, ss_pos


def leading_A(w):
    n = 0
    for s in w:
        if s == 1:
            n += 1
        else:
            break
    return n


def trailing_A(w):
    n = 0
    for s in reversed(w):
        if s == 1:
            n += 1
        else:
            break
    return n


def scan_period(p):
    lag_cap = 4 * p
    kinds = Counter()
    n_iso = n_low = n_comp = 0
    examples = []
    for bits in itertools.product((1, -1), repeat=p):
        e = bits
        low_end = {}
        iso_prev = {}
        for t in range(p):
            if e[t] != 1:
                continue
            d, w, ss, ss_pos = min_p2(e, t, p, lag_cap)
            if d is None:
                continue
            lead = leading_A(w)
            if ss <= 1:
                n_low += 1
                q = (t - d) % p
                low_end[q] = (t, d, to_str(w))
            elif ss == 2 and lead == 0:
                n_iso += 1
                q = (t - 1) % p
                if e[q] != -1:
                    kinds['iso_prev_not_S'] += 1
                    examples.append(('iso_prev_not_S', p, t, to_str(w)))
                if q in iso_prev:
                    kinds['iso_prev_self'] += 1
                    examples.append(('iso_prev_self', p, t, iso_prev[q][0], to_str(w)))
                iso_prev[q] = (t, d, to_str(w))
            elif ss == 2:
                n_comp += 1
        for q, rec in iso_prev.items():
            if q in low_end:
                kinds['iso_prev_hits_lowSS'] += 1
                t, d, w = rec
                t0, d0, w0 = low_end[q]
                if len(examples) < 40:
                    examples.append(('iso_prev_hits_lowSS', p, t, t0, q, w, w0, to_str(e)))
    return dict(p=p, low=n_low, iso=n_iso, other_ss2=n_comp,
                kinds=dict(kinds), examples=examples, n_ex=len(examples))


def classify_words(max_n):
    rows = []
    for n in range(3, max_n + 1):
        for bits in itertools.product((-1, 1), repeat=n):
            mass, moment, ss, hits, ss_pos = data(bits)
            if mass != 1 or moment != 0 or ss != 2:
                continue
            if hits != [n]:
                continue
            if leading_A(bits) != 0:
                continue
            rows.append(dict(
                n=n, word=to_str(bits), end_A=bits[-1] == 1,
                nosaas='SAAS' not in to_str(bits),
                sss='SSS' in to_str(bits),
                trailing_A=trailing_A(bits),
                ss_pos=ss_pos,
                holdout=n >= 16,
            ))
    return rows


def main():
    print('protocol=H-20260910-31 isolated a=0 previous-S vs E-128')
    print('source_revision=' + subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip())
    print('source_sha256=' + hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    print('command=python3 experiments/issue73_20260910/two_ss/isolated_a0_charge.py')
    print('start_clock=see runner')
    print('PHASE=word_classification discovery=3..15 holdout=16..23')
    rows = classify_words(23)
    by_n = Counter(r['n'] for r in rows)
    print('ISO_A0_COUNTS=' + json.dumps(dict(by_n), sort_keys=True))
    print('ISO_A0_TOTAL=' + str(len(rows)))
    shapes = Counter((r['end_A'], r['nosaas'], r['sss'], r['trailing_A'], r['n']) for r in rows)
    for key, c in sorted(shapes.items()):
        print('SHAPE=' + json.dumps(dict(
            end_A=key[0], nosaas=key[1], sss=key[2], trailing_A=key[3],
            n=key[4], count=c)))
    for r in rows:
        if r['n'] <= 15 or r['nosaas']:
            print('WORD=' + json.dumps(r, sort_keys=True))

    print('PHASE=periodic_scan discovery=1..16 holdout=17..20 lag_cap=4p')
    for p in range(1, 21):
        rec = scan_period(p)
        print('PERIOD=' + json.dumps(dict(
            p=p, holdout=p >= 17, low=rec['low'], iso=rec['iso'],
            other_ss2=rec['other_ss2'], kinds=rec['kinds'], n_ex=rec['n_ex'],
        ), sort_keys=True), flush=True)
        for ex in rec['examples'][:8]:
            print('COLLISION=' + json.dumps(dict(kind=ex[0], data=list(map(str, ex[1:])))))


if __name__ == '__main__':
    main()
