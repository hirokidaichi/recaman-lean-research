#!/usr/bin/env python3
"""H-20260910-30 follow-up: newest-S vs low-SS, one-per-run, oldest-S collision dump.

Discovery periods 1..16, holdout 17..18. Computation, not a proof.
"""
from __future__ import annotations

import hashlib
import itertools
import json
import subprocess
from collections import Counter
from pathlib import Path


def to_str(w):
    return ''.join('A' if s == 1 else 'S' for s in w)


def min_p2(e, t, p, lag_cap):
    mass = moment = ss = 0
    prev = 1
    w = []
    for d in range(1, lag_cap + 1):
        s = e[(t - d) % p]
        w.append(s)
        mass += s
        moment += d * s
        if s == prev == -1:
            ss += 1
        prev = s
        if mass == 1 and moment == 0:
            return d, tuple(w), ss
    return None, None, None


def newest_S_offset(w):
    for i, s in enumerate(w):
        if s == -1:
            return i
    return None


def oldest_S_offset(w):
    for i in range(len(w) - 1, -1, -1):
        if w[i] == -1:
            return i
    return None


def dump_oldest_collision():
    """Period 16 word from the first scan."""
    # Reconstruct from collision record: p=16, t=12 and t=3 share oldest 9
    # word shown was the min window of t=12: SASASAASAAAASSSASAS
    p = 16
    print('PHASE=oldest_S_collision_dump')
    # Search the unique (up to rotation) period-16 words with an oldest-S collision
    n_found = 0
    for bits in itertools.product((1, -1), repeat=p):
        e = bits
        used = {}
        for t in range(p):
            if e[t] != 1:
                continue
            d, w, ss = min_p2(e, t, p, 4 * p)
            if d is None or ss != 2:
                continue
            q = (t - (oldest_S_offset(w) + 1)) % p
            if q in used:
                t0 = used[q]
                d0, w0, ss0 = min_p2(e, t0, p, 4 * p)
                print('OLDEST_COLLISION=' + json.dumps(dict(
                    p=p, stream=to_str(e),
                    t0=t0, d0=d0, ss0=ss0, w0=to_str(w0),
                    t1=t, d1=d, ss1=ss, w1=to_str(w),
                    shared_oldest=q, nosaas='SAAS' not in (to_str(e) * 2),
                    run_same=all(e[(min(t0, t) + i) % p] == 1
                                 for i in range((max(t0, t) - min(t0, t)) % p)),
                ), sort_keys=True))
                n_found += 1
                if n_found >= 4:
                    return
            used[q] = t


def scan(p):
    lag_cap = 4 * p
    kinds = Counter()
    n_ss2 = 0
    n_low = 0
    n_run_two = 0
    examples = []
    for bits in itertools.product((1, -1), repeat=p):
        e = bits
        used_low = {}
        used_newest = {}
        ss2_by_run_S = {}
        for t in range(p):
            if e[t] != 1:
                continue
            d, w, ss = min_p2(e, t, p, lag_cap)
            if d is None:
                continue
            if ss <= 1:
                n_low += 1
                endpoint = (t - d) % p
                used_low[endpoint] = (t, d, to_str(w))
            elif ss == 2:
                n_ss2 += 1
                ns = newest_S_offset(w)
                q = (t - (ns + 1)) % p
                # preceding-run S: skip leading A's
                lead = 0
                while lead < d and w[lead] == 1:
                    lead += 1
                run_S = (t - (lead + 1)) % p
                if run_S != q:
                    kinds['newest_ne_run_S'] += 1
                    examples.append(('newest_ne_run_S', p, t, to_str(w)))
                if q in used_newest:
                    kinds['newest_collision'] += 1
                    t0, d0, w0 = used_newest[q]
                    examples.append(('newest_collision', p, t0, t, q, w0, to_str(w), to_str(e)))
                used_newest[q] = (t, d, to_str(w))
                ss2_by_run_S.setdefault(run_S, []).append(t)
        for q, srcs in ss2_by_run_S.items():
            if len(srcs) >= 2:
                n_run_two += 1
                kinds['two_ss2_same_run'] += 1
                examples.append(('two_ss2_same_run', p, srcs, q, to_str(e)))
        for q, rec in used_newest.items():
            if q in used_low:
                kinds['newest_hits_lowSS'] += 1
                t, d, w = rec
                t0, d0, w0 = used_low[q]
                examples.append(('newest_hits_lowSS', p, t, t0, q, w, w0, to_str(e)))
    return dict(p=p, low=n_low, ss2=n_ss2, two_ss2_same_run=n_run_two,
                kinds=dict(kinds), examples=examples[:12], n_examples=len(examples))


def trailing_A_check():
    """Every min P2 of any SS count, lengths 3..19: does it end AA?"""
    from classify_and_charge import data
    print('PHASE=trailing_AA_any_SS lengths=3..19')
    found = []
    for n in range(3, 20):
        n_min = n_end_A = n_end_AA = 0
        for bits in itertools.product((-1, 1), repeat=n):
            mass, moment, ss, hits, _ = data(bits)
            if mass != 1 or moment != 0:
                continue
            if hits != [n]:
                continue
            n_min += 1
            if bits[-1] == 1:
                n_end_A += 1
                if n >= 2 and bits[-2] == 1:
                    n_end_AA += 1
                    found.append((n, ss, ''.join('A' if s == 1 else 'S' for s in bits)))
        print('TRAIL=' + json.dumps(dict(
            n=n, min_P2=n_min, end_A=n_end_A, end_AA=n_end_AA)))
    print('END_AA_EXAMPLES=' + json.dumps(found[:20]))


def main():
    print('protocol=H-20260910-30 newest-S audit')
    print('source_revision=' + subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip())
    print('source_sha256=' + hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    print('command=python3 experiments/issue73_20260910/two_ss/newest_s_audit.py')
    dump_oldest_collision()
    trailing_A_check()
    print('PHASE=newest_S_periodic discovery=1..16 holdout=17..18')
    for p in range(1, 19):
        rec = scan(p)
        print('PERIOD=' + json.dumps(dict(
            p=p, holdout=p >= 17, low=rec['low'], ss2=rec['ss2'],
            two_ss2_same_run=rec['two_ss2_same_run'], kinds=rec['kinds'],
            n_examples=rec['n_examples'],
        ), sort_keys=True), flush=True)
        for ex in rec['examples'][:6]:
            print('EX=' + json.dumps(dict(kind=ex[0], data=list(map(str, ex[1:])))))


if __name__ == '__main__':
    main()
