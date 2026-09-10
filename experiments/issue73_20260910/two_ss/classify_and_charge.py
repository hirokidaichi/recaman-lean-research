#!/usr/bin/env python3
"""H-20260910-30: classify SS=2 P2 words and falsify named charges.

Discovery lengths 3..15; holdout 16..23. This is computation, not a proof.
"""
from __future__ import annotations

import hashlib
import itertools
import json
import subprocess
from collections import Counter, defaultdict
from pathlib import Path


def data(w):
    mass = moment = ss = 0
    hits = []
    previous = 1
    ss_pos = []
    for i, s in enumerate(w, 1):
        mass += s
        moment += i * s
        if s == previous == -1:
            ss += 1
            ss_pos.append(i - 2)
        previous = s
        if mass == 1 and moment == 0:
            hits.append(i)
    return mass, moment, ss, hits, ss_pos


def to_str(w):
    return ''.join('A' if s == 1 else 'S' for s in w)


def trailing_A(w):
    n = 0
    for s in reversed(w):
        if s == 1:
            n += 1
        else:
            break
    return n


def leading_A(w):
    n = 0
    for s in w:
        if s == 1:
            n += 1
        else:
            break
    return n


def oldest_S_offset(w):
    for i in range(len(w) - 1, -1, -1):
        if w[i] == -1:
            return i
    return None


def newest_S_offset(w):
    for i, s in enumerate(w):
        if s == -1:
            return i
    return None


def first_SS_S(w, ss_pos):
    return ss_pos[0] if ss_pos else None


def overlapping_SSS(w):
    s = to_str(w)
    return 'SSS' in s


def no_saas(w):
    return 'SAAS' not in to_str(w)


def classify_length(n, holdout):
    stats = Counter()
    shapes = Counter()
    min_words = []
    a_ended_min = []
    moment_bound = None
    for bits in itertools.product((-1, 1), repeat=n):
        mass, moment, ss, hits, ss_pos = data(bits)
        if ss != 2 or mass != 1 or moment != 0:
            if bits and bits[-1] == 1 and ss == 2:
                val = moment + n
                if moment_bound is None or val < moment_bound[0]:
                    moment_bound = (val, to_str(bits), mass, moment, ss)
            continue
        stats['p2_ss2'] += 1
        is_min = hits == [n]
        ends_A = bits[-1] == 1
        stats['min'] += is_min
        stats['end_A'] += ends_A
        stats['min_end_A'] += is_min and ends_A
        stats['nosaas'] += no_saas(bits)
        stats['min_nosaas'] += is_min and no_saas(bits)
        stats['sss'] += overlapping_SSS(bits)
        stats['min_sss'] += is_min and overlapping_SSS(bits)
        stats['min_end_A_sss'] += is_min and ends_A and overlapping_SSS(bits)
        if is_min:
            key = (
                'endA' if ends_A else 'endS',
                'SSS' if overlapping_SSS(bits) else 'sepSS',
                'NoSAAS' if no_saas(bits) else 'SAAS',
                f'a{leading_A(bits)}',
                f'v{trailing_A(bits)}',
                f'ss@{tuple(ss_pos)}',
            )
            shapes[key] += 1
            rec = dict(
                word=to_str(bits),
                length=n,
                end_A=ends_A,
                nosaas=no_saas(bits),
                sss=overlapping_SSS(bits),
                leading_A=leading_A(bits),
                trailing_A=trailing_A(bits),
                ss_pos=ss_pos,
                oldest_S=oldest_S_offset(bits),
                newest_S=newest_S_offset(bits),
                first_SS_S=first_SS_S(bits, ss_pos),
                holdout=holdout,
            )
            min_words.append(rec)
            if ends_A:
                a_ended_min.append(rec)
    return stats, shapes, min_words, a_ended_min, moment_bound


def min_p2_window(e, t, p, lag_cap):
    """Incremental mass/moment/ss over newest-first past of source t."""
    mass = moment = ss = 0
    prev = 1
    ss_pos = []
    w = []
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


def periodic_scan(p, lag_cap):
    """All binary periods of length p. Minimum P2 lag up to lag_cap."""
    collisions = []
    n_words = 0
    n_A = 0
    n_low = 0
    n_ss2 = 0
    n_ss_ge3 = 0
    n_unsupplied = 0
    for bits in itertools.product((1, -1), repeat=p):
        n_words += 1
        e = bits
        used_low = {}
        used_ss2_oldest = {}
        used_ss2_newest = {}
        used_ss2_firstss = {}
        for t in range(p):
            if e[t] != 1:
                continue
            n_A += 1
            min_d, min_word, min_ss, ss_pos = min_p2_window(e, t, p, lag_cap)
            if min_d is None:
                n_unsupplied += 1
                continue
            if min_ss <= 1:
                n_low += 1
                endpoint = (t - min_d) % p
                if e[endpoint] != -1:
                    collisions.append(('lowSS_prefix_not_S', p, t, min_d, to_str(min_word)))
                    continue
                if endpoint in used_low:
                    collisions.append(('lowSS_endpoint_collision', p, t, used_low[endpoint],
                                       endpoint, to_str(min_word)))
                used_low[endpoint] = t
            elif min_ss == 2:
                n_ss2 += 1
                oldest = (t - (oldest_S_offset(min_word) + 1)) % p
                newest = (t - (newest_S_offset(min_word) + 1)) % p
                firstss = (t - (ss_pos[0] + 1)) % p
                if e[oldest] != -1:
                    collisions.append(('ss2_oldest_not_S', p, t, min_d, to_str(min_word)))
                if oldest in used_ss2_oldest:
                    collisions.append(('ss2_oldest_collision', p, t, used_ss2_oldest[oldest],
                                       oldest, to_str(min_word)))
                used_ss2_oldest[oldest] = t
                if newest in used_ss2_newest:
                    collisions.append(('ss2_newest_collision', p, t, used_ss2_newest[newest],
                                       newest, to_str(min_word)))
                used_ss2_newest[newest] = t
                if firstss in used_ss2_firstss:
                    collisions.append(('ss2_firstSS_collision', p, t, used_ss2_firstss[firstss],
                                       firstss, to_str(min_word)))
                used_ss2_firstss[firstss] = t
            else:
                n_ss_ge3 += 1
        for q, t2 in used_ss2_oldest.items():
            if q in used_low:
                collisions.append(('ss2_oldest_hits_lowSS', p, t2, used_low[q], q,
                                   'joint'))
    return dict(p=p, words=n_words, A=n_A, low=n_low, ss2=n_ss2, ss_ge3=n_ss_ge3,
                unsupplied=n_unsupplied, collisions=collisions)


def finite_common_history(max_len):
    """All finite newest-first histories. Current sign is an implicit extra A.

    A source at offset 0 uses the whole word as its past. A source at
    offset t (0<t<n) uses the prefix of length t as its past, and the
    current sign is word[t] which must be A.
    """
    collisions = []
    examples = 0
    for n in range(3, max_len + 1):
        for bits in itertools.product((-1, 1), repeat=n):
            # implicit current A at time n (just after index 0 of the word)
            # times: source u at "now" has past = bits[0:d]
            # older source at position t (0<=t<n) has current sign bits[t]
            # and past bits[t+1:] of length n-t-1? Let's use integer times.
            #
            # Layout: indices 0..n-1 are past signs at times n-1, n-2, ..., 0
            # Current source time = n, current sign = A (implicit).
            # Older source time t in 1..n-1 has current sign = bits[n-1-t]
            # (the sign at time t is the letter at offset n-1-t).
            #
            # Simpler: build an explicit stream of length n+1: A + word
            stream = (1,) + bits  # stream[0] is current A at time 0 looking forward? 
            # Use times 0..n with e[0]=A (newest current), e[1:]=bits
            e = (1,) + bits
            T = len(e)
            used_low = {}
            used_oldest = {}
            sources = []
            for t in range(T):
                if e[t] != 1:
                    continue
                # past is e[t+1], e[t+2], ... (older)
                past = e[t + 1:]
                if not past:
                    continue
                mass, moment, ss, hits, ss_pos = data(past)
                min_d = hits[0] if hits else None
                if min_d is None:
                    continue
                w = past[:min_d]
                _, _, ss, _, ss_pos = data(w)
                sources.append((t, min_d, ss, w, ss_pos))
                if ss <= 1:
                    f = hits[0]
                    endpoint = t + f  # older time
                    if endpoint in used_low:
                        collisions.append(('finite_low_collision', n, t, used_low[endpoint],
                                           to_str(w)))
                    used_low[endpoint] = t
                elif ss == 2:
                    off = oldest_S_offset(w)
                    q = t + off + 1
                    if q in used_oldest:
                        collisions.append(('finite_ss2_oldest_collision', n, t,
                                           used_oldest[q], to_str(w), to_str(e)))
                    used_oldest[q] = t
                    if q in used_low:
                        collisions.append(('finite_ss2_hits_low', n, t, used_low[q],
                                           to_str(w), to_str(e)))
            examples += 1
            # reverse direction already handled if we iterate t increasing
            # (newer first). Older sources have larger t.
            for q, t2 in list(used_oldest.items()):
                if q in used_low:
                    rec = ('finite_ss2_hits_low', n, t2, used_low[q])
                    if rec not in collisions and not any(
                            c[0] == 'finite_ss2_hits_low' and c[1] == n and c[2] == t2
                            for c in collisions):
                        collisions.append(('finite_ss2_hits_low_rev', n, t2, used_low[q],
                                           to_str(e)))
    return examples, collisions


def main():
    src = Path(__file__)
    print('protocol=H-20260910-30 SS=2 classification and named-charge falsifier')
    print('source_revision=' + subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip())
    print('source_sha256=' + hashlib.sha256(src.read_bytes()).hexdigest())
    print('command=python3 experiments/issue73_20260910/two_ss/classify_and_charge.py')

    all_min = []
    all_a_ended = []
    print('PHASE=word_classification discovery=3..15 holdout=16..23')
    for n in range(3, 24):
        holdout = n >= 16
        stats, shapes, min_words, a_ended_min, moment_bound = classify_length(n, holdout)
        all_min.extend(min_words)
        all_a_ended.extend(a_ended_min)
        print('LENGTH=' + json.dumps(dict(
            n=n, holdout=holdout,
            p2_ss2=stats['p2_ss2'], minimum=stats['min'],
            end_A=stats['end_A'], min_end_A=stats['min_end_A'],
            nosaas=stats['nosaas'], min_nosaas=stats['min_nosaas'],
            sss=stats['sss'], min_sss=stats['min_sss'],
            min_end_A_sss=stats['min_end_A_sss'],
            min_shapes=len(shapes),
            a_ended_moment_plus_len_min=None if moment_bound is None else moment_bound[0],
        ), sort_keys=True))
        if n <= 15 or (holdout and a_ended_min):
            for rec in a_ended_min[:12]:
                print('MIN_END_A=' + json.dumps(rec, sort_keys=True))
            if len(a_ended_min) > 12:
                print(f'MIN_END_A_MORE={len(a_ended_min) - 12}')
        if n <= 11:
            for key, c in shapes.most_common(20):
                print('SHAPE=' + json.dumps(dict(n=n, key=list(key), count=c)))

    boundary = 'AAASSSASASA'
    bw = tuple(1 if c == 'A' else -1 for c in boundary)
    mass, moment, ss, hits, ss_pos = data(bw)
    print('BOUNDARY=' + json.dumps(dict(
        word=boundary, mass=mass, moment=moment, ss=ss, hits=hits,
        ss_pos=ss_pos, oldest_S=oldest_S_offset(bw),
        newest_S=newest_S_offset(bw), first_SS_S=first_SS_S(bw, ss_pos),
        trailing_A=trailing_A(bw), leading_A=leading_A(bw),
        sss=overlapping_SSS(bw), nosaas=no_saas(bw),
        is_minimum=hits == [len(bw)],
    ), sort_keys=True))

    print('PHASE=A_ended_minimum_summary')
    print('A_ENDED_MIN_COUNT=' + str(len(all_a_ended)))
    trail = Counter((r['trailing_A'], r['sss'], r['nosaas'], r['length']) for r in all_a_ended)
    for key, c in sorted(trail.items()):
        print('A_ENDED_TRAIL=' + json.dumps(dict(
            trailing_A=key[0], sss=key[1], nosaas=key[2], length=key[3], count=c)))
    print('A_ENDED_WORDS=' + json.dumps([r['word'] for r in all_a_ended]))

    print('PHASE=periodic_scan discovery=1..16 holdout=17..18 lag_cap=4p')
    for p in range(1, 19):
        lag_cap = 4 * p
        rec = periodic_scan(p, lag_cap)
        cols = rec['collisions']
        kinds = Counter(c[0] for c in cols)
        print('PERIOD=' + json.dumps(dict(
            p=p, holdout=p >= 17, words=rec['words'], A=rec['A'],
            low=rec['low'], ss2=rec['ss2'], ss_ge3=rec['ss_ge3'],
            unsupplied=rec['unsupplied'], collision_kinds=dict(kinds),
            n_collisions=len(cols),
        ), sort_keys=True), flush=True)
        for c in cols[:8]:
            print('COLLISION=' + json.dumps(dict(kind=c[0], data=list(map(str, c[1:])))))
        if len(cols) > 8:
            print(f'COLLISION_MORE={len(cols) - 8}')

    print('PHASE=finite_common_history n=3..12')
    examples, fcols = finite_common_history(12)
    fkinds = Counter(c[0] for c in fcols)
    print('FINITE=' + json.dumps(dict(
        histories=examples, n_collisions=len(fcols), kinds=dict(fkinds))))
    for c in fcols[:20]:
        print('FINITE_COLLISION=' + json.dumps(dict(kind=c[0], data=list(map(str, c[1:])))))

    print('PASS_OR_FAIL: see collision_kinds; zero collisions would support the charge')


if __name__ == '__main__':
    main()
