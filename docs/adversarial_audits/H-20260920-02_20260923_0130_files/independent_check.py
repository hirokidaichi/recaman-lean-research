#!/usr/bin/env python3
"""Independent direct-cycle and local-bit audit of H-20260920-02.

Convention: A=1, S=0; cyclic strings are chronological, windows newest first.
The finite scan is a regression, not an infinite proof or a fresh holdout.
"""

import argparse
import itertools
import json


def p2(w):
    signs = [1 if x else -1 for x in w]
    return sum(signs) == 1 and sum((j + 1) * x for j, x in enumerate(signs)) == 0


def ss_count(w):
    return sum(not w[j] and not w[j + 1] for j in range(len(w) - 1))


def oldest(w):
    return max((j + 1 for j, x in enumerate(w) if not x), default=0)


def window(e, t, d):
    p = len(e)
    return tuple(e[(t - j - 1) % p] for j in range(d))


def compact(w):
    return ''.join('A' if x else 'S' for x in w)


def local_table():
    donors = [w for w in itertools.product((False, True), repeat=11)
              if p2(w) and ss_count(w) == 2]
    coverers = {'AAS': (True, True, False),
                'w1': (False, True, True, True, True, False, False),
                'w2': (True, False, True, True, False, True, False)}
    rows = []
    for w in donors:
        off = oldest(w)
        covers = []
        for name, v in coverers.items():
            for k, bit in enumerate(v):
                if bit:
                    continue
                # Set donor clock to zero, then align coverer bit k with oldest.
                t = -off + k + 1
                assignments = [(t, True)] + [(t - j - 1, x) for j, x in enumerate(v)]
                if all(w[-c - 1] == x for c, x in assignments if -11 <= c <= -1):
                    covers.append((name, t, k, None if not (-11 <= t + 1 <= -1) else w[-t - 2],
                                   None if not (-11 <= t + 2 <= -1) else w[-t - 3]))
        minimal = not any(p2(w[:d]) for d in range(1, 11))
        rows.append({'word': compact(w), 'minimal': minimal, 'oldest': off,
                     'covers': covers, 'prefixes': [d for d in range(1, 11) if p2(w[:d])]})
    print(json.dumps({'kind': 'local_table', 'n_words': len(rows), 'nonminimal': sum(not x['minimal'] for x in rows),
                      'rows': rows}, sort_keys=True))
    assert len(rows) == 12 and sum(not x['minimal'] for x in rows) == 5
    assert sum(len(x['covers']) for x in rows) == 7
    assert sum(y[0] == 'w1' for x in rows for y in x['covers']) == 5
    assert sum(y[0] == 'w2' for x in rows for y in x['covers']) == 2
    assert all(y[0] != 'AAS' for x in rows for y in x['covers'])
    assert all(y[3] is False or y[4] is False for x in rows for y in x['covers'] if y[0] == 'w1')
    # Recreate the failed two-bit table: it checks t-1,t-2 but omits current A at t.
    weak2 = []
    for x in rows:
        w = tuple(z == 'A' for z in x['word'])
        off = x['oldest']
        t = -off + 3
        if all(w[-(t-j)-1] for j in (1, 2)):
            weak2.append({'word': x['word'], 't': t, 'current': w[-t-1]})
    print(json.dumps({'kind': 'two_bit_negative_control', 'rows': weak2}, sort_keys=True))
    assert any(not x['current'] for x in weak2)


def cycle_scan(maxp):
    totals = {'cycles': 0, 'eligible_cycles': 0, 'tight_nonempty': 0,
              'donors': 0, 'nonminimal_donors': 0, 'checks': 0,
              'nonminimal_checks': 0, 'nonpositive_checks': 0, 'violations': 0}
    by_period = []
    for p in range(1, maxp + 1):
        local = {k: 0 for k in totals}
        for bits in itertools.product((False, True), repeat=p):
            local['cycles'] += 1
            lag = {}
            cover = {}
            for b in range(p):
                if not bits[b]:
                    continue
                for d in (3, 7, 11):
                    if p2(window(bits, b, d)):
                        lag[b] = d
                        cover[b] = {s for j in range(d) if not bits[(b-j-1) % p]
                                    for s in [(b-j-1) % p]}
                        break
            donors = [(u, window(bits, u, 11)) for u in range(p)
                      if p2(window(bits, u, 11)) and ss_count(window(bits, u, 11)) == 2]
            local['donors'] += len(donors)
            local['nonminimal_donors'] += sum(any(p2(w[:d]) for d in range(1, 11)) for _, w in donors)
            if not lag or not donors:
                continue
            local['eligible_cycles'] += 1
            phases = list(lag)
            tight = []
            for mask in range(1, 1 << len(phases)):
                subset = [phases[j] for j in range(len(phases)) if mask >> j & 1]
                neighborhood = set().union(*(cover[b] for b in subset))
                if len(neighborhood) == len(subset):
                    tight.append((subset, neighborhood))
            local['tight_nonempty'] += len(tight)
            for u, w in donors:
                s = (u - oldest(w)) % p
                nonminimal = any(p2(w[:d]) for d in range(1, 11))
                for B, N in tight:
                    local['checks'] += 1
                    local['nonminimal_checks'] += nonminimal
                    local['nonpositive_checks'] += 2 * sum(bits) - p <= 0
                    if s in N:
                        local['violations'] += 1
                        print(json.dumps({'kind': 'COUNTEREXAMPLE', 'p': p, 'word': compact(bits),
                                          'u0': u, 'window': compact(w), 'B': B, 'N': sorted(N),
                                          'oldest': oldest(w), 's': s}))
                        raise AssertionError('full-premise counterexample')
        for k, v in local.items():
            totals[k] += v
        by_period.append({'p': p, **local})
    print(json.dumps({'kind': 'cycle_scan', 'maxp': maxp, 'by_period': by_period, 'totals': totals}, sort_keys=True))


def specified_example():
    e = tuple(x == 'A' for x in 'AASSSAAAASSSS')
    p = len(e)
    u = 10
    w = window(e, u, 11)
    B = [7]
    lag = 3
    N = {(7-j-1) % p for j in range(lag) if not e[(7-j-1) % p]}
    s = (u-oldest(w)) % p
    out = {'kind': 'specified_example', 'p': p, 'cycle': compact(e), 'u0': u,
           'current': compact((e[u],)), 'window': compact(w), 'P2': p2(w),
           'ss': ss_count(w), 'proper_P2_prefixes': [d for d in range(1,11) if p2(w[:d])],
           'B': B, 'B_lag': lag, 'B_window': compact(window(e, 7, lag)),
           'N': sorted(N), 'tight': len(N) == len(B), 'oldest': oldest(w),
           's': s, 'avoids': s not in N,
           'translations': {str(v): {'same_window': window(e, u+v*p, 11) == w,
                                      'same_oldest_phase': (u+v*p-oldest(w)) % p == s}
                            for v in (-101,-1,0,1,101)}}
    print(json.dumps(out, sort_keys=True))
    assert out['window'] == 'SAAAASSSAAS' and out['B_window'] == 'AAS'
    assert out['N'] == [4] and out['proper_P2_prefixes'] == [7]
    assert out['avoids'] and all(x['same_window'] and x['same_oldest_phase'] for x in out['translations'].values())


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--maxp', type=int, default=14)
    args = ap.parse_args()
    local_table()
    specified_example()
    cycle_scan(args.maxp)
