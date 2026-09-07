#!/usr/bin/env python3
"""H-20260907-06: frozen support-connectivity enrichment of E-056.
All membership decisions are exact Python integers and sets. Prefix data are
old regression data; discovery/holdout separate only the new enrichment claim.
"""
import argparse
import hashlib
import json
from math import isqrt
from pathlib import Path
import subprocess

REVISION = '612fcfaf74bfb49f3ae05a268057c82f70dcca26'


def canonical_prefix(horizon):
    value, seen = 0, {0}
    for clock in range(1, horizon + 1):
        candidate = value - clock
        value = candidate if candidate > 0 and candidate not in seen else value + clock
        seen.add(value)
    return seen


def parameters(horizon):
    prefix = canonical_prefix(horizon)
    w = 2 * (max(prefix) // 2 + 1)
    d = max(10, 2 * ((isqrt(w + 16) + 4) // 2 + 1))
    assert d % 2 == 0 and d * d - 8 * d > w
    v, j = d * d + w, (d * d + w) // 2
    h = v + 1 + 3 * j
    n = 16 * h + 2 * (h % 2)
    b, c, x = n - 2, n + 2 * j + 1, 3 * n + h - 1
    seed = prefix | {0, x, v - 1}
    seed.update(v + 3 * k for k in range(1, j + 1))
    seed.update((k - 2) * c + v + k * (k - 3) // 2 for k in range(4, d + 1))
    return prefix, seed, dict(horizon=horizon, w=w, D=d, v=v, J=j, h=h, B=b, c=c, x=x)


def replay(seed, p):
    b, c, d, j, x = (p[k] for k in ('B', 'c', 'D', 'J', 'x'))
    seen, fresh, uses = set(seed), set(), {}
    residue, value = x % b, x
    word = 'SS' + 'AS' * j + 'S' + 'A' * d + 'S' * d
    for clock, expected in enumerate(word, b + 1):
        candidate = value - clock
        blocked = candidate > 0 and candidate in seen
        sign = 'S' if candidate > 0 and not blocked else 'A'
        assert sign == expected, (clock, sign, expected, candidate)
        if sign == 'S':
            fresh.add(candidate)
        if c + 5 < clock <= c + 2 * d and blocked:
            uses[candidate] = uses.get(candidate, 0) + 1
        value = candidate if sign == 'S' else value + clock
        seen.add(value)
        next_residue = value % clock
        assert next_residue <= residue, (clock, residue, next_residue)
        residue = next_residue
        if c < clock < c + 2 * d:
            assert value >= clock
    assert clock == c + 2 * d and value == p['w'] and value < clock
    assert len(uses) == d - 5 and max(uses.values()) == 1
    assert len(fresh) == j + d + 3
    return fresh


def bridge_support(seed, forbidden, bound):
    ordered = sorted(seed)
    additions = []
    for left, right in zip(ordered, ordered[1:]):
        cursor = left
        while right - cursor > bound:
            nxt = cursor + bound
            while nxt in forbidden:
                nxt -= 1
            assert cursor < nxt < right and bound - len(forbidden) <= nxt - cursor <= bound
            additions.append(nxt)
            cursor = nxt
    result = seed | set(additions)
    assert len(additions) == len(set(additions))
    assert max(b - a for a, b in zip(sorted(result), sorted(result)[1:])) <= bound
    assert set(additions).isdisjoint(forbidden)
    assert len(additions) * (bound - len(forbidden)) <= max(seed)
    return result, additions


def check(horizon, mode):
    prefix, seed, p = parameters(horizon)
    original_gap = max(b - a for a, b in zip(sorted(seed), sorted(seed)[1:]))
    fresh = replay(seed, p)
    augmented, bridges = bridge_support(seed, fresh, p['B'])
    assert replay(augmented, p) == fresh
    q, j, d, b = len(fresh), p['J'], p['D'], p['B']
    assert q == j + d + 3 <= 2 * j + 3
    assert max(seed) < 2 * d * (b - q)
    assert len(bridges) < 2 * d
    assert len(augmented) <= b + 1
    assert max(augmented) <= b * (b + 1) // 2
    assert p['x'] % 2 == (b * (b + 1) // 2) % 2
    assert prefix <= augmented
    assert 16 * p['v'] - 7 * p['h'] < 0
    summary = {**p, 'mode': mode, 'seed_size': len(seed), 'original_max_gap': original_gap,
               'augmented_size': len(augmented), 'bridge_count': len(bridges), 'fresh_count': q,
               'augmented_max_gap': max(y - x for x, y in zip(sorted(augmented), sorted(augmented)[1:])),
               'max_seed': max(augmented), 'ratio_slack': 16 * p['v'] - 7 * p['h'],
               'bridges_sha256': hashlib.sha256(json.dumps(bridges, separators=(',', ':')).encode()).hexdigest()}
    if horizon == 0:
        summary['original_seed'] = sorted(seed)
        summary['bridges'] = bridges
    print(json.dumps(summary, separators=(',', ':'), sort_keys=True), flush=True)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--mode', choices=('discovery', 'holdout'), required=True)
    args = parser.parse_args()
    actual = subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip()
    print('protocol=H-20260907-06; claim C frozen before experiments; old prefixes reused only as input')
    print('source_base_revision=' + REVISION)
    print('current_revision=' + actual)
    print('source_sha256=' + hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    for horizon in ((0, 4, 128) if args.mode == 'discovery' else (1000, 10000, 200000)):
        check(horizon, args.mode)
    print('PASS: all enriched seeds retain exact word, no-wrap landing, ratio violation, one-use, bounds, parity, and max gap <= B')


if __name__ == '__main__':
    main()
