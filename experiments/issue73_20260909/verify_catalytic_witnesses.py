#!/usr/bin/env python3
"""Independent direct enumeration for H-20260909-02's two counterexamples.

No discovery imports, masks, precomputed potentials, or table recurrence.
Enumerate every A-block length 0..L for each future with <=k S letters.
"""
from collections import Counter
from itertools import product
import hashlib
import json
from pathlib import Path
import subprocess


def score(newest_first, continuation):
    L = len(newest_first)
    w = newest_first
    total = 0
    for sign in continuation:
        if sign == 'S':
            total -= 1
        else:
            found = False
            for d in range(1, L + 1):
                pos = [i + 1 for i, ch in enumerate(w[:d]) if ch == 'A']
                # These identities are independent of the signed accumulator.
                signed_sum = 2 * len(pos) - d
                moment = 2 * sum(pos) - d * (d + 1) // 2
                if (signed_sum, moment) == (1, 0):
                    found = True
            total += found
        w = sign + w[:-1]
    return total


def exhaustive(w, k):
    distribution = Counter()
    best, witness = 0, ''
    for s_count in range(k + 1):
        for blocks in product(range(len(w) + 1), repeat=s_count + 1):
            continuation = 'S'.join('A' * n for n in blocks)
            value = score(w, continuation)
            distribution[value] += 1
            if value > best:
                best, witness = value, continuation
    return {'maximum': best, 'witness': witness,
            'enumerated': sum(distribution.values()),
            'score_histogram': dict(sorted(distribution.items()))}


def main():
    print('protocol=H-20260909-02 independent witness verification')
    print('source_revision=' + subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip())
    print('script_sha256=' + hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    for k, w, expected_from, expected_to in (
        (1, 'SASSSAASSSS', 1, 3),
        (2, 'AAASAASSSSS', 0, 2),
    ):
        after = 'S' + w[:-1]
        before_result, after_result = exhaustive(w, k), exhaustive(after, k)
        assert before_result['maximum'] == expected_from
        assert after_result['maximum'] == expected_to
        assert expected_to > expected_from + 1
        total_future = 'S' + after_result['witness']
        assert total_future.count('S') == k + 1
        assert score(w, total_future) == expected_to - 1 > expected_from
        print('VERIFIED=' + json.dumps({'k': k, 'L': len(w), 'from': w, 'to': after,
              'before': before_result, 'after': after_result,
              'extra_catalyst_future': total_future,
              'extra_catalyst_score': score(w, total_future)}, sort_keys=True))
    print('PASS: both upper bounds and counterexample continuations independently verified')


if __name__ == '__main__':
    main()
