#!/usr/bin/env python3
"""Exact signature falsifier for H-20260907-07; no trajectory approximation."""
import argparse
import hashlib
import itertools
import pathlib
import subprocess


def signatures(word):
    p = len(word)
    total = sum(word)
    assert total > 0
    result = []
    # k = q*p+r and S_k = q*total+partial_r = 1 imply q <= p.
    for nextphase, s in enumerate(word):
        if s < 0:
            continue
        signsum = moment = 0
        hits = []
        for k in range(1, p * (p + 1) + 1):
            e = word[(nextphase - k) % p]
            signsum += e
            moment += (k - 1) * e
            if signsum == 1 and moment == -1:
                hits.append(k)
        result.append((nextphase, hits))
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--min-period', type=int, default=1)
    parser.add_argument('--max-period', type=int, default=12)
    args = parser.parse_args()
    print('protocol=H-20260907-07 exact periodic supply signatures')
    print('source_revision=' + subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip())
    print('script_sha256=' + hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest())
    print('range=' + str((args.min_period, args.max_period)))
    words = candidates = 0
    for p in range(args.min_period, args.max_period + 1):
        count = supplied = 0
        example = None
        for word in itertools.product((-1, 1), repeat=p):
            if sum(word) <= 0:
                continue
            words += 1
            count += 1
            sig = signatures(word)
            if all(hits for _, hits in sig):
                supplied += 1
                candidates += 1
                if example is None:
                    example = (''.join('A' if e > 0 else 'S' for e in word), sig)
        print('period=%d positive_words=%d all_additions_supplied=%d example=%r' % (p, count, supplied, example), flush=True)
    print('total_positive_words=%d all_additions_supplied=%d' % (words, candidates))
    # A local blocker identity exists: after S,A,A, the next A candidate is stale.
    w = (-1, 1, 1, 1)
    assert 3 in dict(signatures(w))[3]
    print('local_SAAA_lag3_positive_control=PASS')


if __name__ == '__main__':
    main()
