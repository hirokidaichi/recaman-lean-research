#!/usr/bin/env python3
"""H-20260909-04: independent generators for the sharp P2 class."""
import hashlib
import json
from pathlib import Path
import subprocess


def partitions(total, cap=None):
    if total == 0:
        yield ()
        return
    cap = total if cap is None else min(cap, total)
    for first in range(cap, 0, -1):
        for rest in partitions(total-first, first):
            yield (first,)+rest


def subsets_with_sum(start, end, count, target):
    if count == 0:
        if target == 0:
            yield ()
        return
    if end-start+1 < count:
        return
    smallest = count*(2*start+count-1)//2
    largest = count*(2*end-count+1)//2
    if not smallest <= target <= largest:
        return
    for first in range(start, end-count+2):
        for rest in subsets_with_sum(first+1, end, count-1, target-first):
            yield (first,)+rest


def check(m):
    d = 4*m-1
    constructed = set()
    for parts in partitions(m):
        padded = parts+(0,)*(m-len(parts))
        late = tuple(3*m+i-padded[i] for i in range(m))
        assert len(set(late)) == m
        assert m < min(late) and max(late) <= d
        assert late not in constructed
        constructed.add(late)
    target = m*(4*m-1)-m*(m+1)//2
    independent = set(subsets_with_sum(m+1, d, m, target))
    assert constructed == independent, (m, constructed-independent, independent-constructed)
    digest = hashlib.sha256()
    for late in sorted(independent):
        a_positions = tuple(range(1,m+1))+late
        assert 2*len(a_positions)-d == 1
        assert 2*sum(a_positions)-d*(d+1)//2 == 0
        inverse = tuple(3*m+i-late[i] for i in range(m))
        assert list(inverse) == sorted(inverse, reverse=True)
        assert min(inverse) >= 0 and sum(inverse) == m
        digest.update((json.dumps(late)+'\n').encode())
    return {'m': m, 'd': d, 'partition_words': len(constructed),
            'independent_words': len(independent), 'symmetric_difference': 0,
            'position_sets_sha256': digest.hexdigest()}


def main():
    print('protocol=H-20260909-04')
    print('source_revision='+subprocess.check_output(['git','rev-parse','HEAD'], text=True).strip())
    print('script_sha256='+hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    for m in range(1,25):
        stage = 'BOUNDARY' if m < 3 else 'DISCOVERY' if m <= 8 else 'HOLDOUT'
        print(stage+'='+json.dumps(check(m)), flush=True)
    print('PASS: complete finite sets agree; the all-m bijection needs the paper argument')


if __name__ == '__main__':
    main()
