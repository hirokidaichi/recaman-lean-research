#!/usr/bin/env python3
"""Frozen H-20260907-09 Hall falsifier. Exact finite words, not actual orbits."""
import argparse
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
import subprocess

DEPENDENCY = Path(__file__).resolve().parents[1] / 'parallel20260907/periodic_search.py'
spec = importlib.util.spec_from_file_location('periodic_supply', DEPENDENCY)
supply = importlib.util.module_from_spec(spec)
spec.loader.exec_module(supply)


def domains(word):
    signatures = supply.suppliers(word)
    p = len(word)
    return signatures, {
        t: {(t-i) % p for i in range(1, min(lags)+1) if word[(t-i) % p] == -1}
        for t, lags in signatures.items() if lags
    }


def match_or_deficiency(neighbors):
    owner = {}

    def augment(t, visited):
        for s in sorted(neighbors[t]):
            if s in visited:
                continue
            visited.add(s)
            if s not in owner or augment(owner[s], visited):
                owner[s] = t
                return True
        return False

    for t in neighbors:
        augment(t, set())
    if len(owner) == len(neighbors):
        return owner, None
    left = set(neighbors) - set(owner.values())
    right = set()
    todo = list(left)
    while todo:
        t = todo.pop()
        for s in neighbors[t]:
            right.add(s)
            if s in owner and owner[s] not in left:
                left.add(owner[s])
                todo.append(owner[s])
    assert right == set().union(*(neighbors[t] for t in left))
    assert len(right) < len(left)
    return owner, (left, right)


def brute_hall(neighbors):
    vertices = list(neighbors)
    for bits in range(1 << len(vertices)):
        chosen = [t for i, t in enumerate(vertices) if bits >> i & 1]
        union = set().union(*(neighbors[t] for t in chosen))
        if len(union) < len(chosen):
            return False
    return True


def controls():
    for text in ('A', 'AA', 'SAAA', 'SSSSAAAASAAA'):
        word = tuple(1 if c == 'A' else -1 for c in text)
        signatures, neighbors = domains(word)
        assert signatures == supply.naive(word)
        owner, deficient = match_or_deficiency(neighbors)
        assert deficient is None
        if text == 'SAAA':
            assert neighbors == {3: {0}}
        print('control=' + json.dumps({'word': text, 'domains': {t: sorted(v) for t, v in neighbors.items()},
                                      'matching': sorted((t, s) for s, t in owner.items())}), flush=True)
    # Removing the moment condition would admit lag 1 at both A phases of AA.
    weak = {0: set(), 1: set()}
    assert match_or_deficiency(weak)[1] is not None
    assert not brute_hall(weak)
    checked = 0
    for p in range(1, 9):
        for word in itertools.product((-1, 1), repeat=p):
            if sum(word) <= 0:
                continue
            signatures, neighbors = domains(word)
            assert signatures == supply.naive(word)
            assert (match_or_deficiency(neighbors)[1] is None) == brute_hall(neighbors)
            checked += 1
    print(f'independent_lag_and_all_subset_checks=PASS positive_words={checked}', flush=True)
    print('moment_removed_AA_negative_control=PASS', flush=True)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--mode', choices=('discovery', 'holdout'), required=True)
    args = parser.parse_args()
    print('protocol=H-20260907-09 minimum-P2-lag S-domain Hall condition', flush=True)
    print('source_base_revision=b4b5afaaac126acaa0c4fc0042bdaa4fafd289a1', flush=True)
    print('current_revision=' + subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(), flush=True)
    print('source_sha256=' + hashlib.sha256(Path(__file__).read_bytes()).hexdigest(), flush=True)
    print('dependency_sha256=' + hashlib.sha256(DEPENDENCY.read_bytes()).hexdigest(), flush=True)
    controls()
    total = 0
    lo, hi = (1, 12) if args.mode == 'discovery' else (13, 18)
    for p in range(lo, hi+1):
        count = 0
        for word in itertools.product((-1, 1), repeat=p):
            if sum(word) <= 0:
                continue
            signatures, neighbors = domains(word)
            count += 1
            total += 1
            owner, deficient = match_or_deficiency(neighbors)
            if deficient is not None:
                assert signatures == supply.naive(word)
                left, right = deficient
                witness = {'period': p, 'word': ''.join('A' if e == 1 else 'S' for e in word),
                           'sum': sum(word), 'A_count': sum(e == 1 for e in word),
                           'D_count': sum(e == -1 for e in word), 'U_count': len(neighbors),
                           'all_lags': signatures, 'minimum_lag_S_domains': {t: sorted(v) for t, v in neighbors.items()},
                           'deficient_left': sorted(left), 'neighbor_union': sorted(right),
                           'matching_size': len(owner), 'cumulative_words': total}
                print('HALL_COUNTEREXAMPLE=' + json.dumps(witness, sort_keys=True), flush=True)
                print('STOP: this Hall class is refuted; weaker claims require separate count checks', flush=True)
                return
        print(f'period={p} positive_words={count} Hall_failures=0', flush=True)
    print(f'COMPLETE mode={args.mode} positive_words={total} Hall_failures=0; finite evidence only', flush=True)


if __name__ == '__main__':
    main()
