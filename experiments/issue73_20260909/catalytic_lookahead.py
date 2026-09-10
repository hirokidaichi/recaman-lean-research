#!/usr/bin/env python3
"""Frozen H-20260909-02: at most one future S, with one k=2 repair.

No least-potential table is loaded. Newest sign is bit zero, A=1.
The candidate is evaluated by its uniform A-block formula.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess


def lags(m: int, L: int) -> list[int]:
    s = moment = 0
    hits = []
    for i in range(1, L + 1):
        e = 1 if m & (1 << (i - 1)) else -1
        s += e
        moment += i * e
        if (s, moment) == (1, 0):
            hits.append(i)
    return hits


def word(m: int, L: int) -> str:
    return ''.join('A' if m & (1 << i) else 'S' for i in range(L))


def mask(w: str) -> int:
    return sum(1 << i for i, c in enumerate(w) if c == 'A')


def tables(L: int, k: int):
    size = 1 << L
    bound = size - 1
    supply = bytearray(bool(lags(m, L)) for m in range(size))
    base = []
    for m in range(size):
        u, total = m, 0
        for _ in range(L):
            total += supply[u]
            u = ((u << 1) | 1) & bound
        base.append(total)
    values = [base]
    for _ in range(k):
        prev = values[-1]
        current = []
        for m in range(size):
            u, prefix, best = m, 0, base[m]
            for _r in range(L + 1):
                best = max(best, prefix - 1 + prev[(u << 1) & bound])
                prefix += supply[u]
                u = ((u << 1) | 1) & bound
            current.append(best)
        values.append(current)
    return supply, values


def maximizing_future(m: int, L: int, k: int, supply, values) -> str:
    if values[k][m] == values[0][m]:
        return 'A' * L
    u, prefix, bound = m, 0, (1 << L) - 1
    for r in range(L + 1):
        v = (u << 1) & bound
        if prefix - 1 + values[k-1][v] == values[k][m]:
            return 'A' * r + 'S' + maximizing_future(v, L, k-1, supply, values)
        prefix += supply[u]
        u = ((u << 1) | 1) & bound
    raise AssertionError('no maximizing future')


def replay(w: str, future: str) -> dict:
    """Independent string/arithmetic replay, no bit supply checker."""
    history = list(reversed(w))
    L, total, trace = len(w), 0, []
    for clock, b in enumerate(future):
        contacts = []
        if b == 'A':
            for d in range(1, L + 1):
                past = list(reversed(history[-d:]))
                signed = [1 if c == 'A' else -1 for c in past]
                sums = (sum(signed), sum(i * e for i, e in enumerate(signed, 1)))
                if sums == (1, 0):
                    contacts.append({'d': d, 'sum': sums[0], 'moment': sums[1]})
        charge = int(bool(contacts)) if b == 'A' else -1
        total += charge
        if charge:
            trace.append({'step': clock+1, 'bit': b, 'charge': charge,
                          'contacts': contacts})
        history.append(b)
    return {'future': future, 'score': total, 'nonzero_steps': trace}


def enumerate_string_max(w: str, k: int) -> dict:
    """Exhaust all <=k-S futures with each A block of length <=L.

    Separate from the table recurrence. Also permits stopping early.
    """
    from itertools import product
    L, best, winner = len(w), 0, ''
    for s_count in range(k + 1):
        for blocks in product(range(L + 1), repeat=s_count + 1):
            future = 'S'.join('A' * n for n in blocks)
            score = replay(w, future)['score']
            if score > best:
                best, winner = score, future
    return {'score': best, 'future': winner}


def edge_record(m: int, L: int, k: int, bit: int, supply, values) -> dict:
    v = ((m << 1) | bit) & ((1 << L) - 1)
    charge = int(supply[m]) if bit else -1
    out = {'L': L, 'k': k, 'from': word(m, L), 'bit': 'A' if bit else 'S',
           'to': word(v, L), 'charge': charge, 'Rfrom': values[k][m],
           'Rto': values[k][v], 'potential_slack': values[k][m]-values[k][v]-charge}
    for key, state in [('before', m), ('after', v)]:
        future = maximizing_future(state, L, k, supply, values)
        exact = replay(word(state, L), future)
        assert exact['score'] == values[k][state]
        out[key] = exact
    return out


def run(k: int):
    for L in (3, 7, 11, 15, 19):
        supply, values = tables(L, k)
        stage = 'discovery' if L <= 11 else 'conditional_holdout'
        if L in (7, 11):
            named = [('AAAASSS', 0)] if L == 7 else [
                ('SSAAAAAASSS', 1), ('AAASAASSSSS', 0), ('AASSSSAAASS', 1)]
            for w, b in named:
                print('CONTROL=' + json.dumps(edge_record(mask(w), L, k, b, supply, values)), flush=True)
        fail_a = fail_s = 0
        first = None
        for m in range(1 << L):
            for bit in (0, 1):
                v = ((m << 1) | bit) & ((1 << L)-1)
                charge = int(supply[m]) if bit else -1
                if values[k][m] < values[k][v] + charge:
                    fail_a += bit
                    fail_s += 1-bit
                    if first is None:
                        first = (m, bit)
        print('STAGE=' + json.dumps({'k': k, 'L': L, 'stage': stage,
              'states': 1 << L, 'fail_A': fail_a, 'fail_S': fail_s,
              'max_R': max(values[k])}), flush=True)
        if first is not None:
            m, bit = first
            record = edge_record(m, L, k, bit, supply, values)
            for key in ('from', 'to'):
                independent = enumerate_string_max(record[key], k)
                assert independent['score'] == record['Rfrom' if key == 'from' else 'Rto']
                record['independent_' + key] = independent
            print('REFUTED=' + json.dumps(record), flush=True)
            return record
    print('FINITE_ONLY=' + json.dumps({'k': k, 'status': 'COMPUTED', 'max_L': 19}), flush=True)
    return None


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--k', type=int, choices=(1, 2), required=True)
    args = parser.parse_args()
    print('protocol=H-20260909-02', flush=True)
    print('source_revision=' + subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(), flush=True)
    print('script_sha256=' + hashlib.sha256(Path(__file__).read_bytes()).hexdigest(), flush=True)
    print('orientation=windows-newest-first; futures-forward', flush=True)
    # The unchanged moment equation must rule out all-A self-loop supply.
    assert all(lags((1 << L)-1, L) == [] for L in (3, 7, 11))
    print('NEGATIVE_CONTROL=without_moment_all_A_lag1_has_sum1_and_positive_self_loop', flush=True)
    run(args.k)


if __name__ == '__main__':
    main()
