#!/usr/bin/env python3
"""H-20260907-08: exact finite regression of a hole-only abstraction."""
import hashlib
import itertools
from pathlib import Path
import subprocess


def arc(remaining, entry):
    remaining = set(remaining)
    choices = [v for v in remaining if v % 3 == entry]
    removed = []
    while choices:
        v = max(choices)
        remaining.remove(v)
        removed.append(v)
        choices = [w for w in remaining if w < v and w % 3 == (v - 1) % 3]
    return remaining, removed


def main():
    print('protocol=H-20260907-08 frozen subsets 1..12; paper-proof regression, no holdout claim')
    print('source_revision=' + subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip())
    print('source_sha256=' + hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    schedules = list(itertools.permutations(range(3)))
    schedule_trials = 0
    max_greedy_arcs = 0
    max_schedule_attempts = 0
    for mask in range(1 << 12):
        original = {i + 1 for i in range(12) if (mask >> i) & 1}
        remaining = original.copy()
        used = 0
        while remaining:
            old_size = len(remaining)
            remaining, removed = arc(remaining, max(remaining) % 3)
            assert removed and len(remaining) < old_size
            used += 1
        assert used <= len(original)
        max_greedy_arcs = max(max_greedy_arcs, used)
        for order in schedules:
            remaining = original.copy()
            attempts = 0
            while remaining:
                remaining, _ = arc(remaining, order[attempts % 3])
                attempts += 1
                assert attempts <= 3 * len(original)
            schedule_trials += 1
            max_schedule_attempts = max(max_schedule_attempts, attempts)
    print(f'exhaustive_subsets=4096 greedy_max_arcs={max_greedy_arcs} violations=0')
    print(f'fixed_schedule_trials={schedule_trials} max_attempts={max_schedule_attempts} violations=0')
    for k in [0, 1, 2, 12, 100, 1000]:
        remaining = {3 * i + 1 for i in range(k)}
        used = 0
        while remaining:
            remaining, removed = arc(remaining, 1)
            assert len(removed) == 1
            used += 1
        assert used == k
        print(f'single_residue_size={k} required_nonempty_arcs={used}')

    values, seen, first = [0], {0}, {0: 0}
    for n in range(1, 99735):
        candidate = values[-1] - n
        value = candidate if candidate > 0 and candidate not in seen else values[-1] + n
        values.append(value)
        seen.add(value)
        first.setdefault(value, n)
    targets = {4, 5, 19}
    assert not (targets & set(values[:129]))
    assert {m: first[m] for m in targets} == {4: 131, 5: 129, 19: 99734}
    print('canonical_control: M={4,5,19} absent_through=128 all_appear_by=99734')
    print('canonical_first_hits=' + str(sorted((m, first[m]) for m in targets)))
    print('PASS: finite checks support the abstraction proof only; no canonical non-surjectivity conclusion')


if __name__ == '__main__':
    main()
