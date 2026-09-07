#!/usr/bin/env python3
"""Exact phase/weight decomposition of the first frozen H-08 counterexample."""
import argparse
from collections import Counter
import hashlib
from pathlib import Path

C, E, J = 11685598221, 11685741477, 276986
BEGIN, END = C - 2 * J - 3, E + 1


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('trace', type=Path)
    args = parser.parse_args()
    data = args.trace.read_bytes()
    rows = {}
    for line in data.decode().splitlines():
        if not line or line.startswith('#'):
            continue
        f = line.split()
        t, value, q, r = map(int, f[:4])
        assert t not in rows and value == q * t + r and 0 <= r < t
        rows[t] = (value, q, r, f[4])
    assert len(rows) == END - BEGIN + 1
    assert min(rows) == BEGIN and max(rows) == END
    assert rows[C][0] == 4318940415 and rows[E][0] == 4318376915
    weights = Counter()
    for t in range(BEGIN + 1, END + 1):
        prev, cur = rows[t - 1], rows[t]
        assert cur[0] == prev[0] + (t if cur[3] == 'A' else -t)
        assert cur[2] <= prev[2]
        assert cur[1] == prev[1] + (1 if cur[3] == 'A' else -1)
        assert cur[2] == prev[2] - prev[1]
        if C < t <= E and cur[3] == 'A':
            weights[prev[1]] += 1
    drop = rows[C][0] - rows[E][0]
    total = sum((2 * q + 1) * n for q, n in weights.items())
    assert total == drop
    assert all(rows[t][1] > 0 for t in range(C + 1, E))
    # The run's level-two visited rail includes the extra SS middle output.
    base = 2 * C + rows[C][0]
    rail_lo, rail_hi = base - J - 1, base - 1
    assert all(rows[C - 2 * i][0] == base - i for i in range(1, J + 2))
    first_return = next(t for t in range(C + 3, E) if rows[t][1] == 2)
    assert first_return == E - 2 and rows[first_return][3] == 'S'
    print('diagnostic=H-20260906-08 first counterexample, no refitted conjecture')
    print('script_sha256=' + hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    print('trace_sha256=' + hashlib.sha256(data).hexdigest())
    print(f'trace_rows={len(rows)} recurrence/residue/quotient checks=PASS')
    print(f'c={C} v={rows[C][0]} J={J} e={E} u={rows[E][0]}')
    print(f'drop={drop} gap={E-C} 3drop-7J={3*drop-7*J}')
    print('addition_weights_(starting_q,count,total)=' + str(
        [(q, n, (2*q+1)*n) for q, n in sorted(weights.items())]))
    print(f'rail=[{rail_lo},{rail_hi}] first_q2_return={first_return} '
          f'value={rows[first_return][0]} distance_below_rail={rail_lo-rows[first_return][0]}')
    print(f'drop-2gap={drop-2*(E-C)} J+2={J+2}')
    print('maximal two-level alternating segments: start end levels steps residue_start residue_end')
    t = C
    while t < E:
        end = t + 1
        levels = tuple(sorted((rows[t][1], rows[end][1])))
        while end < E and rows[end+1][1] == rows[end-1][1]:
            end += 1
        print(t, end, levels, end-t, rows[t][2], rows[end][2])
        t = end


if __name__ == '__main__':
    main()
