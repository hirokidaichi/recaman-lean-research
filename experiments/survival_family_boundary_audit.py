#!/usr/bin/env python3
"""Fixed boundary and weakened-clearance audit for H-20260907-01.

The final case is a negative control, not an admissible parameter choice.
"""
import hashlib
from pathlib import Path
import subprocess

CASES = [([], 2, 10), ([0, 1, 3, 9], 10, 14),
         ([7, 99, 301], 302, 24), ([], 2, 30), ([], 20, 10)]


def main():
    print('source_revision=' + subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip())
    print('source_sha256=' + hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    for f, w, d in CASES:
        v, j = d*d+w, (d*d+w)//2
        h = v+1+3*j
        n = 16*h+2*(h%2)
        b, c, value = n-2, n+2*j+1, 3*n+h-1
        seen = set(f) | {0, value, v-1}
        seen.update(v+3*t for t in range(1, j+1))
        seen.update((p-2)*c+v+p*(p-3)//2 for p in range(4, d+1))
        previous_residue = value % b
        outcome = 'PASS'
        for clock, expected in enumerate('SS'+'AS'*j+'S'+'A'*d+'S'*d, b+1):
            candidate = value-clock
            sign = 'S' if candidate > 0 and candidate not in seen else 'A'
            if sign != expected:
                outcome = (clock, candidate, sign, expected)
                break
            value = candidate if sign == 'S' else value+clock
            seen.add(value)
            assert value % clock <= previous_residue
            previous_residue = value % clock
        if d*d-8*d > w:
            assert outcome == 'PASS' and value == w
        else:
            assert outcome == (4957, 9937, 'A', 'S')
        print(f'F={f} w={w} D={d} strict={d*d-8*d>w} outcome={outcome} final={value}')


if __name__ == '__main__':
    main()
