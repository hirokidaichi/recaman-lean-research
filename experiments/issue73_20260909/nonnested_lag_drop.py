#!/usr/bin/env python3
"""H-20260909-07: replay every prefix of the proposed lag-drop family."""
import hashlib
import json
from pathlib import Path
import subprocess


def sharp(m):
    return [1]*m+[-1]*(m-1)+[1]+[-1]*m+[1]*(m-1)


def first_p2(w):
    mass = moment = 0
    for i, b in enumerate(w, 1):
        mass += b
        moment += i*b
        if mass == 1 and moment == 0:
            return i
    return None


def check(r):
    m = r*r-1
    v = sharp(m+1)[1:]
    tail = [1]*(2*r)+[-1, 1]+[-1]*(2*r-1)
    w = v+tail
    old = first_p2(w)
    new = first_p2([1]+w)
    assert w[:m] == [1]*m and w[m] == -1
    assert old == len(w) == 4*r*r+4*r-1
    assert new == 4*r*r-1 and old-new == 4*r
    assert sum(v) == 0 and sum(i*b for i,b in enumerate(v,1)) == -1
    assert sum(tail) == 1 and sum(i*b for i,b in enumerate(tail,1)) == -4*m-1
    result = {'r': r, 'leading_A': m, 'old_min_lag': old,
              'new_min_lag': new, 'lag_drop': old-new,
              'word_sha256': hashlib.sha256(bytes(b == 1 for b in w)).hexdigest()}
    if r == 2:
        result['word_newest_first'] = ''.join('A' if b == 1 else 'S' for b in w)
    return result


def main():
    print('protocol=H-20260909-07')
    print('source_revision='+subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
    print('script_sha256='+hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    for r in range(2,65):
        print(('DISCOVERY' if r <= 8 else 'HOLDOUT')+'='+json.dumps(check(r)),flush=True)
    print('REFUTED: nesting cannot follow from a long leading A run and minimal supply')
    print('PASS: proposed counterfamily replay; universal family still needs a proof')


if __name__ == '__main__':
    main()
