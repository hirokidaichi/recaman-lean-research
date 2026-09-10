#!/usr/bin/env python3
"""Independent modular-time replay of H-07's positive-periodic embedding."""
import hashlib
import json
from pathlib import Path
import subprocess


def audit(r):
    m = r*r-1
    # Construct the seven runs directly, not via sharp() or first_p2().
    old = [1]*m+[-1]*m+[1]+[-1]*(m+1)+[1]*(m+2*r)+[-1,1]+[-1]*(2*r-1)
    chronological = list(reversed(old))+[1,1]
    p = len(chronological)
    e = lambda t: chronological[(t+len(old)) % p]
    assert p == 4*r*r+4*r+1 and sum(chronological) == 3
    assert e(0) == e(1) == 1
    found = []
    for t in (0,1):
        mass = moment = 0
        contacts = []
        for d in range(1,p+1):
            bit = e(t-d)
            mass += bit
            moment += d*bit
            if mass == 1 and moment == 0:
                contacts.append(d)
        found.append(min(contacts))
    assert found == [4*r*r+4*r-1,4*r*r-1]
    return {'r': r, 'period': p, 'signed_period_sum': 3,
            'current_signs': 'AA', 'minimum_lags': found,
            'prefixes_checked': 2*p}


def main():
    print('protocol=H-20260909-07-periodic-audit')
    print('source_revision='+subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
    print('script_sha256='+hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    for r in range(2,65):
        print(('DISCOVERY' if r <= 8 else 'HOLDOUT')+'='+json.dumps(audit(r)),flush=True)
    print('PASS: positive-sum periodic embeddings retain the minimal-lag drop')


if __name__ == '__main__':
    main()
