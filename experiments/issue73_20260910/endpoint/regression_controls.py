#!/usr/bin/env python3
"""Check stopped endpoint rules and independently replay the canonical boundary."""
import hashlib
import json
from pathlib import Path
import subprocess
from finite_verifier import data, parse


def main():
    print('protocol=H-20260910-28 stopped-branch and canonical controls')
    print('source_revision=' + subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip())
    print('source_sha256=' + hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    print('finite_verifier_sha256=' + hashlib.sha256(Path(__file__).with_name('finite_verifier.py').read_bytes()).hexdigest())
    print('command=python3 experiments/issue73_20260910/endpoint/regression_controls.py')
    word = 'SSSSAAAASAAA'
    out = []
    for t in (7, 11):
        back = ''.join(word[(t-d) % len(word)] for d in range(1, len(word)*(len(word)+1)+1))
        d = data(parse(back))[3][0]
        out.append(dict(phase=t, lag=d, SS=data(parse(back[:d]))[2], endpoint=(t-d) % len(word)))
    assert out == [dict(phase=7, lag=11, SS=3, endpoint=8), dict(phase=11, lag=3, SS=0, endpoint=8)]
    print('E069=' + json.dumps(dict(period=12, word=word, sources=out, first_excluded_by_low_SS=True)))
    abstract = 'SAAASAASSSA'
    assert data(parse(abstract)) == (1, 0, 2, [11])
    print('E073=' + json.dumps(dict(word=abstract, SS=2, minimum_lag=11, endpoint='A', NoSAAS=False)))
    values = [0]
    signs = []
    seen = {0}
    for n in range(1, 116):
        candidate = values[-1] - n
        sub = candidate > 0 and candidate not in seen
        signs.append('S' if sub else 'A')
        value = candidate if sub else values[-1] + n
        values.append(value)
        seen.add(value)
    back = ''.join(signs[114-d] for d in range(1, 12))
    assert back == 'AAASSSASASA' and data(parse(back)) == (1, 0, 2, [11])
    assert signs[114] == signs[103] == 'A'
    assert values[114] == values[103]+115
    assert 'SAAS' not in back
    print('CANONICAL=' + json.dumps(dict(step=115, sign_time=114, backward_word=back,
          minimum_lag=11, SS=2, endpoint_time=103, endpoint_sign=signs[103],
          current_sign=signs[114], a103=values[103], a114=values[114], a115=values[115], NoSAAS=True)))
    print('PASS: stopped controls remain outside the theorem; canonical step115 independently agrees')


if __name__ == '__main__':
    main()
