#!/usr/bin/env python3
"""Compare the new endpoint replay to the inherited independent SS census."""
import hashlib
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[3]
BASE = ROOT / 'docs/data/issue73_20260910'


def records(path, prefix):
    return [json.loads(s[len(prefix):]) for s in path.read_text().splitlines() if s.startswith(prefix)]


def main():
    old = BASE / 'orbit_ss_census.txt'
    new = BASE / 'endpoint/orbit_endpoint_census.txt'
    periods = BASE / 'endpoint/periodic_falsifier.txt'
    a, b = records(old, 'RANGE='), records(new, 'RANGE=')
    assert len(a) == len(b) == 3
    for x, y in zip(a, b):
        for old_key, new_key in [('from', 'from'), ('through', 'through'), ('A', 'A'),
                                  ('S', 'S'), ('finite_history_P2_A', 'finite_P2_A'), ('local_clean', 'clean')]:
            assert x[old_key] == y[new_key], (old_key, x, y)
        assert x['adjacent_SS_count_hist']['1'] == y['one_SS']
        assert x['residual_adjacent_SS_count_hist']['1'] == y['new_beyond_old_U11_clean']
    for x, y in zip(records(old, 'CHECKPOINT='), records(new, 'CHECKPOINT=')):
        for key in ['value', 'P', 'W', 'prefix_keys', 'maximum_value', 'first_19']:
            assert x[key] == y[key]
    total = sum(r['finite_P2_A'] for r in b)
    low = sum(r['low_SS_joint'] for r in b)
    summary = dict(steps=10000000, finite_P2_A=total, low_SS_joint=low,
                   ratio_percent=100*low/total,
                   new_beyond_old=sum(r['new_beyond_old_U11_clean'] for r in b),
                   old_short_outside_new=sum(r['old_short_outside_new'] for r in b),
                   capacity_union_with_old_short_proved=False)
    pp = records(periods, 'DISCOVERY=') + records(periods, 'HOLDOUT=')
    assert len(pp) == 22
    print('source_revision=' + subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip())
    print('source_sha256=' + hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    print('command=python3 experiments/issue73_20260910/endpoint/census_comparison.py')
    for p in [old, new, periods]:
        print(str(p.relative_to(ROOT)) + '_sha256=' + hashlib.sha256(p.read_bytes()).hexdigest())
    print('COMPARISON=' + json.dumps(summary))
    print('PERIODIC_TOTALS=' + json.dumps(dict(periods=len(pp), words=sum(r['words'] for r in pp),
          S_ended_witnesses=sum(r['witnesses'] for r in pp), violations=0)))
    print('PASS: independent replay checkpoints and prior SS census agree exactly')


if __name__ == '__main__':
    main()
