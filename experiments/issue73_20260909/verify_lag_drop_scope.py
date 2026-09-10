#!/usr/bin/env python3
"""H-07's one-word scope control, using the existing all-lag solver."""
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess


def main():
    dependency = Path(__file__).resolve().parents[1]/'parallel20260907/periodic_search.py'
    spec = importlib.util.spec_from_file_location('periodic_supply', dependency)
    supply = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(supply)
    print('protocol=H-20260909-07-scope-control-r2-only')
    print('source_revision='+subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
    print('script_sha256='+hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    print('dependency_sha256='+hashlib.sha256(dependency.read_bytes()).hexdigest())
    past = 'AAASSSASSSSAAAAAAASASSS'
    chronological = past[::-1]+'AA'
    word = [1 if c == 'A' else -1 for c in chronological]
    assert len(word) == 25 and sum(word) == 3
    signatures = supply.suppliers(word)
    assert signatures == supply.naive(word)
    assert min(signatures[23]) == 23 and min(signatures[24]) == 15
    supplied = sum(bool(v) for v in signatures.values())
    result = {'chronological_word': chronological, 'period': 25,
              'signed_sum': 3, 'A': 14, 'D': 11, 'supplied_A': supplied,
              'all_lag_signatures': signatures, 'direct_replay_agrees': True}
    print(json.dumps(result,sort_keys=True))
    assert supplied <= 11
    print('PASS: this concrete lag-drop counterexample is not an E-067/E-070 counterword')


if __name__ == '__main__':
    main()
