#!/usr/bin/env python3
"""Read-only provenance checks; run from the repository root."""
import argparse
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
BUNDLE = ROOT / 'docs/data/issue73_20260910'

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--manifest', action='store_true')
    args = parser.parse_args()
    print('protocol=2026-09-10 provenance audit')
    print('source_sha256=' + digest(Path(__file__)))
    old = ROOT / 'docs/data/issue73_20260909/SHA256SUMS'
    overrides = {
        name: BUNDLE / 'baseline' / (name.replace('/', '__') + '.txt')
        for name in ['Recaman.lean', 'Recaman/Audit.lean',
                     'Recaman/LeadingRunSupply.lean', 'Recaman/SharpPeriodicSupply.lean',
                     'docs/MODULE_IMPORT_CONTRACTS.tsv']
    }
    count = 0
    for line in old.read_text().splitlines():
        expected, name = line.split('  ', 1)
        target = overrides.get(name, ROOT / name)
        assert digest(target) == expected, ('old manifest mismatch', name, str(target))
        count += 1
    print('BASELINE=' + json.dumps(dict(entries=count, preserved_snapshots=len(overrides), verified=True)))
    candidates = list((ROOT / 'experiments').rglob('*.py')) + list((ROOT / 'experiments').rglob('*.cpp'))
    records = []
    for log in sorted(BUNDLE.glob('*.txt')):
        if log.name.startswith(('check', 'provenance_')):
            continue
        for key, expected in re.findall(r'^([^\n=]*sha256)=([a-f0-9]{64})$', log.read_text(), re.M):
            if log.stem == 'eventual_periodic_bridge_control_clock_error':
                choices = [BUNDLE / 'baseline/eventual_periodic_bridge_control_clock_error.py.txt']
            elif key in ('source_sha256', 'script_sha256'):
                choices = [p for p in candidates if p.stem == log.stem]
            elif key == 'generator_sha256':
                choices = [ROOT / 'experiments/issue73_20260910/bounded_excess_multiplicity.py']
            elif key == 'solver_sha256':
                choices = [ROOT / 'experiments/parallel20260907/periodic_search.py']
            else:
                basename = key.removesuffix('_sha256')
                choices = [p for p in candidates if p.name == basename]
            matching = [p for p in choices if digest(p) == expected]
            assert matching, ('logged source hash mismatch', log.name, key, expected, [str(p) for p in choices])
            records.append(dict(log=log.name, key=key, source=str(matching[0].relative_to(ROOT))))
    for record in records:
        print('SOURCE=' + json.dumps(record))
    print('LOGGED_SOURCE_HASHES=' + str(len(records)))
    if args.manifest:
        manifest = BUNDLE / 'SHA256SUMS'
        count = 0
        for line in manifest.read_text().splitlines():
            expected, name = line.split('  ', 1)
            assert digest(ROOT / name) == expected, ('new manifest mismatch', name)
            count += 1
        print('CURRENT_MANIFEST=' + json.dumps(dict(entries=count, verified=True)))
    print('PASS: historical snapshots and recorded source identities agree')

if __name__ == '__main__':
    main()
