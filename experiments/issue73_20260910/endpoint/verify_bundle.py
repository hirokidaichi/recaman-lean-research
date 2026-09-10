#!/usr/bin/env python3
"""Read-only verification of the endpoint-research artifact manifest and source logs.
Use --revision COMMIT to verify the archived bundle after later research edits.
"""
import argparse
import hashlib
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[3]
BASE = Path('docs/data/issue73_20260910/endpoint')
SOURCE = Path('experiments/issue73_20260910/endpoint')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--revision')
    args = parser.parse_args()

    def read(path):
        if args.revision:
            return subprocess.check_output(['git', 'show', f'{args.revision}:{path}'], cwd=ROOT)
        return (ROOT / path).read_bytes()

    def digest(path):
        return hashlib.sha256(read(path)).hexdigest()

    print('protocol=endpoint research source and artifact audit')
    print('tree=' + (args.revision or 'current working tree'))
    paths = []
    for line in read(BASE / 'SHA256SUMS').decode().splitlines():
        expected, name = line.split('  ', 1)
        assert digest(Path(name)) == expected, ('manifest mismatch', name)
        paths.append(name)
    assert paths and len(set(paths)) == len(paths)
    print('MANIFEST_ENTRIES=' + str(len(paths)))
    sources = {
        'periodic_falsifier': 'periodic_falsifier.cpp',
        'orbit_endpoint_census': 'orbit_endpoint_census.cpp',
        'finite_verifier': 'finite_verifier.py',
        'census_comparison': 'census_comparison.py',
        'repetition_falsifier': 'repetition_falsifier.py',
        'regression_controls': 'regression_controls.py',
    }
    for log, source in sources.items():
        content = read(BASE / (log + '.txt')).decode()
        expected = re.search(r'^source_sha256=([a-f0-9]{64})$', content, re.M)
        assert expected and digest(SOURCE / source) == expected.group(1), ('logged source mismatch', log)
        assert 'PASS:' in content, ('missing successful completion', log)
        print('SOURCE_OK=' + str(SOURCE / source))
    controls = read(BASE / 'regression_controls.txt').decode()
    imported = re.search(r'^finite_verifier_sha256=([a-f0-9]{64})$', controls, re.M)
    assert imported and digest(SOURCE / 'finite_verifier.py') == imported.group(1)
    comparison = read(BASE / 'census_comparison.txt').decode()
    for name, expected in re.findall(r'^([^\n]+\.txt)_sha256=([a-f0-9]{64})$', comparison, re.M):
        assert digest(Path(name)) == expected, ('comparison input changed', name)
    print('PASS: all manifest artifacts, recorded source hashes, and comparison inputs match')


if __name__ == '__main__':
    main()
