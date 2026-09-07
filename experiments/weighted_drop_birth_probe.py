#!/usr/bin/env python3
"""Diagnostic replay of seven fixed boundary candidates, after H-08 was refuted.

Only the watched-value array of the existing accelerated simulator is changed.
This is a provenance inspection, not a new fitted inequality or holdout test.
"""
import hashlib
from pathlib import Path
import re
import subprocess
import tempfile

SOURCE = Path(__file__).with_name('run_length_recaman_simulator.cpp')
TARGETS = [27690136859, 39375735083, 39375735080, 39375641912,
           27689981566, 27689859871, 27689859868]
HORIZON = 11685741477


def main() -> None:
    source = SOURCE.read_text()
    patched, count = re.subn(
        r'constexpr std::size_t kWatchedCount = 8U;\s*'
        r'constexpr Nat kWatched\[kWatchedCount\] = \{.*?\};',
        'constexpr std::size_t kWatchedCount = 7U;\n'
        'constexpr Nat kWatched[kWatchedCount] = {' +
        ','.join(str(t) + 'U' for t in TARGETS) + '};',
        source, count=1, flags=re.DOTALL)
    assert count == 1
    print('diagnostic=H-20260906-08 fixed seven phase-boundary candidates', flush=True)
    print('reference_sha256=' + hashlib.sha256(source.encode()).hexdigest(), flush=True)
    print('generated_sha256=' + hashlib.sha256(patched.encode()).hexdigest(), flush=True)
    print('horizon=' + str(HORIZON) + ' mode=accel accelFrom=2097152', flush=True)
    with tempfile.TemporaryDirectory(prefix='recaman-birth-') as directory:
        cpp, binary = Path(directory) / 'probe.cpp', Path(directory) / 'probe'
        cpp.write_text(patched)
        subprocess.run(['c++', '-O3', '-std=c++20', '-Wall', '-Wextra',
                        '-Wpedantic', '-Werror', str(cpp), '-o', str(binary)], check=True)
        result = subprocess.run([str(binary), str(HORIZON), 'accel'],
                                capture_output=True, text=True, check=True)
        for line in result.stdout.splitlines():
            if line.startswith(('value ', 'final ', 'mode=')):
                print(line)
        print('expected final value=4318376915')
        assert 'final clock=11685741477 value=4318376915 ' in result.stdout


if __name__ == '__main__':
    main()
