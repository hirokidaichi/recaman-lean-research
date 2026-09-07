#!/usr/bin/env python3
"""Independent one-clock-at-a-time first-birth check for all fixed W values.

Adds one observer and a first-seen array to arc_death_rule_probe.cpp. No orbit
or arc logic is changed. Keeps its native arc table and consumer trace.
"""
import argparse
import hashlib
from pathlib import Path
import subprocess
import tempfile

SOURCE = Path(__file__).with_name('arc_death_rule_probe.cpp')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    source = SOURCE.read_text()
    anchor = '    if (lock_.active) OnLockStep(clock, subtract, k, r);'
    observer = '''    if (39375641912ULL <= value_ && value_ <= 39375735083ULL &&
        (39375735083ULL-value_)%3U == 0U) {
      const Nat wi = (39375735083ULL-value_)/3U;
      if (!joint_seen_[wi]) {
        joint_seen_[wi] = true;
        std::cout << "jointbirth " << wi << ' ' << value_ << ' ' << clock
                  << ' ' << (subtract ? 'S' : 'A') << ' ' << arc_.ordinal
                  << ' ' << k << ' ' << r << '\\n';
      }
    }
'''
    assert source.count(anchor) == 1
    generated = source.replace(anchor, observer+'\n'+anchor)
    anchor = '  void Step() {'
    assert generated.count(anchor) == 1
    generated = generated.replace(anchor, '  bool joint_seen_[31058] = {};\n\n'+anchor)
    print('protocol=H-20260907-02 scalar independent observer', flush=True)
    print('source_revision='+subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(), flush=True)
    print('reference_sha256='+hashlib.sha256(source.encode()).hexdigest(), flush=True)
    print('generated_sha256='+hashlib.sha256(generated.encode()).hexdigest(), flush=True)
    with tempfile.TemporaryDirectory(prefix='recaman-scalar-birth-') as directory:
        cpp, binary = Path(directory)/'probe.cpp', Path(directory)/'probe'
        cpp.write_text(generated)
        subprocess.run(['c++','-O3','-std=c++20','-Wall','-Wextra','-Wpedantic','-Werror',
                        str(cpp),'-o',str(binary)], check=True)
        with (args.out/'stdout.txt').open('w') as stdout, (args.out/'stderr.txt').open('w') as stderr:
            subprocess.run([str(binary),'11685741478',str(args.out),
                            '11685044246','11685741478'], stdout=stdout, stderr=stderr, check=True)
    print('scalar replay completed', flush=True)


if __name__ == '__main__':
    main()
