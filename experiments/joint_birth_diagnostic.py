#!/usr/bin/env python3
"""H-20260907-02: fixed joint-birth observer on the existing exact simulator.

Only watched-value instrumentation is replaced. The recurrence, membership,
section lookahead and interval insertion code are byte-for-byte unchanged.
"""
import argparse
import hashlib
from pathlib import Path
import re
import subprocess
import tempfile

SOURCE = Path(__file__).with_name('run_length_recaman_simulator.cpp')
C, V, LAST = 11685598221, 4318940415, 31057
HORIZON = 11685741478
BOUNDARIES = {27690136859: 11657331305, 39375735083: 11684552030,
              39375735080: 11684552036, 39375641912: 7575011311,
              27689981566: 11656976131, 27689859871: 11685044249,
              27689859868: 11685741475}
FIELDS = 'value birth sign section_start section_value section_pairs j side'.split()


def instrument(source, targets):
    patched, count = re.subn(
        r'constexpr std::size_t kWatchedCount = 8U;\s*'
        r'constexpr Nat kWatched\[kWatchedCount\] = \{.*?\};',
        'constexpr std::size_t kWatchedCount = '+str(len(targets))+'U;\n'
        'constexpr Nat kWatched[kWatchedCount] = {'+
        ','.join(str(t)+'ULL' for t in targets)+'};', source, count=1, flags=re.DOTALL)
    assert count == 1
    old = '''    for (std::size_t w = 0U; w < kWatchedCount; ++w)
      if (value_ == kWatched[w]) Watched_(w, clock);'''
    new = '''    const Nat* hit = std::lower_bound(kWatched, kWatched+kWatchedCount, value_);
    if (hit != kWatched+kWatchedCount && *hit == value_)
      Watched_(static_cast<std::size_t>(hit-kWatched), clock,
               subtract ? 'S' : 'A', 0U, 0U, 0U, 0U, 'P');'''
    assert patched.count(old) == 1
    patched = patched.replace(old, new)
    old = '''    for (std::size_t w = 0U; w < kWatchedCount; ++w) {
      const Nat x = kWatched[w];
      if (lower_lo <= x && x <= lower_hi) Watched_(w, n + 2U * (lower_hi - x));
      if (v + 1U <= x && x <= v + pairs) Watched_(w, n + 2U * (x - v - 1U) + 1U);
    }'''
    new = '''    const Nat* finish = kWatched+kWatchedCount;
    for (const Nat* p = std::lower_bound(kWatched, finish, lower_lo);
         p != finish && *p <= lower_hi; ++p) {
      const Nat j = lower_hi-*p;
      Watched_(static_cast<std::size_t>(p-kWatched), n+2U*j,
               'S', n, v, pairs, j, 'L');
    }
    for (const Nat* p = std::lower_bound(kWatched, finish, v+1U);
         p != finish && *p <= v+pairs; ++p) {
      const Nat j = *p-v-1U;
      Watched_(static_cast<std::size_t>(p-kWatched), n+2U*j+1U,
               'A', n, v, pairs, j, 'U');
    }'''
    assert patched.count(old) == 1
    patched = patched.replace(old, new)
    old = '''  void Watched_(std::size_t w, Nat clock) {
    ++watched_landings_[w];
    if (watched_first_clock_[w] == 0U) watched_first_clock_[w] = clock;
  }'''
    new = '''  void Watched_(std::size_t w, Nat clock, char sign,
                Nat n, Nat v, Nat pairs, Nat j, char side) {
    ++watched_landings_[w];
    if (watched_first_clock_[w] == 0U) {
      watched_first_clock_[w] = clock;
      std::cout << "birth " << kWatched[w] << ' ' << clock << ' ' << sign
                << ' ' << n << ' ' << v << ' ' << pairs << ' ' << j
                << ' ' << side << '\\n';
    }
  }'''
    assert patched.count(old) == 1
    return patched.replace(old, new)


def run(binary, horizon, mode, start):
    result = subprocess.run([str(binary), str(horizon), mode, str(start)],
                            text=True, capture_output=True, check=True)
    births = {}
    final = ''
    for line in result.stdout.splitlines():
        if line.startswith('birth '):
            raw = line.split()[1:]
            row = {key: (value if key in ('sign', 'side') else int(value))
                   for key, value in zip(FIELDS, raw, strict=True)}
            assert row['value'] not in births
            births[row['value']] = row
            if row['side'] != 'P':
                n, v, j = row['section_start'], row['section_value'], row['j']
                assert 0 <= j < row['section_pairs']
                assert row['birth'] == n+2*j+(row['side'] == 'U')
                assert row['value'] == (v-n-j if row['side'] == 'L' else v+j+1)
        if line.startswith('final '):
            final = line
    return births, final


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    source = SOURCE.read_text()
    print('protocol=H-20260907-02 diagnostic; not a fitted conjecture', flush=True)
    print('source_revision='+subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(), flush=True)
    print('reference_sha256='+hashlib.sha256(source.encode()).hexdigest(), flush=True)
    with tempfile.TemporaryDirectory(prefix='recaman-joint-birth-') as directory:
        cpp, binary = Path(directory)/'observer.cpp', Path(directory)/'observer'
        def build(targets):
            generated = instrument(source, targets)
            cpp.write_text(generated)
            subprocess.run(['c++','-O3','-std=c++20','-Wall','-Wextra','-Wpedantic',
                            '-Werror',str(cpp),'-o',str(binary)], check=True)
            return hashlib.sha256(generated.encode()).hexdigest()
        build(list(range(1, 4001)))
        small_plain, _ = run(binary, 20000, 'plain', 1)
        small_accel, _ = run(binary, 20000, 'accel', 1)
        key = lambda rows: {w: (r['birth'], r['sign']) for w, r in rows.items()}
        assert key(small_plain) == key(small_accel)
        print(f'small_plain_accel horizon=20000 targets=1..4000 births={len(small_plain)} PASS', flush=True)
        targets = sorted({3*C+V+5-3*i for i in range(LAST+1)} | BOUNDARIES.keys())
        sha = build(targets)
        print('generated_sha256='+sha, flush=True)
        records, final = run(binary, HORIZON, 'accel', 2097152)
        alternative, final_alt = run(binary, HORIZON, 'accel', 3000000)
        assert key(records) == key(alternative)
        assert len(records) == len(targets)
        for w, birth in BOUNDARIES.items():
            assert records[w]['birth'] == birth
        assert 'final clock=11685741478 value=16004118393 ' in final
        assert 'final clock=11685741478 value=16004118393 ' in final_alt
        table = '\t'.join(FIELDS)+'\n'+''.join('\t'.join(str(records[w][f]) for f in FIELDS)+'\n' for w in targets)
        (args.out/'issue71_births.tsv').write_text(table)
        print(f'all_targets={len(targets)} W={LAST+1} alternate_accel_from=3000000 PASS boundary_births=7 PASS', flush=True)
        print('birth_table_sha256='+hashlib.sha256(table.encode()).hexdigest(), flush=True)
        print(final, flush=True)
        print('observer changes: watched constants, plain observer, section observer, birth output only', flush=True)


if __name__ == '__main__':
    main()
