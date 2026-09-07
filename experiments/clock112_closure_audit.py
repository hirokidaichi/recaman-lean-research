#!/usr/bin/env python3
"""Fixed regression / weakened-history audit for H-20260907-03."""
import hashlib
from pathlib import Path
import subprocess


def main():
    print('protocol=H-20260907-03 fixed endpoints; no new discovery/holdout claim')
    print('source_revision='+subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
    print('source_sha256='+hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    values, seen = [0], {0}
    for clock in range(1,99735):
        candidate = values[-1]-clock
        value = candidate if candidate>0 and candidate not in seen else values[-1]+clock
        values.append(value)
        seen.add(value)
    assert values[4825]==371 and values.index(371)==4825
    assert values[99734]==19
    print('canonical_108_113='+str([(t,values[t]) for t in range(108,114)]))
    assert values[112]<223<=values[113]
    print('local_crossing_at_112=present; full permanent-tail replay is the exclusion domain')
    print('first_371=4825 value_99734=19 PASS')
    assert values[4825]>223 and values[99734]>18 and values[99734]<=19
    assert 4825<99734 and values[99734]<=114
    print('witness_boundaries: 4825@371 not_low_for_223; 99734@19 low_for_19_and_114; not_low_for_18 PASS')
    assert values[4826]!=371
    print(f'weakened_model: canonical through4825, constant371 later; '
          f'no_future_low_for_223; recurrence_break_at4826 actual={values[4826]} fake=371')
    print('finite regression PASS; no computation is assumed by the Lean proof')


if __name__=='__main__':
    main()
