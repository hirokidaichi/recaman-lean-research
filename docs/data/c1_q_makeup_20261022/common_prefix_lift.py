"""Try to lift a relaxed spectrum witness to one actual block prefix.

If all required old windows share a real prefix, their earliest chosen start
cuts out a BlockWord suffix of mass at most max(required mass). This gives
the finite search domain. Prefix deficit zero is checked separately.
"""
import argparse
import json
from pathlib import Path
import time

from c1_constraints import direct


def lift(result, seconds=60):
    w = result.get('relaxed_witness')
    if w is None:
        return dict(status='not_applicable', solver_status=result['status'])
    tail = w['tail']
    local = direct(tail)['endable']
    # An old flag at an already local-supplied clock can be cleared without
    # changing E, d or an. Only causal old flags need a common prefix.
    required = {(row['mass'], row['required_area']) for row in w['old_flags'] if not local[row['b']]}
    ignored = [row['b'] for row in w['old_flags'] if local[row['b']]]
    max_mass = max((r for r, a in required), default=0)
    target_e = w['endable']
    started = time.monotonic()
    counts = dict(words=0, joint_signatures=0, exact_E_patterns=0)
    complete = True
    actual = None
    partial = None
    atoms = [(1, 'A'), (2, 'SAAA'), (4, 'SSAAAASAAA')]
    def visit(prefix, mass):
        nonlocal complete, actual, partial
        counts['words'] += 1
        if time.monotonic()-started > seconds:
            complete = False
            return
        f, g = [0], [0]
        for c in prefix:
            f.append(f[-1]+(1 if c == 'A' else -1))
            g.append(g[-1]+f[-1])
        n = len(prefix)
        signature = {(f[n]-f[t], g[n]-g[t]-(n-t)*f[t]) for t in range(n)}
        if required <= signature:
            counts['joint_signatures'] += 1
            check = direct(prefix+tail)
            if check['endable'][n:] == target_e:
                counts['exact_E_patterns'] += 1
                item = dict(prefix=prefix, k1=n, q0=n+len(tail), word=prefix+tail,
                            prefix_deficit=check['d'][n], prefix_nonnegative=min(check['d'][:n+1]) >= 0,
                            actual=check)
                if check['d'][n] == 0 and item['prefix_nonnegative']:
                    assert check['d'][-1] == 1
                    assert min(check['d'][n+1:]) >= 1
                    assert check['an'][-1]-check['an'][n] <= 3
                    assert min(check['F'][n:]) <= check['F'][n]-5
                    actual = item
                    return
                if partial is None:
                    partial = item
        for dm, atom in atoms:
            if mass+dm <= max_mass:
                visit(prefix+atom, mass+dm)
                if not complete or actual is not None:
                    return
    visit('', 0)
    out = dict(status='actual_numeric_lift' if actual is not None else
               'common_pattern_only' if counts['exact_E_patterns'] else
               'no_common_prefix' if complete else 'incomplete',
               complete=complete and actual is None, stopped_on_lift=actual is not None,
               max_prefix_mass=max_mass, counts=counts, ignored_redundant_old_flags=ignored,
               elapsed_seconds=time.monotonic()-started,
               no_completed_D_or_IH_check=True)
    if actual is not None:
        out['actual_lift'] = actual
    if partial is not None:
        out['partial_lift'] = partial
    return out


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('relaxed_result', type=Path)
    ap.add_argument('--out', type=Path, required=True)
    ap.add_argument('--seconds', type=float, default=60)
    args = ap.parse_args()
    result = lift(json.loads(args.relaxed_result.read_text()), args.seconds)
    args.out.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k:v for k, v in result.items() if k not in ('actual_lift', 'partial_lift')}))
