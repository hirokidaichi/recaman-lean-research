"""Independent old-prefix spectra relaxation; SAT is not an actual history."""
import argparse
import datetime
import hashlib
import json
from pathlib import Path
import resource
import time

from ortools.sat.python import cp_model
import ortools
from c1_constraints import base, direct, fixed, solver


def spectra(max_mass):
    values = [dict() for _ in range(max_mass+1)]
    values[0][0] = ''
    atoms = [(1, 1, 1, 'A'), (2, 4, 2, 'SAAA'), (4, 10, 9, 'SSAAAASAAA')]
    for mass in range(max_mass+1):
        for area, word in list(values[mass].items()):
            for dm, length, da, atom in atoms:
                if mass+dm <= max_mass:
                    new_area = area+length*mass+da
                    values[mass+dm].setdefault(new_area, word+atom)
    for mass, rows in enumerate(values):
        for area in rows:
            assert mass*(mass+1) <= 2*area+2
    return values


def relaxed_model(n, max_mass):
    m, z = base(n, free_tags=True)
    spec = spectra(max_mass)
    pairs = [(mass, area) for mass in range(1, max_mass+1) for area in spec[mass]]
    olds = []
    x, e, f, g = (z[key] for key in ('x', 'e', 'f', 'g'))
    for b in range(n):
        old = m.new_bool_var(f'old_{b}')
        olds.append(old)
        m.add(old <= x[b])
        r = m.new_int_var(-n, n+1, f'old_mass_{b}')
        area = m.new_int_var(-n*n, n*n, f'old_area_{b}')
        m.add(r == 1-f[b])
        m.add(area == -g[b]+b*(f[b]-1))
        m.add_allowed_assignments([r, area], pairs).only_enforce_if(old)
        wins = [old]
        for t in range(b-3, -1, -4):
            length = b-t
            mass_eq = m.new_bool_var(f'local_mass_{t}_{b}')
            moment_eq = m.new_bool_var(f'local_moment_{t}_{b}')
            w = m.new_bool_var(f'local_P2_{t}_{b}')
            mass_expr = sum(x[t:b])
            moment_expr = sum((b-i)*x[i] for i in range(t, b))
            m.add(mass_expr == (length+1)//2).only_enforce_if(mass_eq)
            m.add(mass_expr != (length+1)//2).only_enforce_if(mass_eq.Not())
            m.add(moment_expr == length*(length+1)//4).only_enforce_if(moment_eq)
            m.add(moment_expr != length*(length+1)//4).only_enforce_if(moment_eq.Not())
            m.add_bool_and([mass_eq, moment_eq]).only_enforce_if(w)
            m.add_bool_or([mass_eq.Not(), moment_eq.Not()]).only_enforce_if(w.Not())
            wins.append(w)
        m.add_bool_or(wins).only_enforce_if(e[b])
        for w in wins:
            m.add_bool_or([x[b].Not(), w.Not(), e[b]])
    return m, z, olds, spec


def calibrate(out):
    cases = [('SAAA', 'SSSSAAAASAAA'), ('SSAAAASAAA', 'S'*8+'A'*6)]
    for prefix, tail in cases:
        m, z, old, _ = relaxed_model(len(tail), len(tail)+1)
        fixed(m, z, tail)
        actual = direct(prefix+tail)
        for i, v in enumerate(z['e']):
            m.add(v == actual['endable'][len(prefix)+i])
        ss = solver(30)
        assert ss.solve(m) == cp_model.OPTIMAL
    tail = 'S'*4+'A'*5+'SS'
    m, z, old, _ = relaxed_model(len(tail), len(tail)+1)
    fixed(m, z, tail)
    m.add(old[8] == 1)  # mass=1, required old area=8: no such block suffix.
    ss = solver(30)
    assert ss.solve(m) == cp_model.INFEASIBLE
    result = dict(status='passed', real_prefix_embedding_cases=cases,
                  phantom_mass_one_area_eight='INFEASIBLE',
                  source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    out.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result))


def run(args):
    n = args.n
    max_mass = (n+1)//2+1
    m, z, old, spec = relaxed_model(n, max_mass)
    f, g, d, an = (z[key] for key in ('f', 'g', 'd', 'an'))
    for u in range(1, n+1):
        m.add(d[u] >= 1)
    m.add(d[n] == 1)
    m.add(an[n] <= 3)
    m.add(sum(1-v for v in z['x']) <= (n+1)//2)
    low = m.new_int_var(-n, n, 'minimum')
    m.add_min_equality(low, f)
    m.add(low <= -5)
    assert not m.validate(), m.validate()
    model_path = args.out.with_suffix('.model.pbtxt')
    m.export_to_file(str(model_path))
    spec_path = args.out.with_suffix('.spectrum.json')
    spec_path.write_text(json.dumps([{'mass':i, 'area_witnesses':rows} for i, rows in enumerate(spec)], indent=2)+'\n')
    ss = solver(args.seconds)
    ss.parameters.log_search_progress = True
    ss.parameters.log_to_stdout = False
    log = args.out.with_suffix('.solver.log').open('w')
    def log_line(line):
        log.write(line+'\n')
        log.flush()
    ss.log_callback = log_line
    started = time.monotonic()
    start_iso = datetime.datetime.now(datetime.timezone.utc).isoformat()
    print(json.dumps(dict(event='solve_started', utc=start_iso, n=n, max_mass=max_mass, seconds=args.seconds)), flush=True)
    status = ss.solve(m)
    result = dict(status=ss.status_name(status), n=n, max_old_mass=max_mass,
                  population='independent old-prefix spectra relaxation', actual_history_counterexample=False,
                  started_utc=start_iso, finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                  elapsed_seconds=time.monotonic()-started, workers=1, seed=20261022,
                  ortools=ortools.__version__, source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  model_sha256=hashlib.sha256(model_path.read_bytes()).hexdigest(), response_stats=ss.response_stats())
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        tail = ''.join('A' if ss.value(v) else 'S' for v in z['x'])
        actual_local = direct(tail)
        flags = [ss.value(v) for v in old]
        endable = [int(c == 'A' and (actual_local['endable'][i] or flags[i])) for i, c in enumerate(tail)]
        assert endable == [ss.value(v) for v in z['e']]
        deficit, new_as = [0], [0]
        old_rows = []
        for b, (c, e, flag) in enumerate(zip(tail, endable, flags)):
            deficit.append(deficit[-1]+(c == 'S')-e)
            new_as.append(new_as[-1]+(c == 'A' and not e))
            if flag:
                r = 1-actual_local['F'][b]
                area = -sum(v-actual_local['F'][b]+1 for v in actual_local['F'][1:b+1])
                assert area in spec[r]
                witness = spec[r][area]
                check = direct(witness)
                assert check['F'][-1] == r and sum(check['F'][1:]) == area
                old_rows.append(dict(b=b, mass=r, required_area=area, individual_prefix_witness=witness))
        assert deficit == [ss.value(v) for v in d] and new_as == [ss.value(v) for v in an]
        assert deficit[-1] == 1 and min(deficit[1:]) >= 1 and new_as[-1] <= 3 and min(actual_local['F']) <= -5
        result['relaxed_witness'] = dict(tail=tail, F=actual_local['F'], d=deficit, an=new_as,
                                         endable=endable, old_flags=old_rows, common_prefix='not checked')
    usage = resource.getrusage(resource.RUSAGE_SELF)
    result.update(user_seconds=usage.ru_utime, system_seconds=usage.ru_stime, maxrss_native=usage.ru_maxrss)
    args.out.write_text(json.dumps(result, indent=2)+'\n')
    log.close()
    print(json.dumps({k:result[k] for k in ('status', 'elapsed_seconds', 'actual_history_counterexample')}))


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--mode', choices=['calibrate', 'run'], required=True)
    ap.add_argument('--n', type=int, default=32)
    ap.add_argument('--seconds', type=float, default=240)
    ap.add_argument('--out', type=Path, required=True)
    args = ap.parse_args()
    if args.mode == 'calibrate':
        calibrate(args.out)
    else:
        resource.setrlimit(resource.RLIMIT_CPU, (270, 272))
        run(args)
