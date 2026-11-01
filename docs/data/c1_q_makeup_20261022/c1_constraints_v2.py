"""Exact finite C1 constraint probes. SAT results are checked by direct sums.

This is discovery, not a proof for unbounded words or completed setting D.
"""
import argparse
import datetime
import hashlib
import json
from pathlib import Path
import resource
import time

import ortools
from ortools.sat.python import cp_model


def direct(word):
    signs = [1 if c == 'A' else -1 for c in word]
    f = [0]
    for v in signs:
        f.append(f[-1]+v)
    ends, starts, d, an = [], [], [0], [0]
    for b, v in enumerate(signs):
        ts = [t for t in range(b) if sum(signs[t:b]) == 1
              and sum(signs[i]*(b-i) for i in range(t, b)) == 0]
        e = bool(ts) and v == 1
        starts.append(ts)
        ends.append(int(e))
        d.append(d[-1]+(v < 0)-e)
        an.append(an[-1]+(v == 1 and not e))
    return dict(F=f, endable=ends, starts=starts, d=d, an=an)


def base(n, free_tags=False):
    m = cp_model.CpModel()
    x = [m.new_bool_var(f'A_{i}') for i in range(n)]
    e = [m.new_bool_var(f'E_{i}') for i in range(n)]
    f = [m.new_int_var(-n, n, f'F_{i}') for i in range(n+1)]
    g = [m.new_int_var(-n*(n+1)//2, n*(n+1)//2, f'G_{i}') for i in range(n+1)]
    d = [m.new_int_var(-n, n, f'd_{i}') for i in range(n+1)]
    an = [m.new_int_var(0, n, f'an_{i}') for i in range(n+1)]
    for vs in (f, g, d, an):
        m.add(vs[0] == 0)
    for b in range(n):
        m.add(f[b+1] == f[b]+2*x[b]-1)
        m.add(g[b+1] == g[b]+f[b+1])
        m.add(d[b+1] == d[b]+1-x[b]-e[b])
        m.add(an[b+1] == an[b]+x[b]-e[b])
        m.add(e[b] <= x[b])
        if free_tags:
            continue
        wins = []
        # All possible lengths: necessity of L = 3 mod 4 is already proved.
        for t in range(b-3, -1, -4):
            mass = m.new_bool_var(f'mass_{t}_{b}')
            moment = m.new_bool_var(f'moment_{t}_{b}')
            w = m.new_bool_var(f'P2_{t}_{b}')
            m.add(f[b] == f[t]+1).only_enforce_if(mass)
            m.add(f[b] != f[t]+1).only_enforce_if(mass.Not())
            m.add(g[b]-g[t] == (b-t)*f[t]).only_enforce_if(moment)
            m.add(g[b]-g[t] != (b-t)*f[t]).only_enforce_if(moment.Not())
            m.add_bool_and([mass, moment]).only_enforce_if(w)
            m.add_bool_or([mass.Not(), moment.Not()]).only_enforce_if(w.Not())
            m.add_bool_or([x[b].Not(), w.Not(), e[b]])
            wins.append(w)
        if wins:
            m.add_bool_or(wins).only_enforce_if(e[b])
        else:
            m.add(e[b] == 0)
    return m, dict(x=x, e=e, f=f, g=g, d=d, an=an)


def fixed(m, z, word):
    for x, c in zip(z['x'], word):
        m.add(x == (c == 'A'))


def solver(seconds=30):
    s = cp_model.CpSolver()
    s.parameters.num_search_workers = 1
    s.parameters.random_seed = 20261022
    s.parameters.max_time_in_seconds = seconds
    s.parameters.max_memory_in_mb = 768
    return s


def checked_values(s, z):
    word = ''.join('A' if s.value(x) else 'S' for x in z['x'])
    r = direct(word)
    assert r['F'] == [s.value(v) for v in z['f']]
    assert r['d'] == [s.value(v) for v in z['d']]
    assert r['an'] == [s.value(v) for v in z['an']]
    assert r['endable'] == [s.value(v) for v in z['e']]
    return dict(word=word, **r)


def calibrate(out):
    m, z = base(8)
    s = solver(30)
    class CheckAll(cp_model.CpSolverSolutionCallback):
        def __init__(self):
            super().__init__()
            self.words = set()
        def on_solution_callback(self):
            v = checked_values(self, z)
            assert v['word'] not in self.words
            self.words.add(v['word'])
    cb = CheckAll()
    s.parameters.enumerate_all_solutions = True
    status = s.solve(m, cb)
    assert status == cp_model.OPTIMAL and len(cb.words) == 256
    fixtures = ['SAAA', 'SSAAAASAAA', 'SAAASSSSAAAASAAA', 'SSSAAAS']
    for word in fixtures:
        m, z = base(len(word))
        fixed(m, z, word)
        ss = solver()
        assert ss.solve(m) == cp_model.OPTIMAL
        checked_values(ss, z)
    # A true P2 clock cannot be silently omitted from Endable.
    m, z = base(4)
    fixed(m, z, 'SAAA')
    m.add(z['e'][3] == 0)
    ss = solver()
    assert ss.solve(m) == cp_model.INFEASIBLE
    # One phantom Endable makes the low-area/free-tag word look like d=1.
    word = 'SAAA'+'S'*4+'A'*5+'SS'
    tags = {3, 10, 11, 12}
    tag_status = {}
    for free in (True, False):
        m, z = base(len(word), free_tags=free)
        fixed(m, z, word)
        for i, v in enumerate(z['e']):
            m.add(v == (i in tags))
        m.add(z['d'][13] == 1)
        ss = solver()
        st = ss.solve(m)
        tag_status[str(free)] = ss.status_name(st)
        assert st == (cp_model.OPTIMAL if free else cp_model.INFEASIBLE)
    result = dict(status='passed', n8_words=256, fixtures=fixtures,
                  forced_omission='INFEASIBLE', phantom_tags=tag_status,
                  ortools=ortools.__version__, source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    out.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result))


def research(args):
    n, q, b, k = args.n, args.q0, args.b, 4
    assert n >= 8 and k < q <= n
    m, z = base(n)
    fixed(m, z, 'SAAA')
    f, g, d, an = (z[key] for key in ('f', 'g', 'd', 'an'))
    m.add(d[k] == 0)
    for u in range(1, k+1):
        m.add(d[u] >= 0)
    m.add(d[q] == 1)
    end = b+1 if args.mode in ('Q-old-min', 'Y-triangle') else q
    assert end <= n
    for u in range(k+1, end+1):
        m.add(d[u] >= 1)
    if args.mode in ('Q-old-min', 'Y-triangle'):
        assert q <= b < n
        m.add(an[b+1]-an[q] <= 1)
        m.add(f[b] <= f[k])
        old = m.new_int_var(-n, n, 'old_minimum')
        young = m.new_int_var(-n, n, 'young_minimum')
        m.add_min_equality(old, f[k:q])
        m.add_min_equality(young, f[q:b+1])
        m.add(young >= old+1)
        area = m.new_int_var(-n*n, n*n, 'Z')
        # f[b] is a variable; multiplication here is by a fixed length.
        m.add(area == g[b]-g[k]-(b-k)*(f[b]-1))
        if args.mode == 'Q-old-min':
            m.add(area <= -1)
        else:
            drop = m.new_int_var(0, n, 'drop')
            m.add(drop == f[q]-f[b])
            dp = m.new_int_var(1, n+1, 'drop_plus_one')
            m.add(dp == drop+1)
            triangular_twice = m.new_int_var(0, n*(n+1), 'twice_triangle')
            m.add_multiplication_equality(triangular_twice, [drop, dp])
            y = g[b]-g[q]-(b-q)*(f[b]-1)
            m.add(2*y-triangular_twice <= -1)
    elif args.mode == 'deep-three':
        m.add(an[q]-an[k] <= 3)
        low = m.new_int_var(-n, n, 'lowest_level')
        m.add_min_equality(low, f[k:q+1])
        m.add(low <= f[k]-5)
    elif args.mode == 'R-negative':
        h = m.new_int_var(1, n, 'h')
        m.add(h == f[q]-f[k])
        hp = m.new_int_var(2, n+1, 'h_plus_one')
        m.add(hp == h+1)
        square = m.new_int_var(0, n*(n+1), 'h_times_h_plus_one')
        m.add_multiplication_equality(square, [h, hp])
        az = g[q]-g[k]-(q-k)*(f[k]-1)
        m.add(2*az+square <= -1)
    elif args.mode == 'peak-five':
        peak = m.new_int_var(0, n, 'peak')
        m.add_max_equality(peak, d[k+1:q+1])
        m.add(peak >= 5)
    else:
        raise ValueError(args.mode)
    invalid = m.validate()
    assert not invalid, invalid
    model_path = args.out.with_suffix('.model.pbtxt')
    m.export_to_file(str(model_path))
    s = solver(args.seconds)
    s.parameters.log_search_progress = True
    s.parameters.log_to_stdout = False
    log = args.out.with_suffix('.solver.log').open('w')
    def log_line(line):
        log.write(line+'\n')
        log.flush()
    s.log_callback = log_line
    start = time.monotonic()
    started = datetime.datetime.now(datetime.timezone.utc).isoformat()
    print(json.dumps(dict(event='solve_started', mode=args.mode, n=n, q0=q, b=b,
                          utc=started, max_seconds=args.seconds)), flush=True)
    status = s.solve(m)
    result = dict(mode=args.mode, n=n, k1=k, q0=q, b=b, status=s.status_name(status),
                  started_utc=started, finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                  solve_elapsed_seconds=time.monotonic()-start, ortools=ortools.__version__,
                  seed=20261022, workers=1, memory_parameter_mib=768,
                  source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  model_sha256=hashlib.sha256(model_path.read_bytes()).hexdigest(),
                  response_stats=s.response_stats(), no_completed_D_or_IH_check=True)
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        w = checked_values(s, z)
        ff, dd, aa = (w[key] for key in ('F', 'd', 'an'))
        assert dd[k] == 0 and dd[q] == 1 and min(dd[k+1:end+1]) >= 1
        if args.mode in ('Q-old-min', 'Y-triangle'):
            zz = sum(ff[u]-ff[b]+1 for u in range(k+1, b+1))
            assert aa[b+1]-aa[q] <= 1 and ff[b] <= ff[k]
            assert min(ff[k:q]) < min(ff[q:b+1])
            w['Z'] = zz
            if args.mode == 'Q-old-min':
                assert zz < 0
            else:
                drop = ff[q]-ff[b]
                y = sum(ff[u]-ff[b]+1 for u in range(q+1, b+1))
                assert drop >= 0 and 2*y < drop*(drop+1)
                w.update(Y=y, drop=drop, twice_margin=2*y-drop*(drop+1))
        elif args.mode == 'deep-three':
            assert aa[q]-aa[k] <= 3 and min(ff[k:q+1]) <= ff[k]-5
            w.update(a_z=aa[q]-aa[k], depth=ff[k]-min(ff[k:q+1]))
        elif args.mode == 'R-negative':
            h = ff[q]-ff[k]
            az = sum(ff[u]-ff[k]+1 for u in range(k+1, q+1))
            assert h >= 1 and 2*az+h*(h+1) < 0
            w.update(Az=az, h=h, twice_R=2*az+h*(h+1))
        else:
            assert max(dd[k+1:q+1]) >= 5
            w['peak'] = max(dd[k+1:q+1])
        result['witness'] = w
    usage = resource.getrusage(resource.RUSAGE_SELF)
    result.update(process_user_seconds=usage.ru_utime, process_system_seconds=usage.ru_stime,
                  maximum_resident_size_native=usage.ru_maxrss)
    args.out.write_text(json.dumps(result, indent=2)+'\n')
    log.close()
    print(json.dumps({k:result[k] for k in ('mode', 'status', 'solve_elapsed_seconds')}), flush=True)


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--mode', required=True, choices=['calibrate', 'Q-old-min', 'R-negative', 'peak-five', 'deep-three', 'Y-triangle'])
    ap.add_argument('--n', type=int, default=65)
    ap.add_argument('--q0', type=int, default=32)
    ap.add_argument('--b', type=int, default=64)
    ap.add_argument('--seconds', type=float, default=900)
    ap.add_argument('--out', type=Path, required=True)
    args = ap.parse_args()
    if args.mode == 'calibrate':
        calibrate(args.out)
    else:
        resource.setrlimit(resource.RLIMIT_CPU, (int(args.seconds)+10, int(args.seconds)+12))
        research(args)
