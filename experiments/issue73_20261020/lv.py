#!/usr/bin/env python3
"""CP-SAT search for (relaxed) finite closures, line model, clocks 0..N-1, windows of length L=3 mod 4 (or any odd with --anylen).
Options:
  --moment eq|ge|le   : moment condition sum_{u in (t,b]} (F(u)-h) =0 / >=0 / <=0
  --P                 : require every covered S to be covered >= 2 times (Claim P failure)
  --nohall            : drop ownership; only require #members == #covered S
  --extra NAME        : extra constraints for lemma testing (see code)
"""
import sys, json, argparse
from ortools.sat.python import cp_model
ap = argparse.ArgumentParser()
ap.add_argument('N', type=int); ap.add_argument('LMAX', type=int)
ap.add_argument('--moment', default='eq'); ap.add_argument('--P', action='store_true')
ap.add_argument('--nohall', action='store_true'); ap.add_argument('--anylen', action='store_true')
ap.add_argument('--extra', default=''); ap.add_argument('--time', type=float, default=300)
ap.add_argument('--workers', type=int, default=2); ap.add_argument('--minlong', type=int, default=0); ap.add_argument('--excess', type=int, default=0)
a = ap.parse_args()
N, LMAX = a.N, a.LMAX
Ls = list(range(3, LMAX+1, 2 if a.anylen else 4))
m = cp_model.CpModel()
x = [m.NewBoolVar(f'x{c}') for c in range(N)]
F = [m.NewIntVar(-N, N, f'F{c}') for c in range(N+1)]
m.Add(F[0] == 0)
for c in range(N): m.Add(F[c+1] == F[c] + 2*x[c] - 1)
y = {}
for b in range(N):
    for L in Ls:
        if b-L >= 0: y[b, L] = m.NewBoolVar('')
mem = {}
for b in range(N):
    ys = [y[b, L] for L in Ls if (b, L) in y]
    if ys:
        mem[b] = m.NewBoolVar(''); m.Add(sum(ys) == mem[b]); m.AddImplication(mem[b], x[b])
for (b, L), v in y.items():
    t = b-L
    m.Add(F[b] == F[t]+1).OnlyEnforceIf(v)
    area = sum(F[u] for u in range(t+1, b+1)) - L*F[t]
    if a.moment == 'eq': m.Add(area == 0).OnlyEnforceIf(v)
    elif a.moment == 'ge': m.Add(area >= 0).OnlyEnforceIf(v)
    elif a.moment == 'le': m.Add(area <= 0).OnlyEnforceIf(v)
covers = [[] for _ in range(N)]
for (b, L), v in y.items():
    for c in range(b-L, b): covers[c].append(v)
cov = [m.NewBoolVar('') for c in range(N)]  # covered
for c in range(N):
    if covers[c]:
        for v in covers[c]: m.AddImplication(v, cov[c])
        m.AddBoolOr(covers[c]).OnlyEnforceIf(cov[c])
    else: m.Add(cov[c] == 0)
covS = [m.NewBoolVar('') for c in range(N)]
for c in range(N):
    m.AddBoolAnd([cov[c], x[c].Not()]).OnlyEnforceIf(covS[c]); m.AddBoolOr([cov[c].Not(), x[c], covS[c]])
o = {}
if not a.nohall:
    for b in mem:
        for c in range(max(0, b-LMAX), b):
            o[b, c] = m.NewBoolVar('')
            m.AddImplication(o[b, c], x[c].Not())
            cb = [y[b, L] for L in Ls if (b, L) in y and b-L <= c]
            if cb: m.AddBoolOr(cb).OnlyEnforceIf(o[b, c])
            else: m.Add(o[b, c] == 0)
        m.Add(sum(o[b, c] for c in range(max(0, b-LMAX), b)) == mem[b])
    for c in range(N):
        os_ = [o[b, c] for b in mem if (b, c) in o]
        m.Add(sum(os_) == covS[c]) if os_ else m.Add(covS[c] == 0)
else:
    (m.Add(sum(mem.values()) >= sum(covS)+a.excess) if a.excess else m.Add(sum(mem.values()) == sum(covS)))
m.Add(sum(mem.values()) >= 1)
m.AddBoolOr([y[L, L] for L in Ls if (L, L) in y])
if a.P:
    for c in range(N):
        if covers[c]: m.Add(sum(covers[c]) >= 2).OnlyEnforceIf(covS[c])
if a.minlong:
    m.AddBoolOr([v for (b, L), v in y.items() if L >= a.minlong])
# ---- extra lemma tests ----
exec(open(__file__.replace('lv.py', 'extra.py')).read()) if a.extra else None
s = cp_model.CpSolver(); s.parameters.num_workers = a.workers; s.parameters.max_time_in_seconds = a.time
st = s.Solve(m)
print(f'N={N} LMAX={LMAX} moment={a.moment} P={a.P} nohall={a.nohall} extra={a.extra} status={s.StatusName(st)} t={s.WallTime():.1f}')
if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
    sig = ''.join('A' if s.Value(x[c]) else 'S' for c in range(N))
    print('sigma:', sig); print('F:', [s.Value(F[c]) for c in range(N+1)])
    for (b, L), v in sorted(y.items()):
        if s.Value(v):
            ow = [c for c in range(max(0, b-LMAX), b) if (b, c) in o and s.Value(o[b, c])]
            area = sum(s.Value(F[u]) for u in range(b-L+1, b+1)) - L*s.Value(F[b-L])
            print(f'  b={b} L={L} W=[{b-L},{b-1}] word={sig[b-L:b]} h={s.Value(F[b-L])} own={ow} area={area}')
    print('  cov:', {c: sum(s.Value(v) for v in covers[c]) for c in range(N) if s.Value(covS[c])})
