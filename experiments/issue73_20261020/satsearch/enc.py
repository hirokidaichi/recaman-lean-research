#!/usr/bin/env python3
"""CP-SAT encoding of finite closures (line model, arbitrary P2 windows) on clocks 0..N-1.

Usage: enc.py N LMAX MODE [--time T] [--workers W] [--maxS K] [--json out]
MODE:
  any      : any nonempty closure
  w7       : closure containing a member of lag 7
  long     : closure containing a member of lag >= 11   (classification violation)
  P        : Claim P counterexample (nonempty, every owned S covered >= 2 times)
  SC       : Conjecture SC violation (some member does not own the oldest clock of its window)
  defect1  : 'near miss': all M-conditions except exactly ONE covered S is unowned, and a member of lag >= 11 exists
  defect1x : like defect1 but also the unowned S is not the only obstacle trivially: requires lag>=11 member AND
             no private member structure check (same as defect1; kept for symmetry)
Symmetry breaking: some window starts at clock 0.
"""
import sys, json, time, argparse
from ortools.sat.python import cp_model

ap = argparse.ArgumentParser()
ap.add_argument('N', type=int)
ap.add_argument('LMAX', type=int)
ap.add_argument('MODE')
ap.add_argument('--time', type=float, default=600)
ap.add_argument('--workers', type=int, default=2)
ap.add_argument('--json', default=None)
ap.add_argument('--minlen', type=int, default=11, help='threshold for "long" member in long/defect modes')
ap.add_argument('--maxlen_at_least', type=int, default=0, help='require some member with lag >= this')
ap.add_argument('--relax', default='', help='le or ge: moment one-sided (for validation)')
ap.add_argument('--conn', action='store_true', help='union of windows is an interval starting at 0 (WLOG: one component)')
ap.add_argument('--cuts', action='store_true', help='add trivially-implied Hall counting cuts')
ap.add_argument('--enum', action='store_true')
ap.add_argument('--fsplit', action='store_true', help='add walk variables F for propagation')
a = ap.parse_args()
N, LMAX, MODE = a.N, a.LMAX, a.MODE
Ls = [L for L in range(3, LMAX + 1, 4)]

m = cp_model.CpModel()
x = [m.NewBoolVar(f'x{c}') for c in range(N)]  # True = A
y = {}  # (b,L)
for b in range(N):
    for L in Ls:
        if b - L >= 0:
            y[b, L] = m.NewBoolVar(f'y{b}_{L}')
mem = {}
for b in range(N):
    ys = [y[b, L] for L in Ls if (b, L) in y]
    if not ys:
        continue
    mem[b] = m.NewBoolVar(f'm{b}')
    m.Add(sum(ys) == mem[b])
    m.AddImplication(mem[b], x[b])

if a.fsplit:
    F = [m.NewIntVar(-N, N, f'F{c}') for c in range(N + 1)]
    m.Add(F[0] == 0)
    for c in range(N):
        m.Add(F[c + 1] == F[c] + 2 * x[c] - 1)

for (b, L), v in y.items():
    t = b - L
    # mass: #A = (L+1)/2
    m.Add(sum(x[c] for c in range(t, b)) == (L + 1) // 2).OnlyEnforceIf(v)
    # moment: sum sigma(c)(b-c) = 0  <=> sum x_c (b-c) = L(L+1)/4
    mexpr = sum((b - c) * x[c] for c in range(t, b))
    if a.relax == 'le':
        m.Add(mexpr <= L * (L + 1) // 4).OnlyEnforceIf(v)
    elif a.relax == 'ge':
        m.Add(mexpr >= L * (L + 1) // 4).OnlyEnforceIf(v)
    else:
        m.Add(mexpr == L * (L + 1) // 4).OnlyEnforceIf(v)
    if a.fsplit:
        m.Add(F[b] == F[t] + 1).OnlyEnforceIf(v)
        m.Add(sum(F[u] for u in range(t + 1, b + 1)) == L * F[t]).OnlyEnforceIf(v)

# ownership
o = {}
for b in mem:
    for c in range(max(0, b - LMAX), b):
        o[b, c] = m.NewBoolVar(f'o{b}_{c}')
        m.AddImplication(o[b, c], x[c].Not())
        cov_by_b = [y[b, L] for L in Ls if (b, L) in y and b - L <= c]
        if not cov_by_b:
            m.Add(o[b, c] == 0)
        else:
            m.AddBoolOr(cov_by_b).OnlyEnforceIf(o[b, c])
    m.Add(sum(o[b, c] for c in range(max(0, b - LMAX), b)) == mem[b])

owned = []
covers = [[] for _ in range(N)]
for (b, L), v in y.items():
    for c in range(b - L, b):
        covers[c].append(v)
for c in range(N):
    os_ = [o[b, c] for b in mem if (b, c) in o]
    ow = m.NewBoolVar(f'ow{c}')
    if os_:
        m.Add(sum(os_) == ow)
    else:
        m.Add(ow == 0)
    owned.append(ow)

unowned = []  # covered S not owned (only relevant for defect modes)
if MODE.startswith('defect'):
    for c in range(N):
        u = m.NewBoolVar(f'u{c}')
        # u <-> covered & S & not owned
        for v in covers[c]:
            m.AddBoolOr([v.Not(), x[c], ow := owned[c], u])
        m.AddImplication(u, x[c].Not())
        m.AddImplication(u, owned[c].Not())
        if covers[c]:
            m.AddBoolOr(covers[c]).OnlyEnforceIf(u)
        else:
            m.Add(u == 0)
        unowned.append(u)
    m.Add(sum(unowned) == 1)
else:
    for c in range(N):
        for v in covers[c]:
            m.AddBoolOr([v.Not(), x[c], owned[c]])  # M2

m.Add(sum(mem.values()) >= 1)
if a.cuts:
    cS = []
    for c in range(N):
        k = m.NewBoolVar(f'cS{c}')   # covered S  (== owned in closure modes)
        if covers[c]:
            m.AddBoolOr(covers[c]).OnlyEnforceIf(k)
            m.AddImplication(k, x[c].Not())
            for v in covers[c]:
                m.AddBoolOr([v.Not(), x[c], k])
        else:
            m.Add(k == 0)
        cS.append(k)
    memv = [mem.get(b, 0) for b in range(N)]
    slack = 1 if MODE.startswith('defect') else 0
    m.Add(sum(cS) == sum(mem.values()) + slack)
    for z in range(N):
        m.Add(sum(memv[:z + 1]) <= sum(cS[:z]))            # prefix Hall
        m.Add(sum(cS[z:]) <= sum(memv[z + 1:]) + slack)   # suffix Hall
if a.conn:
    cv = []
    for c in range(N):
        k = m.NewBoolVar(f'cv{c}')
        if covers[c]:
            m.AddBoolOr(covers[c]).OnlyEnforceIf(k)
            for v in covers[c]:
                m.AddImplication(v, k)
        else:
            m.Add(k == 0)
        cv.append(k)
    for c in range(1, N):
        m.AddImplication(cv[c], cv[c - 1])
# symmetry: a window starts at 0
m.AddBoolOr([y[L, L] for L in Ls if (L, L) in y])

def longvars(th):
    return [v for (b, L), v in y.items() if L >= th]

if MODE == 'any':
    pass
elif MODE == 'w7':
    m.AddBoolOr([v for (b, L), v in y.items() if L == 7])
elif MODE == 'long':
    m.AddBoolOr(longvars(a.minlen))
elif MODE == 'P':
    for c in range(N):
        if covers[c]:
            m.Add(sum(covers[c]) >= 2).OnlyEnforceIf(owned[c])
        else:
            m.Add(owned[c] == 0)
elif MODE == 'SC':
    zs = []
    for (b, L), v in y.items():
        z = m.NewBoolVar(f'z{b}_{L}')
        m.AddBoolAnd([v, o[b, b - L]]).OnlyEnforceIf(z)
        m.AddBoolOr([v.Not(), o[b, b - L].Not(), z])
        zs.append(z)
    m.Add(sum(zs) <= sum(mem.values()) - 1)
elif MODE == 'defect1':
    m.AddBoolOr(longvars(a.minlen))
elif MODE == 'defect1P':   # one covered S unowned, every covered S covered >= 2 times
    for c in range(N):
        if covers[c]:
            for v in covers[c]:
                m.Add(sum(covers[c]) >= 2).OnlyEnforceIf([v, x[c].Not()])
elif MODE == 'defect1SC':  # one covered S unowned, some member does not own its oldest clock
    zs = []
    for (b, L), v in y.items():
        z = m.NewBoolVar(f'z{b}_{L}')
        m.AddBoolAnd([v, o[b, b - L]]).OnlyEnforceIf(z)
        m.AddBoolOr([v.Not(), o[b, b - L].Not(), z])
        zs.append(z)
    m.Add(sum(zs) <= sum(mem.values()) - 1)
elif MODE == 'nonclass':
    bads = list(longvars(11))
    for b in range(N):
        if (b, 7) not in y:
            continue
        conds = [y[b, 7], o[b, b - 7]]
        word = 'SSAAAAS'
        for i, ch in enumerate(word):
            conds.append(x[b - 7 + i] if ch == 'A' else x[b - 7 + i].Not())
        ok = (b + 2, 3) in y and (b - 3, 3) in y
        if ok:
            conds += [y[b + 2, 3], y[b - 3, 3]]
        g = m.NewBoolVar(f'g{b}')
        if ok:
            m.AddBoolAnd(conds).OnlyEnforceIf(g)
            m.AddBoolOr([c_.Not() for c_ in conds] + [g])
        else:
            m.Add(g == 0)
        bad = m.NewBoolVar(f'bad{b}')
        m.AddBoolOr([y[b, 7].Not(), g, bad])   # y7 & !g -> bad
        m.AddImplication(bad, y[b, 7])
        m.AddImplication(bad, g.Not())
        bads.append(bad)
    m.AddBoolOr(bads)
else:
    raise SystemExit('bad mode')
if a.maxlen_at_least:
    m.AddBoolOr(longvars(a.maxlen_at_least))

s = cp_model.CpSolver()
if a.enum:
    class CB(cp_model.CpSolverSolutionCallback):
        def __init__(self):
            super().__init__(); self.seen = set()
        def on_solution_callback(self):
            sig = ''.join('A' if self.Value(x[c]) else 'S' for c in range(N))
            w = tuple(sorted((b, b - L) for (b, L), v in y.items() if self.Value(v)))
            self.seen.add((sig, w))
    s.parameters.enumerate_all_solutions = True
    s.parameters.num_workers = 1
    cb = CB()
    st = s.Solve(m, cb)
    print('enum status', s.StatusName(st), 'distinct (sigma,windows):', len(cb.seen))
    json.dump(sorted([[a_, list(map(list, w))] for a_, w in cb.seen]), open(a.json or 'enum.json', 'w'))
    sys.exit(0)
s.parameters.num_workers = a.workers
s.parameters.max_time_in_seconds = a.time
t0 = time.time()
st = s.Solve(m)
el = time.time() - t0
name = s.StatusName(st)
print(f'N={N} LMAX={LMAX} MODE={MODE} status={name} time={el:.1f}s', flush=True)
if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
    sig = ''.join('A' if s.Value(x[c]) else 'S' for c in range(N))
    mems = []
    for (b, L), v in sorted(y.items()):
        if s.Value(v):
            own = [c for c in range(max(0, b - LMAX), b) if s.Value(o[b, c])]
            mems.append({'b': b, 'L': L, 't': b - L, 'own': own[0] if own else None})
    unow = [c for c in range(len(unowned)) if s.Value(unowned[c])] if unowned else []
    print('sigma (clock 0..N-1, oldest->newest):', sig)
    for d in mems:
        print(f"  member b={d['b']} L={d['L']} window=[{d['t']},{d['b']-1}] word(old->new)={sig[d['t']:d['b']]} own={d['own']}")
    if unow:
        print('  unowned covered S:', unow)
    if a.json:
        json.dump({'N': N, 'LMAX': LMAX, 'MODE': MODE, 'sigma': sig, 'members': mems, 'unowned': unow}, open(a.json, 'w'))
