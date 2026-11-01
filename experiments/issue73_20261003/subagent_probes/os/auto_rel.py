#!/usr/bin/env python3
"""Left-to-right automaton for closed configurations with ARBITRARY P2 windows (line model).

State before processing clock z: sorted tuple of open windows (age, d, psi, owned)
  age   = z - t_b
  d     = F(z) - h_b
  psi   = sum_{tau in (t_b, z]} (F(tau) - h_b)
  owned = 1 if own(b) < z already chosen
A window may close at z (member b = z) iff d==1, psi==0, owned, age>=3; then sigma(z)=A.
Transition at clock z: optional close of one window; start k>=0 new windows; pick sigma(z);
if S, assign an unowned open window as owner (M2 + M1'); update.
Component ends when the state is empty after a close (and no new start).
Bounds: age <= LMAX, #open <= KMAX.
Also tracks phase: before first S (pre) / after.
"""
import sys
from functools import lru_cache
from collections import defaultdict, deque

LMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 11
KMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 4
import os
REL=os.environ.get('REL','eq')
CLOSEOK={'eq':lambda p:p==0,'le':lambda p:p<=0,'ge':lambda p:p>=0}[REL]
MINIMAL=False

@lru_cache(None)
def addrange(d, r):
    """(min,max) of sum of positions after each of r steps (+-1) starting at d and ending at 1; None if impossible"""
    if r == 0:
        return (0, 0) if d == 1 else None
    if abs(d - 1) > r or (r - abs(d - 1)) % 2:
        return None
    lo, hi = None, None
    for s in (1, -1):
        sub = addrange(d + s, r - 1)
        if sub is None:
            continue
        a, b = sub[0] + d + s, sub[1] + d + s
        lo = a if lo is None else min(lo, a)
        hi = b if hi is None else max(hi, b)
    return (lo, hi)

def viable(w):
    age, d, psi, owned = w
    r_max = LMAX - age
    for r in range(0, r_max + 1):
        if age + r < 3:
            continue
        rg = addrange(d, r)
        if rg is None:
            continue
        if (REL=='eq' and psi + rg[0] <= 0 <= psi + rg[1]) or (REL=='le' and psi+rg[0]<=0) or (REL=='ge' and psi+rg[1]>=0):
            return True
    return False

def step(state, pre):
    """yield (newstate, newpre, info) for processing one clock. state nonempty or start."""
    ws = list(state)
    results = []
    # close options
    close_opts = [None]
    for i, w in enumerate(ws):
        if w[1] == 1 and CLOSEOK(w[2]) and w[3] == 1 and w[0] >= 3:
            if i > 0 and ws[i - 1] == w:
                continue
            close_opts.append(i)
    if MINIMAL:
        # in the minimal model a window MUST close at its first P2 point: we do not track 'first' exactly here
        pass
    for c in close_opts:
        base = [w for j, w in enumerate(ws) if j != c]
        for k in range(0, KMAX - len(base) + 1):
            cur = base + [(0, 0, 0, 0)] * k
            if not cur:
                if c is not None:
                    results.append(((), pre, 'end'))
                continue
            sigmas = ['A'] if c is not None else ['A', 'S']
            for sg in sigmas:
                if sg == 'A':
                    opts = [tuple(cur)]
                    s = 1
                else:
                    s = -1
                    opts = []
                    seen = set()
                    for i, w in enumerate(cur):
                        if w[3] == 0 and w not in seen:
                            seen.add(w)
                            nw = list(cur)
                            nw[i] = (w[0], w[1], w[2], 1)
                            opts.append(tuple(nw))
                    if not opts:
                        continue
                for o in opts:
                    nxt = []
                    ok = True
                    for (age, d, psi, owned) in o:
                        nd = d + s
                        nw = (age + 1, nd, psi + nd, owned)
                        if nw[0] > LMAX or not viable(nw):
                            ok = False
                            break
                        nxt.append(nw)
                    if not ok:
                        continue
                    npre = pre and sg == 'A'
                    results.append((tuple(sorted(nxt)), npre, (c is not None, k, sg)))
    return results

def E(state):
    return sum(1 for w in state if w[3] == 0)

def main():
    # initial: the first clock x starts >=1 windows; state "START" = ((), True) handled as step from empty w/ k>=1
    start = ((), True)
    graph = defaultdict(list)
    seen = {start}
    dq = deque([start])
    while dq:
        st = dq.popleft()
        state, pre = st
        for (ns, npre, info) in step(state, pre):
            if info == 'end':
                key = ('END',)
            else:
                key = (ns, npre)
                # an S at the first S clock: record E after it
            graph[st].append((key, info))
            if key != ('END',) and key not in seen:
                seen.add(key)
                dq.append(key)
    # co-reachability
    rev = defaultdict(list)
    for a, lst in graph.items():
        for b, info in lst:
            rev[b].append((a, info))
    good = {('END',)}
    dq = deque([('END',)])
    while dq:
        b = dq.popleft()
        for a, info in rev[b]:
            if a not in good:
                good.add(a)
                dq.append(a)
    print('LMAX', LMAX, 'KMAX', KMAX, 'states', len(seen), 'coreachable', len(good))
    # E>=1 coreachable states (excluding start)
    bad = [s for s in good if s != ('END',) and s != start and E(s[0]) >= 1]
    print('coreachable states with E>=1:', len(bad))
    # OS failures: transitions from pre=True to pre=False (the first S) landing in a coreachable state with E>=1
    osf = []
    for a, lst in graph.items():
        if a == ('END',) or not a[1]:
            continue
        for b, info in lst:
            if b != ('END',) and not b[1] and b in good and E(b[0]) >= 1:
                osf.append((a, b, info))
    print('OS failures (coreachable post-s0 states with E>=1):', len(osf))
    for x in osf[:10]:
        print('  ', x)
    return graph, good, seen

if __name__ == '__main__':
    main()
