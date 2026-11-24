"""Frozen exact finite controls for H02; no finite computation proves the all-height claim."""
import json, sys, time
from fractions import Fraction as Q

started = time.process_time()
mode = sys.argv[1]
assert mode in {'discovery', 'holdout'}

def profile(H):
    g = [1, 1]
    for h in range(2, H + 1):
        g.append(sum((2 * (h-t) - 3) * g[t] for t in range(h-1)))
    return g[:H+1]

def word_and_marks(H, g):
    assert H >= 1
    w = list('S' * (H+2))
    marks = []
    for h in range(H+1):
        for _ in range(g[h]-1):
            marks.append((len(w), h, h >= 2))
            w.extend('AS')
        marks.append((len(w), h, h >= 2))
        w.append('A')
    w.extend('S' * (H+1))
    marks.extend([(len(w), 0, False), (len(w)+1, 1, False)])
    w.extend('AA')
    return ''.join(w), dict((q, (h, supplied)) for q, h, supplied in marks)

Hs = list(range(1, 9)) if mode == 'discovery' else [9, 10]
qs = [Q(1,3), Q(2,5), Q(9,20), Q(1,2)] if mode == 'discovery' else [Q(1,4), Q(3,7), Q(5,11)]
g = profile(60)
assert g[:7] == [1,1,1,4,9,19,42]
assert all(g[h] == 2*g[h-1] + g[h-3] for h in range(4,61))
rho_polynomial = lambda z: z**3 - 2*z**2 - 1
assert rho_polynomial(Q(11,5)) < 0 < rho_polynomial(Q(221,100))
cone = []
for q in qs:
    kap = q*q*(1+q)/(1-q)**2
    values = []
    for H in [2, 5, 12, 30, 60]:
        s = sum(q**h*g[h] for h in range(H+1))
        ratio = s/(1+q)
        if kap < 1:
            assert ratio <= 1/(1-kap)
        values.append({'H':H, 'weighted_A_over_F':str(ratio)})
    cone.append({'q':str(q), 'kappa':str(kap), 'finite_values':values,
                 'subcritical':kap < 1, 'proposed_uniform_C':str(1/(1-kap)) if kap < 1 else None})

walks = []
prefix_checks = 0
for H in Hs:
    w, marks = word_and_marks(H, g)
    A = [0]*(H+1); E = [0]*(H+1); F = [0]*(H+1)
    height = 0; S = 0; up = [0]*(H+1); down = [0]*(H+1)
    for q, ch in enumerate(w):
        if ch == 'A':
            h, supplied = marks[q]
            assert height+(H+2) == h
            A[h] += 1; E[h] += supplied; F[h] += not supplied
            up[h] += 1
            height += 1
        else:
            h = height+(H+2)-1
            if H+2 <= q < len(w)-2 and 0 <= h <= H:
                down[h] += 1
            S += 1; height -= 1
        assert height <= -1 and S-sum(E) >= 1
        for h in range(H+1):
            assert E[h] <= sum((2*(h-t)-3)*A[t] for t in range(h-1))
            prefix_checks += 1
    assert A == [2,2]+g[2:H+1] and F == [2,2]+[0]*(H-1)
    assert E == [0,0]+g[2:H+1] and height == -H
    assert up == [2,2]+g[2:H+1] and down == g[:H+1]
    walks.append({'H':H, 'word_length':len(w), 'A':A, 'declared_E':E, 'declared_F':F,
                  'up':up, 'core_down':down, 'max_height':-1,
                  'final_height':height, 'initial_head':H+2,
                  'actual_EndN_checked':False})

# Literal ALL-source EndN only on small predeclared words. The declaration is not the source predicate.
literal = []
for H in ([1,2,3,4] if mode == 'discovery' else [5]):
    w, marks = word_and_marks(H, g)
    heights = [0]; prefix_sum = [0]; mismatch = []; actual_E = actual_F = 0
    for q, ch in enumerate(w):
        if ch == 'A':
            # Forward relative sum of heights at states u+1,...,q; includes ALL u<q.
            sources = [u for u in range(q) if heights[q] == heights[u]+1
                       and prefix_sum[q]-prefix_sum[u] == (q-u)*heights[u]]
            declared = marks[q][1]
            actual_E += bool(sources); actual_F += not sources
            if declared != bool(sources):
                mismatch.append({'q':q, 'stage_h':marks[q][0], 'declared_supplied':declared,
                                 'actual_sources':sources})
        heights.append(heights[-1]+(1 if ch == 'A' else -1))
        prefix_sum.append(prefix_sum[-1]+heights[-1])
    if H >= 3:
        assert any(m['declared_supplied'] and not m['actual_sources'] for m in mismatch)
    literal.append({'H':H, 'word':w, 'actual_E':actual_E, 'actual_F':actual_F,
                    'declared_E':sum(s for h,s in marks.values()),
                    'declared_F':sum(not s for h,s in marks.values()), 'mismatches':mismatch})
assert time.process_time()-started < .6
print(json.dumps({'mode':mode, 'all_pass':True, 'recurrence_checked_through':60,
                  'g60':g[60], 'cone':cone, 'walks':walks, 'prefix_inequality_checks':prefix_checks,
                  'literal_EndN_controls':literal,
                  'scope':'COMPUTED finite controls, not actual/canonical construction or all-height proof',
                  'internal_cpu_seconds':time.process_time()-started}))
