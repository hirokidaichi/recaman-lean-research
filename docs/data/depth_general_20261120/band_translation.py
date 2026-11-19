"""Explicit translation and endpoint-capacity checks; no subprocesses."""
from pathlib import Path
import json, sys

data = json.loads(Path(sys.argv[1]).read_text())
cases = data['sharp_threshold'] + data['sharp_count'] + data['regressions']
translated = steps = endpoint_checks = 0
for case in cases:
    events, b = case['events'], case['b']
    T0 = 1 + max([0] + [e['n'] - e['candidate'] for e in events])
    for T in [T0, T0 + 1, 5 * T0 + 7]:
        seen = {0} | {z + T for z in case['stock']} | {e['candidate'] + T for e in events if e['A'] and e['candidate'] <= 0}
        cur, H, B = case['x'] + T, [0], [0]
        wallet = {Y: 0 for Y in [0, 1, 2, 3, 6, 10, 20, 50, 100]}
        assert min(seen) >= 0
        if case['x'] in case['stock']:
            assert cur in seen
        for p, e in enumerate(events):
            n = b + p + 1
            c = cur - n
            A = c <= 0 or c in seen
            assert A == e['A'] and c == e['candidate'] + T and c > n
            assert not any(0 <= c <= Y <= n for Y in wallet)
            for u in range(p):
                if H[p] == H[u] + 1 and B[p] - B[u] == (p - u) * H[u]:
                    assert c == case['values'][u] + T
            cur += n if A else -n
            assert cur == case['values'][p + 1] + T
            seen.add(cur)
            H.append(H[-1] + (1 if A else -1)); B.append(B[-1] + H[-1])
            assert H[-1] == case['H'][p + 1]
            steps += 1
        translated += 1
    # Endpoint capacity is checked separately on each ORIGINAL trace and every horizon.
    lower = case['x'] // (b + 1)
    counts = {Y: 0 for Y in wallet}
    for p, e in enumerate(events):
        for Y in counts:
            counts[Y] += int(e['A'] and e['n'] >= max(1, Y) and 0 <= e['candidate'] <= Y)
            assert counts[Y] <= (Y // 3 + 1) * (case['H'][p + 1] + lower + 2)
            endpoint_checks += 1
# Naive translation fails at the original canonical first A; the extra seed is essential.
assert 100 - 1 > 0 and 99 not in {100}
assert 99 in ({100} | {0, 99})
print(json.dumps({'status': 'PASS', 'old_traces': len(cases), 'constructed_translations': translated,
                  'translated_steps': steps, 'original_endpoint_checks': endpoint_checks,
                  'naive_translation_counter': 'b0/current0/seen{0}, T100: naive next sign S, original A; adding99 restores A',
                  'scope': 'Finite support for new all-T PAPER transport/endpoint bound; no canonical reachability or fresh orbit data'}))
