"""Check the new cross-height rank on hashed, already generated finite traces."""
import json, sys
from pathlib import Path

d = json.loads(Path(sys.argv[1]).read_text())
cases = d['sharp_threshold'] + d['sharp_count'] + d['regressions']
comparisons = selected = 0
for case in cases:
    seen = set(case['stock'])
    x, h, b = case['x'], 0, case['b']
    for p, e in enumerate(case['events']):
        n = b + p + 1
        c = x - n
        add = c <= 0 or c in seen
        assert e['q'] == p and e['n'] == n and e['candidate'] == c and e['A'] == add
        assert case['H'][p] == h and case['values'][p] == x
        x += n if add else -n
        h += 1 if add else -1
        assert x > 0
        seen.add(x)
    for Y in range(101):
        previous = None
        K = Y // 3 + 1
        for e in case['events']:
            p, c = e['q'], e['candidate']
            if not e['A'] or e['n'] < max(1, Y) or not 0 <= c <= Y:
                continue
            H = case['H'][p]
            phi = K * H - c // 3
            selected += 1
            if previous is not None:
                pp, pc, ph, pr = previous
                assert H >= ph, (Y, pp, p, ph, H)
                assert phi >= pr + 1, (Y, pp, p, pr, phi)
                if H == ph:
                    assert c <= pc - 3
                comparisons += 1
            previous = p, c, H, phi
print(json.dumps({'status': 'PASS', 'trace_count': len(cases), 'Y_controls': [0, 100], 'selected_events': selected,
                  'rank_comparisons': comparisons, 'scope': 'NEW rank predicate on OLD hashed finite traces; no fresh orbit/holdout claim'}))
