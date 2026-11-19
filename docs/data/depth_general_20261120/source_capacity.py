"""New source-capacity predicates on frozen old and small finite controls."""
import json, sys
from pathlib import Path

cfg = json.loads(Path(sys.argv[1]).read_text())
counts = {'steps': 0, 'source_target_pairs': 0, 'reused_sources': 0, 'non_P2_blocked_additions': 0}
examples = []
for case in cfg['cases']:
    b, x, seen = case['base'], case['value'], set(case['seen'])
    signs, xs, hs, bs, candidates = [], [x], [0], [0], []
    for p in range(case['steps']):
        n = b + p + 1
        c = x - n
        a = not (c > 0 and c not in seen)
        candidates.append(c)
        sig = 1 if a else -1
        signs.append(sig)
        x += n * sig
        seen.add(x)
        xs.append(x); hs.append(hs[-1] + sig); bs.append(bs[-1] + hs[-1])
    uses = [[] for _ in signs]
    for p, sig in enumerate(signs):
        if sig != 1:
            continue
        mass = area = 0
        literal = []
        for u in range(p - 1, -1, -1):
            mass += signs[u]
            area += (p - u) * signs[u]
            if mass == 1 and area == 0:
                literal.append(u)
        forward = [u for u in range(p) if hs[p] - hs[u] == 1 and bs[p] - bs[u] == (p - u) * hs[u]]
        assert sorted(literal) == forward
        for u in literal:
            assert candidates[p] == xs[u] and hs[p] == hs[u] + 1
            uses[u].append(p)
        if not literal and candidates[p] > 0:
            counts['non_P2_blocked_additions'] += 1
    for u, targets in enumerate(uses):
        M = len(targets)
        if not M:
            continue
        y, a = xs[u], b + u
        counts['source_target_pairs'] += M
        assert M <= max(1, y - 2)
        assert b + targets[0] + 1 >= a + 4
        late = [p for p in targets if b + p + 1 >= max(1, y - 6)]
        assert len(late) <= 1
        if M >= 2:
            counts['reused_sources'] += 1
            k = M - 2
            assert all(b + p + 1 <= y - 7 for p in targets[:-1])
            assert 10 * k - 2 * (k % 2) <= y - a - 11
            assert y >= a + 11
            assert M <= 2 + (y - a - 9) // 10
            if len(examples) < 8:
                examples.append({'case': case['name'], 'u': u, 'value': y, 'source_clock': a, 'targets': targets})
    counts['steps'] += len(signs)
print(json.dumps({'status': 'PASS', 'scope': 'finite controls for NEW predicates, not an arbitrary-depth proof or fresh orbit data', **counts, 'reuse_examples': examples}, sort_keys=True))
