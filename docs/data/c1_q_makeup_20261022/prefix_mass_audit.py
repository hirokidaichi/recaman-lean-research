"""Independent prefix-language audit and small-tail differential check."""
import argparse
import json
from pathlib import Path
import time

from context_tree_audit import supplied_before_A


def words_by_mass(limit):
    words = [set() for _ in range(limit+1)]
    words[0].add('')
    for mass in range(limit+1):
        for w in list(words[mass]):
            for dm, atom in [(1, 'A'), (2, 'SAAA'), (4, 'SSAAAASAAA')]:
                if mass+dm <= limit:
                    words[mass+dm].add(w+atom)
    return words


def prefix_state(word):
    current = ''
    levels, deficit = [0], 0
    for c in word:
        e = c == 'A' and supplied_before_A(current)
        deficit += (c == 'S')-e
        levels.append(levels[-1]+(1 if c == 'A' else -1))
        assert deficit >= 0, (word, current, deficit)
        current += c
    assert deficit == 0, (word, deficit)
    return tuple(levels)


def check_prefixes(limit):
    started = time.monotonic()
    groups = words_by_mass(limit)
    recurrence = [0]*(limit+1)
    recurrence[0] = 1
    maxlen = 0
    for mass, rows in enumerate(groups):
        if mass:
            recurrence[mass] = sum(recurrence[mass-d] for d in (1, 2, 4) if d <= mass)
        assert len(rows) == recurrence[mass]
        for word in rows:
            levels = prefix_state(word)
            assert levels[-1] == mass
            maxlen = max(maxlen, len(word))
    return groups, dict(status='passed', max_mass=limit, counts=[len(rows) for rows in groups],
                        words=sum(map(len, groups)), max_length=maxlen,
                        full_prefix_deficit_zero_and_nonnegative=True,
                        elapsed_seconds=time.monotonic()-started)


def check_tail(limit, groups, expected):
    counts = dict(nodes=0, S_cuts=0, A_cuts=0, zero_cuts=0, return_cuts=0)
    stats = [dict(az=i, count=0, maxS=-1, maxDepth=-1, maxLength=-1,
                  minAz=10**9, minR_or_Q0=10**9, zwords=set()) for i in range(4)]
    smax = (limit+1)//2
    def visit(word, levels, deficit, az, ns, n, g):
        counts['nodes'] += 1
        used = len(word)-n
        if deficit == 1:
            s = stats[az]
            s['count'] += 1
            s['maxS'] = max(s['maxS'], ns)
            s['maxDepth'] = max(s['maxDepth'], g-min(levels[n:]))
            s['maxLength'] = max(s['maxLength'], used)
            area = sum(v-g+1 for v in levels[n+1:])
            h = levels[-1]-g
            r = area+h*(h+1)//2 if h > 0 else sum(v-levels[-1]+1 for v in levels[n+1:])
            s['minAz'] = min(s['minAz'], area)
            s['minR_or_Q0'] = min(s['minR_or_Q0'], r)
            s['zwords'].add(word[n:])
            assert s['maxDepth'] < 5, 'actual deep witness in small audit; inspect instead of treating as routine failure'
        if used == limit:
            return
        if deficit-1 > limit-used:
            counts['return_cuts'] += 1
            return
        for c in 'SA':
            if c == 'S' and ns == smax:
                counts['S_cuts'] += 1
                continue
            e = c == 'A' and supplied_before_A(word)
            na = az+(c == 'A' and not e)
            nd = deficit+(c == 'S')-e
            if na > 3:
                counts['A_cuts'] += 1
                continue
            if nd < 1:
                counts['zero_cuts'] += 1
                continue
            visit(word+c, levels+(levels[-1]+(1 if c == 'A' else -1),), nd, na,
                  ns+(c == 'S'), n, g)
    started = time.monotonic()
    for rows in groups:
        for word in rows:
            levels = prefix_state(word)
            visit(word, levels, 0, 0, 0, len(word), levels[-1])
    for s in stats:
        s['zwords'] = sorted(s['zwords'])
    assert expected['complete']
    for key, value in counts.items():
        assert expected[key] == value, (key, expected[key], value)
    assert expected['classes'] == stats
    assert expected['prefix_counts'] == [len(rows) for rows in groups]
    return dict(status='passed', tail_limit=limit, counts=counts, classes=stats,
                elapsed_seconds=time.monotonic()-started,
                window_test='backwards mass/moment all starts', area_test='direct sum', mod4_filter=False)


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--max-mass', type=int, required=True)
    ap.add_argument('--tail-limit', type=int)
    ap.add_argument('--expected', type=Path)
    ap.add_argument('--out', type=Path, required=True)
    args = ap.parse_args()
    groups, result = check_prefixes(args.max_mass)
    if args.tail_limit is not None:
        result['tail_audit'] = check_tail(args.tail_limit, groups, json.loads(args.expected.read_text()))
    args.out.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k:v for k, v in result.items() if k != 'tail_audit'}))
