"""Independent exhaustive audit using backwards mass/moment, no G or mod-4 filter."""
import argparse
from functools import cache
import json
from pathlib import Path
import time

from semantic_cases import walk


@cache
def supplied_before_A(word):
    mass = moment = 0
    b = len(word)
    for t in range(b-1, -1, -1):
        sign = 1 if word[t] == 'A' else -1
        mass += sign
        moment += sign*(b-t)
        if mass == 1 and moment == 0:
            return True
    return False


def audit(reps, expected):
    counts = dict(nodes=0, max_tail_length=0, z_endpoints=0, guard_endpoints=0,
                  depth_cuts=0, budget_cuts=0, zero_cuts=0)
    stats = [dict(az=i, count=0, maxS=-1, minAz=10**9, minR=10**9, zwords=set()) for i in range(4)]
    minq = 10**9
    def node(word, n):
        counts['nodes'] += 1
        counts['max_tail_length'] = max(counts['max_tail_length'], len(word)-n)
        assert len(word)-n < 512, 'protection guard reached; not a complete classification'
    def successor(word, levels, deficit, new_as, c):
        e = c == 'A' and supplied_before_A(word)
        return (word+c, levels+(levels[-1]+(1 if c == 'A' else -1),),
                deficit+(c == 'S')-e, new_as+(c == 'A' and not e))
    def ywalk(word, levels, deficit, ay, n, g):
        nonlocal minq
        node(word, n)
        for c in 'SA':
            nw, nl, nd, na = successor(word, levels, deficit, ay, c)
            if na > 1:
                counts['budget_cuts'] += 1
                continue
            if nd < 1:
                counts['zero_cuts'] += 1
                continue
            if levels[-1] <= g:
                counts['guard_endpoints'] += 1
                z = sum(f-levels[-1]+1 for f in levels[n+1:])
                minq = min(minq, z)
                assert z >= 0, (nw, n, z)
            if nl[-1] < g-4:
                counts['depth_cuts'] += 1
                continue
            ywalk(nw, nl, nd, na, n, g)
    def zwalk(word, levels, deficit, az, ns, n, g):
        node(word, n)
        if deficit == 1:
            counts['z_endpoints'] += 1
            s = stats[az]
            s['count'] += 1
            s['maxS'] = max(s['maxS'], ns)
            s['zwords'].add(word[n:])
            area = sum(f-g+1 for f in levels[n+1:])
            h = levels[-1]-g
            r = area+h*(h+1)//2 if h > 0 else sum(f-levels[-1]+1 for f in levels[n+1:])
            s['minAz'] = min(s['minAz'], area)
            s['minR'] = min(s['minR'], r)
            ywalk(word, levels, deficit, 0, n, g)
        for c in 'SA':
            nw, nl, nd, na = successor(word, levels, deficit, az, c)
            if nl[-1] < g-4:
                counts['depth_cuts'] += 1
                continue
            if na > 3:
                counts['budget_cuts'] += 1
                continue
            if nd < 1:
                counts['zero_cuts'] += 1
                continue
            zwalk(nw, nl, nd, na, ns+(c == 'S'), n, g)
    started = time.monotonic()
    for row in reps:
        word = row['prefix']
        levels, starts, _ = walk(word)
        deficit = sum(c == 'S' for c in word)-sum(c == 'A' and bool(starts[i]) for i, c in enumerate(word))
        assert deficit == 0
        zwalk(word, tuple(levels), 0, 0, 0, len(word), levels[-1])
    for s in stats:
        s['zwords'] = sorted(s['zwords'])
    assert expected['complete'] and expected['reason'] == 'complete'
    for key, value in counts.items():
        assert expected[key] == value, (key, expected[key], value)
    assert stats == expected['classes'], (stats, expected['classes'])
    assert minq == expected['minQ']['value']
    return dict(status='passed', elapsed_seconds=time.monotonic()-started,
                independent_window_test='backwards signed mass and weighted moment, all starts',
                independent_area_test='direct sum of all levels', mod_four_filter=False,
                complete_tree=True, counts=counts, classes=stats, minQ=minq,
                cached_prefixes=supplied_before_A.cache_info().currsize)


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--directory', type=Path, default=Path(__file__).parent)
    args = ap.parse_args()
    p = args.directory
    result = audit(json.loads((p/'contexts.json').read_text()), json.loads((p/'context-classify.json').read_text()))
    (p/'context-tree-audit.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ('status', 'elapsed_seconds', 'complete_tree', 'counts', 'minQ')}))
