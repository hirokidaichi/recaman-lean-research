"""H-20261025-01 frozen fixed-root r4 relaxation; not a proof of C1."""
from pathlib import Path
from functools import lru_cache
import datetime, hashlib, json, resource, time

BASE = Path(__file__).parent
ROOTS = ('', 'AAA', 'SAAAA', 'ASAAA', 'AAAA', 'AASAAA', 'ASAAAA',
         'SAAAAA', 'SAAASAAA', 'SSAAAASAAA')

@lru_cache(None)
def signature(w):
    f = ar = 0
    for c in w:
        f += 1 if c == 'A' else -1
        ar += f
    return f, ar

@lru_cache(None)
def local(w):
    return any(signature(w[t:]) == (1, 0) for t in range(len(w)))

def profile(root):
    return frozenset(signature(root[t:]) for t in range(len(root))
                     if signature(root[t:])[0] in (3, 4))

PROFILES = {r: profile(r) for r in ROOTS}

def gap(st, j):
    w, a, ss, free = st
    ns = min(19, ss+j)
    v = w+'S'*j
    return (v[-19:] if ns == 19 else v, a, ns, free)

def old_info(w):
    f, ar = signature(w)
    r = 1-f
    b = -ar-len(w)*r
    necessary = (r >= 1 and b >= 1 and r*(r+1) <= 2*b+2
                 and 4*b <= 5*r*r-11*r+16 and (r != 1 or b == 1))
    return r, b, necessary

def move(root, st, j, e):
    w, a, ss, free = gap(st, j)
    le = local(w)
    if ss == 19:
        # No true-mass inference from this trimmed word is permitted.
        admitted = le if e else not le
    else:
        r, b, necessary = old_info(w)
        if r in (3, 4):
            actual = le or (r, b) in PROFILES[root]
            admitted = actual if e else not actual
        else:
            admitted = (le or necessary) if e else not le
    an = free+1-e
    if not admitted or an > 4 or (ss != 19 and ss-a-1+an < 1):
        return None
    v = w+'A'
    return (v[-19:] if ss == 19 else v, a+1, ss, an)

def graph(root, start, wall):
    states = [('', 0, 0, 0)]
    indices = {states[0]: 0}
    rows = []
    classes = [set() for _ in range(5)]
    while len(rows) < len(states):
        if time.monotonic()-start > wall:
            raise TimeoutError('incomplete: wall guard')
        if len(states) > 150000:
            raise RuntimeError('incomplete: state guard')
        st = states[len(rows)]
        if st[1] > 10:
            raise RuntimeError(('A11 retained; stop and save witness', root, st))
        for j in range(20):
            w, a, ss, free = gap(st, j)
            if ss-a+free == 1:
                classes[free].add(w)
        edges = []
        for j in range(20):
            for e in (0, 1):
                target = move(root, st, j, e)
                if target is None:
                    edges.append(None)
                    continue
                if target not in indices:
                    indices[target] = len(states)
                    states.append(target)
                edges.append(indices[target])
        rows.append({'state': list(st), 'edges': edges})
    return {'root': root, 'states': len(states), 'processed': len(rows),
            'highest_A': max(s[1] for s in states),
            'classes': [sorted(c) for c in classes], 'rows': rows}

def main():
    resource.setrlimit(resource.RLIMIT_CPU, (70, 71))
    start = time.monotonic()
    results = []
    for root in ROOTS:
        result = graph(root, start, 65)
        (BASE/('graph-'+(root or 'empty')+'.json')).write_text(
            json.dumps(result, separators=(',', ':'))+'\n')
        results.append({k: v for k, v in result.items() if k != 'rows'})
    old = json.loads((BASE.parent/'c1_four_20261024/macro-certificate.json').read_text())
    oldstates = {tuple(r['state']) for r in old['rows']}
    projection = set()
    projected_edges = set()
    for root in ROOTS:
        rs = json.loads((BASE/('graph-'+(root or 'empty')+'.json')).read_text())['rows']
        for row in rs:
            s = tuple(row['state'])
            projection.add(s)
            for i, t in enumerate(row['edges']):
                if t is not None:
                    projected_edges.add((s, i//2, i%2, tuple(rs[t]['state'])))
    oldedges = {(tuple(row['state']), i//2, i%2, tuple(old['rows'][t]['state']))
                for row in old['rows'] for i, t in enumerate(row['edges']) if t is not None}
    assert projection <= oldstates and projected_edges <= oldedges
    summary = {'complete': True, 'root_results': results,
               'root_total_states': sum(r['states'] for r in results),
               'max_root_states': max(r['states'] for r in results),
               'old_states': len(oldstates), 'projected_states': len(projection),
               'removed_states': len(oldstates-projection),
               'old_edges': len(oldedges), 'projected_edges': len(projected_edges),
               'removed_edges': len(oldedges-projected_edges),
               'removed_state_examples': sorted(oldstates-projection)[:8],
               'removed_edge_examples': sorted(oldedges-projected_edges)[:8],
               'elapsed_seconds': time.monotonic()-start,
               'cpu_seconds': time.process_time(),
               'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
               'utc': datetime.datetime.now(datetime.timezone.utc).isoformat()}
    (BASE/'fixed-summary.json').write_text(json.dumps(summary, indent=2)+'\n')
    print(json.dumps(summary))

if __name__ == '__main__':
    main()
