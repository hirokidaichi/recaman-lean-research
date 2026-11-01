"""Independent reverse-moment DFS and unused long-gap controls, H-20261025-01."""
from pathlib import Path
from functools import lru_cache
import datetime, hashlib, json, resource, time

BASE = Path(__file__).parent
ROOTS = ('', 'AAA', 'SAAAA', 'ASAAA', 'AAAA', 'AASAAA', 'ASAAAA',
         'SAAAAA', 'SAAASAAA', 'SSAAAASAAA')

@lru_cache(None)
def reverse_data(v):
    m = p = 0
    supplied = False
    profile = set()
    for k, c in enumerate(reversed(v), 1):
        d = 1 if c == 'A' else -1
        m += d
        p += k*d
        supplied |= m == 1 and p == 0
        if m in (3, 4):
            profile.add((m, p))
    return m, p, supplied, frozenset(profile)

def next_state(root, state, j, e):
    v, a, ss, free = state
    v += 'S'*j
    sn = min(ss+j, 19)
    mass, area, le, _ = reverse_data(v)
    if sn == 19:
        possible = le if e else not le
    else:
        mass_needed = 1-mass
        area_needed = -area-len(v)*mass_needed
        if mass_needed in (3, 4):
            available = le or (mass_needed, area_needed) in reverse_data(root)[3]
            possible = available if e else not available
        else:
            old = (mass_needed == 1 and area_needed == 1) or (
                mass_needed >= 2 and mass_needed*(mass_needed+1)//2-1 <= area_needed
                <= (5*mass_needed*mass_needed-11*mass_needed+16)//4)
            possible = (le or old) if e else not le
    fnext = free+(e == 0)
    if not possible or fnext > 4 or (sn < 19 and sn-a-1+fnext < 1):
        return None
    v += 'A'
    return (v[-19:] if sn == 19 else v, a+1, sn, fnext)

def main():
    resource.setrlimit(resource.RLIMIT_CPU, (70, 71))
    start = time.monotonic()
    summaries = []
    controls = 0
    for root in ROOTS:
        todo = [('', 0, 0, 0)]
        seen = {}
        endpoints = [set() for _ in range(5)]
        while todo:
            if time.monotonic()-start > 65:
                raise TimeoutError('incomplete: independent wall guard')
            s = todo.pop()
            if s in seen:
                continue
            assert s[1] <= 10, ('A11 witness', root, s)
            assert len(seen) <= 150000, 'state guard'
            row = {}
            for j in reversed(range(20)):
                v = s[0]+'S'*j
                sn = min(s[2]+j, 19)
                if sn-s[1]+s[3] == 1:
                    endpoints[s[3]].add(v[-19:] if sn == 19 else v)
                for e in (1, 0):
                    t = next_state(root, s, j, e)
                    row[j, e] = t
                    if t is not None:
                        todo.append(t)
            seen[s] = row
        cert = json.loads((BASE/('graph-'+(root or 'empty')+'.json')).read_text())
        rs = cert['rows']
        normalized = {tuple(row['state']): {
            (j, e): None if row['edges'][2*j+e] is None else tuple(rs[row['edges'][2*j+e]]['state'])
            for j in range(20) for e in (0, 1)} for row in rs}
        assert seen == normalized, ('full edge mismatch', root)
        assert [sorted(c) for c in endpoints] == cert['classes']
        selected = []
        for free in range(5):
            selected += sorted(s for s in seen if s[3] == free)[:16]
        for s in selected:
            for j in (23, 41, 263, 4103):
                for e in (0, 1):
                    assert next_state(root, s, j, e) == next_state(root, s, 19, e), (root, s, j, e)
                    controls += 1
        summaries.append({'root': root, 'states': len(seen), 'all_edges_match': True,
                          'classes': [sorted(c) for c in endpoints], 'holdout_states': len(selected)})
        reverse_data.cache_clear()
    # Known adversarial controls, not a fresh holdout.
    tail = 'S'*5+'A'*3+'S'*4+'A'*4+'S'+'A'*3
    real_controls = []
    for root in ('ASAAA', 'AASAAA', 'SAAASAAA', 'SSAAAASAAA'):
        state = ('', 0, 0, 0)
        history = root
        pending = free = supplies_after_last = 0
        for c in tail:
            if c == 'S':
                history += c
                pending += 1
                continue
            e = int(reverse_data(history)[2])
            assert next_state(root, state, pending, e) is not None, ('lost real transition', root, state, pending, e)
            state = next_state(root, state, pending, e)
            free += 1-e
            supplies_after_last = supplies_after_last+1 if e else 0
            pending = 0
            history += c
        assert free == 4 and supplies_after_last == 5
        real_controls.append({'root': root, 'free': free, 'supplies_after_last_free': supplies_after_last})
    for root in ROOTS:
        assert next_state(root, ('', 0, 0, 0), 19, 0) is not None
        assert next_state(root, ('', 10, 0, 3), 20, 0)[1] == 11
    out = {'complete': True, 'root_results': summaries, 'long_gap_tag_controls': controls,
           'known_real_controls': real_controls, 'A11_and_saturated_free_A_retained': True,
           'elapsed_seconds': time.monotonic()-start, 'cpu_seconds': time.process_time(),
           'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
           'utc': datetime.datetime.now(datetime.timezone.utc).isoformat()}
    (BASE/'independent-summary.json').write_text(json.dumps(out, indent=2)+'\n')
    print(json.dumps(out))

if __name__ == '__main__':
    main()
