"""Independent reverse arithmetic plus full old/new product simulation for H03."""
from pathlib import Path
from collections import deque
from functools import lru_cache
from itertools import product
import datetime, hashlib, json, resource, time

BASE = Path(__file__).parent

@lru_cache(None)
def rev(w):
    m = ar = top = 0
    le = False
    for k, c in enumerate(reversed(w), 1):
        s = 1 if c == 'A' else -1
        m += s
        ar += k*s
        top = max(top, m)
        le |= m == 1 and ar == 0
    return m, ar, top, le

def cut(w, B):
    w = w[-19:]
    choices = [w[t:] for t in range(1, len(w)+1)
               if rev(w[t:])[0]+rev(w[:t])[2]+B <= 0]
    return min(choices, key=len) if choices else w

def step(state, j, e):
    w, ar, a, ss, free = state
    ns = min(ss+j, 19)
    q = w+'S'*j
    # Work from the complete untrimmed q for local checks and holdout.
    le = rev(q)[3]
    next_ar = 0 if ns == 19 else ar+sum(a-ss-k for k in range(1, j+1))
    R = 1-a+ns
    D = -next_ar-(a+ns)*R
    old = ns < 19 and ((R == 1 and D == 1) or (
        R >= 2 and R*(R+1)//2-1 <= D <= (5*R*R-11*R+16)//4))
    if (e == 1 and not (le or old)) or (e == 0 and le):
        return None
    fn = free+(e == 0)
    if fn > 4 or (ns < 19 and ns-a-1+fn < 1):
        return None
    g = cut(q, 10-a)
    return (cut(g+'A', 9-a) if a < 10 else g+'A',
            0 if ns == 19 else next_ar+a-ns+1, a+1, ns, fn)

def main():
    resource.setrlimit(resource.RLIMIT_CPU, (40, 41))
    start = time.monotonic()
    new = json.loads((BASE/'context-certificate.json').read_text())['rows']
    old = json.loads((BASE.parent/'c1_four_20261024/macro-certificate.json').read_text())['rows']
    for row in new:
        for j in range(20):
            for e in (0, 1):
                target = row['edges'][2*j+e]
                assert step(tuple(row['state']), j, e) == (None if target is None else tuple(new[target]['state']))
    todo = deque([(0, 0)])
    seen = set()
    endpoint_checks = 0
    while todo:
        if time.monotonic()-start > 37:
            raise TimeoutError('incomplete')
        pair = todo.popleft()
        if pair in seen:
            continue
        seen.add(pair)
        assert len(seen) <= 100000, 'product state guard'
        oi, ni = pair
        os, ns = old[oi]['state'], new[ni]['state']
        ow, a, ss, free = os
        ctx, ar, na, nss, nf = ns
        assert (a, ss, free) == (na, nss, nf)
        assert ar == (0 if ss == 19 else rev(ow)[1])
        assert ow.endswith(ctx)
        for j in range(20):
            original = ow+'S'*j
            context = cut(ctx+'S'*j, 10-a)
            assert rev(original)[3] == rev(context)[3]
            sn = min(ss+j, 19)
            if sn-a+free == 1:
                # An endpoint's context must be the ENTIRE actual word.
                assert len(context) == a+sn and context == original
                assert context in json.loads((BASE.parent/'c1_four_20261024/macro-certificate.json').read_text())['classes'][free]
                endpoint_checks += 1
            for e in (0, 1):
                ot, nt = old[oi]['edges'][2*j+e], new[ni]['edges'][2*j+e]
                assert (ot is None) == (nt is None), (pair, j, e)
                if ot is not None:
                    todo.append((ot, nt))
    assert len({n for _, n in seen}) == len(new)
    selected = []
    for free in range(5):
        selected += sorted(tuple(r['state']) for r in new if r['state'][4] == free)[:16]
    controls = 0
    for s in selected:
        for j in (29, 43, 269, 4111):
            for e in (0, 1):
                assert step(s, j, e) == step(s, 19, e)
                controls += 1
    # Fresh exact finite future-equivalence attack, separate lengths.
    checks = {}
    for name, lens in [('discovery', range(4)), ('holdout', range(4, 6))]:
        ws = [''.join(v) for n in lens for v in product('SA', repeat=n)]
        xs = [''.join(v) for n in lens for v in product('SA', repeat=n)]
        count = 0
        for w in ws:
            for B in range(3):
                cw = cut(w, B)
                for x in xs:
                    if x.count('A') <= B:
                        assert rev(w+x)[3] == rev(cw+x)[3]
                        count += 1
        checks[name] = count
    assert rev('SSAAAAS')[3] and not rev('SAAAAS')[3], 'budget omission counterexample'
    out = {'complete': True, 'old_new_product_pairs': len(seen), 'new_states': len(new),
           'all_old_and_new_transitions_match': True, 'endpoint_full_word_checks': endpoint_checks,
           'long_gap_controls': controls, 'future_equivalence_checks': checks,
           'elapsed_seconds': time.monotonic()-start, 'cpu_seconds': time.process_time(),
           'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
           'utc': datetime.datetime.now(datetime.timezone.utc).isoformat()}
    (BASE/'context-independent.json').write_text(json.dumps(out, indent=2)+'\n')
    print(json.dumps(out))

if __name__ == '__main__':
    main()
