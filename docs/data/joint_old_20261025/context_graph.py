"""H03: future-safe local context, exact aggregate old area until S saturation."""
from pathlib import Path
from functools import lru_cache
import datetime, hashlib, json, resource, time

BASE = Path(__file__).parent

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

@lru_cache(None)
def ceiling(w):
    return max([0]+[signature(w[t:])[0] for t in range(len(w))])

@lru_cache(None)
def context(B, w):
    w = w[-19:]
    for t in reversed(range(1, len(w)+1)):
        if signature(w[t:])[0]+ceiling(w[:t])+B <= 0:
            return w[t:]
    return w

def gap(st, j):
    w, ar, a, ss, free = st
    sn = min(19, ss+j)
    arn = 0 if sn == 19 else ar+j*(a-ss)-j*(j+1)//2
    return context(10-a, w+'S'*j), arn, a, sn, free

def move(st, j, e):
    w, ar, a, ss, free = gap(st, j)
    le = local(w)
    R = 1-a+ss
    D = -ar-(a+ss)*R
    old = (ss < 19 and R >= 1 and D >= 1 and R*(R+1) <= 2*D+2
           and 4*D <= 5*R*R-11*R+16 and (R != 1 or D == 1))
    an = free+1-e
    if (e and not (le or old)) or (not e and le) or an > 4 or (ss < 19 and ss-a-1+an < 1):
        return None
    # The A11 transition remains part of the model and is an error witness.
    if a == 10:
        return (w+'A', 0 if ss == 19 else ar+a-ss+1, a+1, ss, an)
    return context(9-a, w+'A'), 0 if ss == 19 else ar+a-ss+1, a+1, ss, an

def main():
    resource.setrlimit(resource.RLIMIT_CPU, (30, 31))
    start = time.monotonic()
    states = [('', 0, 0, 0, 0)]
    ids = {states[0]: 0}
    rows = []
    while len(rows) < len(states):
        if time.monotonic()-start > 28:
            raise TimeoutError('incomplete')
        if len(states) > 50000:
            raise RuntimeError('state guard')
        st = states[len(rows)]
        assert st[2] <= 10, ('A11 witness', st)
        edges = []
        for j in range(20):
            for e in (0, 1):
                child = move(st, j, e)
                if child is None:
                    edges.append(None)
                else:
                    if child not in ids:
                        ids[child] = len(states)
                        states.append(child)
                    edges.append(ids[child])
        rows.append({'state': st, 'edges': edges})
    out = {'complete': True, 'states': len(states), 'edges': sum(t is not None for r in rows for t in r['edges']),
           'max_context': max(len(s[0]) for s in states),
           'by_free': {r: sum(s[4] == r for s in states) for r in range(5)},
           'highest_A': max(s[2] for s in states), 'rows': rows,
           'elapsed_seconds': time.monotonic()-start, 'cpu_seconds': time.process_time(),
           'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
           'utc': datetime.datetime.now(datetime.timezone.utc).isoformat()}
    (BASE/'context-certificate.json').write_text(json.dumps(out, separators=(',', ':'))+'\n')
    print(json.dumps({k: v for k, v in out.items() if k != 'rows'}))

if __name__ == '__main__':
    main()
