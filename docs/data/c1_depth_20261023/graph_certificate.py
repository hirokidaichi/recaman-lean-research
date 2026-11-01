"""BFS certificate with literal states and forward suffix-area semantics."""
from collections import deque
import hashlib
import json
from pathlib import Path
import resource
import time

resource.setrlimit(resource.RLIMIT_CPU, (30, 32))


def local(w):
    for t in range(len(w)):
        mass = area = 0
        for c in w[t:]:
            mass += 1 if c == 'A' else -1
            area += mass
        if mass == 1 and area == 0:
            return True
    return False


def old(w):
    mass = area = 0
    for c in w:
        mass += 1 if c == 'A' else -1
        area += mass
    r = 1-mass
    b = -area-len(w)*r
    return r >= 1 and b >= 1 and r*(r+1) <= 2*b+2 and 4*b <= 5*r*r-11*r+16 and (r != 1 or b == 1)


def transitions(st):
    w, a, s, az = st
    s1 = min(13, s+1)
    ans = [('S', ((w+'S')[-13:] if s1 == 13 else w+'S', a, s1, az))]
    le = local(w)
    oe = s < 13 and old(w)
    for e in (0, 1):
        if (e == 0 and le) or (e == 1 and not (le or oe)):
            continue
        new_az = az+1-e
        if new_az > 3 or (s < 13 and s-(a+1)+new_az < 1):
            continue
        ans.append(('A'+str(e), ((w+'A')[-13:] if s == 13 else w+'A', a+1, s, new_az)))
    return ans


def main():
    start = time.monotonic()
    states = [('', 0, 0, 0)]
    index = {states[0]: 0}
    q = deque([states[0]])
    rows = []
    exceptions = []
    while q:
        st = q.popleft()
        if st[1] >= 8:
            raise AssertionError(('eighth A in relaxed graph', st))
        edges = []
        w, a, s, az = st
        if s < 13 and old(w) and not local(w):
            exceptions.append(dict(tail=w, additions=a, subtractions=s, nonsupplied=az))
        for tag, target in transitions(st):
            if target not in index:
                index[target] = len(states)
                states.append(target)
                q.append(target)
            edges.append([tag, index[target]])
        rows.append(dict(state=list(st), edges=edges))
    for i, row in enumerate(rows):
        assert tuple(row['state']) == states[i]
        assert [(tag, states[j]) for tag, j in row['edges']] == transitions(states[i])
    usage = resource.getrusage(resource.RUSAGE_SELF)
    result = dict(graph_exhausted=True, rows=rows, old_optional_states=exceptions,
                  states=len(states), highest_A=max(s[1] for s in states),
                  elapsed_seconds=time.monotonic()-start,
                  user_seconds=usage.ru_utime, system_seconds=usage.ru_stime,
                  source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    p = Path(__file__).parent
    (p/'certificate.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'rows'}))


if __name__ == '__main__':
    main()
