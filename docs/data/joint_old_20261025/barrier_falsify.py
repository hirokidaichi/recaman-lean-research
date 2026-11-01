"""Frozen small/boundary/weakening attack on H-20261025-02 before formalization."""
from functools import lru_cache
from itertools import product
from pathlib import Path
import hashlib, json, resource, time

def words(lengths):
    return [''.join(w) for n in lengths for w in product('SA', repeat=n)]

@lru_cache(None)
def local(w):
    m = p = 0
    for k, c in enumerate(reversed(w), 1):
        d = 1 if c == 'A' else -1
        m += d
        p += k*d
        if m == 1 and p == 0:
            return True
    return False

def main():
    resource.setrlimit(resource.RLIMIT_CPU, (10, 11))
    start = time.monotonic()
    out = {}
    for name, us, vs in [('discovery', words(range(6)), words(range(6))),
                         ('holdout', words(range(6, 8)), words(range(6, 8)))]:
        checks = boundaries = 0
        weak = {1: None, 2: None}
        for u in us:
            for v in vs:
                if time.monotonic()-start > 9:
                    raise TimeoutError('incomplete')
                barrier = v.count('A')-v.count('S')+u.count('A')
                if barrier <= 0:
                    assert local(u+v) == local(v), (u, v)
                    checks += 1
                    boundaries += barrier == 0
                for relaxation in weak:
                    if weak[relaxation] is None and barrier <= relaxation and local(u+v) != local(v):
                        weak[relaxation] = {'u': u, 'v': v, 'barrier': barrier,
                                            'before': local(u+v), 'after': local(v)}
        out[name] = {'checks': checks, 'boundary_checks': boundaries,
                     'weakened_barrier_counterexamples': weak}
    out.update(complete=True, elapsed_seconds=time.monotonic()-start,
               cpu_seconds=time.process_time(),
               source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    Path(__file__).with_name('barrier-falsification.json').write_text(json.dumps(out, indent=2)+'\n')
    print(json.dumps(out))

if __name__ == '__main__':
    main()
