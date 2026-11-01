"""Attack <=1 using leading A plus a balanced tail; fresh lengths10/14/18."""
from pathlib import Path
from itertools import combinations
import hashlib, json, resource, time

def local(v):
    m = ar = 0
    for k, c in enumerate(reversed(v), 1):
        s = 1 if c == 'A' else -1
        m += s
        ar += k*s
        if m == 1 and ar == 0:
            return True
    return False

def main():
    resource.setrlimit(resource.RLIMIT_CPU, (5, 6))
    start = time.monotonic()
    results = {}
    for n in (10, 14, 18):
        count = candidates = 0
        examples = []
        for positions in combinations(range(n), n//2):
            if time.monotonic()-start > 4.5:
                raise TimeoutError('incomplete')
            inds = set(positions)
            v = ''.join('A' if i in inds else 'S' for i in range(n))
            count += 1
            f = ar = 0
            for c in v:
                f += 1 if c == 'A' else -1
                ar += f
            if ar == -n-1 and not local(v):
                assert local('A'+v) and f == 0
                candidates += 1
                if len(examples) < 3:
                    examples.append({'u': 'A', 'v': v, 'mass_v': 0,
                                     'suffixCeiling_u': 1, 'area_v': ar,
                                     'before': True, 'after': False})
        results[n] = {'balanced_words': count, 'counterexamples': candidates, 'examples': examples}
    out = {'complete': True, 'discovery_length': 10, 'holdout_lengths': [14, 18],
           'results': results, 'elapsed_seconds': time.monotonic()-start,
           'cpu_seconds': time.process_time(),
           'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    Path(__file__).with_name('barrier-one.json').write_text(json.dumps(out, indent=2)+'\n')
    print(json.dumps(out))

if __name__ == '__main__':
    main()
