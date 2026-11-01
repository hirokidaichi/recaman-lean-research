"""First sixteenth A with independent optional old-prefix area signatures."""
import datetime
import hashlib
import json
from pathlib import Path
import resource
import time

resource.setrlimit(resource.RLIMIT_CPU, (30, 32))
started = time.monotonic()
visited = 0
seen = set()
witness = None
max_a = 0
deadline = started + 28
old_branches = 0
max_p = [-10**9]*5
max_p_words = [None]*5
potential_violation = None
classes = [set() for _ in range(5)]


def local_end(tail):
    mass = moment = 0
    for length, c in enumerate(reversed(tail[-29:]), 1):
        sign = 1 if c == 'A' else -1
        mass += sign
        moment += length * sign
        if mass == 1 and moment == 0:
            return True
    return False


def old_possible(tail):
    level = area = 0
    for c in tail:
        level += 1 if c == 'A' else -1
        area += level
    r = 1-level
    old_area = -area-len(tail)*r
    if r == 1:
        return old_area == 1
    return r >= 2 and r*(r+1)//2-1 <= old_area <= (5*r*r-11*r+16)//4


def walk(tail, a, s, az, flags):
    global visited, witness, max_a, old_branches, potential_violation
    if witness:
        return
    visited += 1
    if visited % 4096 == 0 and time.monotonic() > deadline:
        raise TimeoutError('wall guard; graph incomplete')
    max_a = max(max_a, a)
    exact_d = tail.count("S")-a+az
    P = a-2*(exact_d-1)
    if tail and P>max_p[az]:
        max_p[az]=P;max_p_words[az]=dict(tail=tail,old_flags=flags,az=az,A=a,d=exact_d,P=P)
    if tail and P>2**az-1 and potential_violation is None:
        potential_violation=max_p_words[az]
    if a == 16:
        witness = dict(tail=tail, old_flags=flags, az=az, d=tail.count('S')-a+az)
        return
    if s < 29 and s-a+az == 1:
        classes[az].add(tail)
    if s >= 29:
        key = a, az, tail[-29:]
        if key in seen:
            return
        seen.add(key)
    e = local_end(tail)
    old = s < 29 and old_possible(tail)
    choices = [1] if e else ([0, 1] if old else [0])
    old_branches += old and not e
    for supplied in choices:
        new_az = az + (not supplied)
        if new_az <= 4 and (s >= 29 or s-(a+1)+new_az >= 1):
            walk(tail+'A', a+1, s, new_az,
                 flags+([len(tail)] if supplied and not e else []))
    walk(tail+'S', a, min(29, s+1), az, flags)


def main():
    try:
        walk('', 0, 0, 0, [])
        exhausted = witness is None
        reason = 'relaxed_witness' if witness else 'complete'
    except TimeoutError as exc:
        exhausted = False
        reason = str(exc)
    usage = resource.getrusage(resource.RUSAGE_SELF)
    result = dict(graph_exhausted=exhausted, reason=reason, visited=visited,
                  saturated_states=len(seen), highest_A=max_a, old_optional_branches=old_branches,
                  classes=[sorted(c) for c in classes], witness=witness, max_P=max_p, max_P_words=max_p_words, potential_violation=potential_violation,
                  elapsed_seconds=time.monotonic()-started,
                  user_seconds=usage.ru_utime, system_seconds=usage.ru_stime,
                  source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
    (Path(__file__).parent/'relaxed-higher.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('classes','max_P_words')}))


if __name__ == '__main__':
    main()
