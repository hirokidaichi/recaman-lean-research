"""Bounded-depth Q, independent old signatures, no word-length cutoff."""
from collections import deque
import datetime
import hashlib
import json
from pathlib import Path
import resource
import time

resource.setrlimit(resource.RLIMIT_CPU, (30,32))
ROOTS = ['S','SA','SAA','SSAAA','SASAAA','SSAAAA','SSAAAASA','SSSSAAAASAAA']


def values(w):
    f = g = 0
    for c in w:
        f += 1 if c == 'A' else -1
        g += f
    return f,g


def local(w):
    mass = moment = 0
    for length,c in enumerate(reversed(w),1):
        sign = 1 if c == 'A' else -1
        mass += sign
        moment += length*sign
        if mass == 1 and moment == 0:
            return True
    return False


def old(w):
    mass,area = values(w)
    r = 1-mass
    B = -area-len(w)*r
    return r >= 1 and B >= 1 and r*(r+1) <= 2*B+2 and 4*B <= 5*r*r-11*r+16 and (r != 1 or B == 1)


def successors(st):
    root,w,ay = st
    f,_ = values(w)
    az = values(ROOTS[root])[0]+1
    edges=[]
    if f-1 >= -4:
        edges.append(('S',(root,w+'S',ay)))
    le,oe=local(w),old(w)
    for e in [0,1]:
        if (not e and le) or (e and not(le or oe)):
            continue
        new_ay = ay+1-e
        if new_ay <= 1 and az+new_ay-(f+1) >= 1:
            edges.append(('A'+str(e),(root,w+'A',new_ay)))
    return edges


def main():
    started=time.monotonic()
    initial=[(i,w,0) for i,w in enumerate(ROOTS)]
    states=initial.copy(); index={s:i for i,s in enumerate(states)}
    queue=deque(states); rows=[]; witness=None; reason='complete'
    guard_count=0; minZ=10**9; optional_old=[]
    while queue:
        if time.monotonic()-started > 28:
            reason='wall_guard';break
        st=queue.popleft();root,w,ay=st
        if len(w)>=512 or len(states)>=500000:
            reason='resource_guard';break
        f,g=values(w)
        if f<=0:
            guard_count+=1;Z=g+len(w)*(1-f);minZ=min(minZ,Z)
            if Z<0:
                witness=dict(root=ROOTS[root],tail=w,ay=ay,Z=Z,kind='relaxed not actual history')
                reason='Q_relaxation_counterexample';break
        if old(w) and not local(w):
            optional_old.append(dict(root=ROOTS[root],tail=w,ay=ay))
        edges=[]
        for tag,target in successors(st):
            if target not in index:
                index[target]=len(states);states.append(target);queue.append(target)
            edges.append([tag,index[target]])
        rows.append(dict(state=list(st),edges=edges))
    usage=resource.getrusage(resource.RUSAGE_SELF)
    result=dict(graph_exhausted=not queue and witness is None,reason=reason,roots=ROOTS,
                states=len(states),rows=rows,processed=len(rows),guards=guard_count,minZ=minZ,
                maximum_word_length=max(len(s[1]) for s in states),optional_old_states=optional_old,
                witness=witness,elapsed_seconds=time.monotonic()-started,
                user_seconds=usage.ru_utime,system_seconds=usage.ru_stime,
                source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
    p=Path(__file__).parent
    (p/'q-certificate.json').write_text(json.dumps(result,separators=(',',':'))+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='rows'}))


if __name__=='__main__':
    main()
