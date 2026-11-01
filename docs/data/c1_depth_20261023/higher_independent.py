"""Independent normalized r4 graph with literal block spectra and forward areas."""
import hashlib
import json
from pathlib import Path
import resource
import time

resource.setrlimit(resource.RLIMIT_CPU,(30,32))
start=time.monotonic();visited=0;max_a=0;seen=set();classes=[set() for _ in range(5)]
max_p=[-10**9]*5;witness=None;old_calls=0


def levels(w):
    f=[0];g=[0]
    for c in w:
        f.append(f[-1]+(1 if c=='A' else -1));g.append(g[-1]+f[-1])
    return f,g


words=[set() for _ in range(15)];words[0].add('')
for m in range(1,15):
    for dm,atom in [(1,'A'),(2,'SAAA'),(4,'SSAAAASAAA')]:
        if m>=dm:words[m].update(w+atom for w in words[m-dm])
spec={(m,levels(w)[1][-1]) for m,ws in enumerate(words) if m for w in ws}


def visit(w,a,s,r):
    global visited,max_a,witness,old_calls
    visited+=1
    if visited%4096==0 and time.monotonic()-start>28:raise TimeoutError('wall_guard')
    max_a=max(max_a,a)
    if a==16:
        witness=dict(word=w,A=a,S_flag=s,r=r);return
    if s<29:
        d=s-a+r;P=a-2*(d-1)
        if w:max_p[r]=max(max_p[r],P)
        if d==1:classes[r].add(w)
    else:
        # The exact actual S may be larger; even its optimistic P upper bound is negative.
        assert 3*a-2*29-2*r+2<=-11
        key=(w,a,r)
        if key in seen:return
        seen.add(key)
    f,g=levels(w);b=len(w)
    le=any(f[b]-f[t]==1 and g[b]-g[t]==(b-t)*f[t] for t in range(b))
    oe=False
    if s<29:
        old_calls+=1
        rm=1-f[b];ba=-g[b]-b*rm
        oe=(rm,ba) in spec
    choices=[1] if le else ([1,0] if oe else [0])
    for e in choices:
        nr=r+1-e
        if nr<=4 and (s>=29 or s-(a+1)+nr>=1):
            nw=w+'A'
            visit(nw[-29:] if s>=29 else nw,a+1,s,nr)
    ns=min(29,s+1);nw=w+'S'
    visit(nw[-29:] if ns==29 else nw,a,ns,r)


def main():
    try:visit('',0,0,0);complete=True
    except TimeoutError:complete=False
    p=Path(__file__).parent
    expected=json.loads((p/'relaxed-higher.json').read_text())
    assert complete and witness is None and expected['graph_exhausted']
    assert max_a==expected['highest_A'] and visited==expected['visited']
    assert len(seen)==expected['saturated_states']
    assert [sorted(c) for c in classes]==expected['classes']
    assert max_p==expected['max_P']
    usage=resource.getrusage(resource.RUSAGE_SELF)
    out=dict(passed=True,complete=True,visited=visited,saturated_states=len(seen),highest_A=max_a,
             endpoint_classes=[sorted(c) for c in classes],max_P=max_p,literal_prefixes=sum(map(len,words)),
             literal_signature_count=len(spec),old_queries=old_calls,
             elapsed_seconds=time.monotonic()-start,user_seconds=usage.ru_utime,system_seconds=usage.ru_stime,
             source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    (p/'higher-independent.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='endpoint_classes'}))


if __name__=='__main__':main()
