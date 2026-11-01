"""Independent literal forward-area reconstruction of the complete Q graph."""
from collections import deque
import hashlib
import json
from pathlib import Path
import resource
import time

resource.setrlimit(resource.RLIMIT_CPU,(30,32))
ROOTS=('S','SA','SAA','SSAAA','SASAAA','SSAAAA','SSAAAASA','SSSSAAAASAAA')


def walk(w):
    f=[0]
    for c in w:
        f.append(f[-1]+(1 if c=='A' else -1))
    return f


def local(w):
    f=walk(w)
    return any(f[-1]-f[t]==1 and sum(x-f[t] for x in f[t+1:])==0 for t in range(len(w)))


def signatures():
    table=[set() for _ in range(6)]
    table[0].add('')
    for m in range(1,6):
        for dm,atom in [(1,'A'),(2,'SAAA'),(4,'SSAAAASAAA')]:
            if m>=dm:
                table[m].update(w+atom for w in table[m-dm])
    return {(m,sum(walk(w)[1:])) for m,ws in enumerate(table) if m for w in ws}


def main():
    start=time.monotonic();spec=signatures()
    seen=set();todo=[(i,w,0) for i,w in enumerate(ROOTS)]
    graph={};minimum=10**9;guards=0
    while todo:
        root,w,ay=todo.pop()
        st=(root,w,ay)
        if st in seen:continue
        seen.add(st)
        f=walk(w);mass=f[-1];az=walk(ROOTS[root])[-1]+1
        if mass<=0:
            Z=sum(x-mass+1 for x in f[1:]);assert Z>=0,(st,Z)
            minimum=min(minimum,Z);guards+=1
        r=1-mass;B=-sum(f[1:])-len(w)*r
        oe=(r,B) in spec;le=local(w)
        edges=[]
        for e in [1,0]:
            if (e and not(le or oe)) or (not e and le):continue
            new=ay+1-e
            if new<=1 and az+new-(mass+1)>=1:
                edges.append(('A'+str(e),(root,w+'A',new)))
        if mass>=-3:edges.append(('S',(root,w+'S',ay)))
        graph[st]=set(edges);todo.extend(t for _,t in edges)
        assert len(seen)<500000 and len(w)<512
    p=Path(__file__).parent
    cert=json.loads((p/'q-certificate.json').read_text())
    assert cert['graph_exhausted']
    expected={tuple(r['state']):{(tag,tuple(cert['rows'][j]['state'])) for tag,j in r['edges']}
              for r in cert['rows']}
    assert graph==expected
    assert minimum==cert['minZ'] and guards==cert['guards']
    prefix='SAAA';z='SSSSAAAASAAA';full=prefix+z
    f=walk(full);n=len(prefix);q=len(full)
    Az=sum(x-f[n]+1 for x in f[n+1:]);assert Az==-2
    g=walk(full+'SS');b=len(g)-1
    Z=sum(x-g[b]+1 for x in g[n+1:]);assert Z==1
    assert local('SSAAAAS') and local('SAAA'+'SSSSAAA')
    usage=resource.getrusage(resource.RUSAGE_SELF)
    result=dict(passed=True,states=len(graph),guards=guards,minZ=minimum,
                all_states_and_all_edges_equal=True,
                independent_old_signatures=sorted(spec),old_signature_method='all literal block words mass1..5',
                local_method='all starts, forward levels and literal area sum',
                controls={'Az':Az,'Z_after_SS':Z,'nonblock_counter_window':'SSAAAAS','sharp_old_window':'SAAASSSSAAA'},
                elapsed_seconds=time.monotonic()-start,user_seconds=usage.ru_utime,system_seconds=usage.ru_stime,
                source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    (p/'q-independent.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))


if __name__=='__main__':main()
