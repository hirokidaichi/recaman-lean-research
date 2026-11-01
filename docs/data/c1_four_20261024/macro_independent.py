"""Independent reverse mass/moment DFS; compare complete normalized edges and long-gap holdout."""
from pathlib import Path
import datetime,hashlib,json,resource,time
resource.setrlimit(resource.RLIMIT_CPU,(50,51))
base=Path(__file__).parent;start=time.monotonic()

def local(v):
    m=p=0
    for k,c in enumerate(reversed(v),1):
        d=1 if c=='A' else -1;m+=d;p+=k*d
        if m==1 and p==0:return True
    return False

def old(v):
    m=sum(1 if c=='A' else -1 for c in v)
    ar=sum((len(v)-i)*(1 if c=='A' else -1) for i,c in enumerate(v))
    r=1-m;b=-ar-len(v)*r
    if r==1:return b==1
    return r>=2 and r*(r+1)//2-1<=b<=(5*r*r-11*r+16)//4

def next_state(s,j,e):
    v,a,ss,r=s
    v=v+'S'*j;sn=min(ss+j,19)
    # Check the entire untrimmed suffix at every holdout gap; trim only the output.
    le=local(v);oe=sn<19 and old(v)
    if (e==0 and le) or (e==1 and not(le or oe)):return None
    an=r+(e==0)
    if an>4 or (sn<19 and sn-a-1+an<1):return None
    v+='A'
    return (v[-19:] if sn==19 else v,a+1,sn,an)

def main():
    todo=[('',0,0,0)];seen={};classes=[set() for _ in range(5)]
    while todo:
        if time.monotonic()-start>45:raise TimeoutError('wall guard; incomplete')
        s=todo.pop()
        if s in seen:continue
        assert s[1]<=10,('unexpected11A',s)
        edges=[]
        for j in reversed(range(20)):
            v=s[0]+'S'*j;sn=min(s[2]+j,19)
            if sn-s[1]+s[3]==1:classes[s[3]].add(v[-19:] if sn==19 else v)
            for e in (1,0):
                t=next_state(s,j,e)
                edges.append((j,e,t))
                if t is not None:todo.append(t)
        seen[s]={(j,e):t for j,e,t in edges}
    cert=json.loads((base/'macro-certificate.json').read_text());rows=cert['rows']
    normalized={tuple(r['state']):{(j,e):(None if r['edges'][2*j+e] is None else tuple(rows[r['edges'][2*j+e]]['state'])) for j in range(20) for e in (0,1)} for r in rows}
    assert seen==normalized
    assert [sorted(c) for c in classes]==cert['classes']
    # Predeclared stratification: first32 lexicographic states for each free count0..4.
    selected=[]
    for r in range(5):selected.extend(sorted(s for s in seen if s[3]==r)[:32])
    controls=0
    for s in selected:
        for j in [20,37,257,4097]:
            for e in [0,1]:
                assert next_state(s,j,e)==next_state(s,19,e),(s,j,e)
                controls+=1
    result=dict(graph_exhausted=True,states=len(seen),edge_cases=len(seen)*40,
        all_states_and_edges_match=True,classes=[sorted(c) for c in classes],
        holdout_states=len(selected),long_gap_tag_controls=controls,
        elapsed_seconds=time.monotonic()-start,source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
    (base/'macro-independent.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
if __name__=='__main__':main()
