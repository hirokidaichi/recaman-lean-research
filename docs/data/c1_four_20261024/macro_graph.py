"""Frozen r4 A-event graph. Complete transitions include every gap0..19 and both tags."""
from collections import deque
from pathlib import Path
import datetime,hashlib,json,resource,time
resource.setrlimit(resource.RLIMIT_CPU,(50,51))
started=time.monotonic()
base=Path(__file__).parent

def local(w):
    for t in range(len(w)):
        f=area=0
        for c in w[t:]:
            f+=1 if c=='A' else -1
            area+=f
        if f==1 and area==0:return True
    return False

def old(w):
    f=area=0
    for c in w:
        f+=1 if c=='A' else -1
        area+=f
    r=1-f;b=-area-len(w)*r
    return r>=1 and b>=1 and r*(r+1)<=2*b+2 and 4*b<=5*r*r-11*r+16 and (r!=1 or b==1)

def gap(st,j):
    w,a,s,r=st;ns=min(19,s+j);v=w+'S'*j
    return (v[-19:] if ns==19 else v,a,ns,r)

def move(st,j,e):
    w,a,s,r=gap(st,j)
    le=local(w);oe=s<19 and old(w)
    if e and not(le or oe) or not e and le:return None
    an=r+1-e
    if an>4 or (s!=19 and s-(a+1)+an<1):return None
    v=w+'A'
    return (v[-19:] if s==19 else v,a+1,s,an)

def main():
    states=[('',0,0,0)];index={states[0]:0};rows=[]
    classes=[set() for _ in range(5)];witness=None
    while len(rows)<len(states):
        if time.monotonic()-started>45:raise TimeoutError('wall guard; incomplete')
        st=states[len(rows)]
        if st[1]>10:
            witness=st;break
        for j in range(20):
            w,a,s,r=gap(st,j)
            if s-a+r==1:classes[r].add(w)
        edges=[]
        for j in range(20):
            for e in (0,1):
                target=move(st,j,e)
                if target is None:edges.append(None);continue
                if target not in index:index[target]=len(states);states.append(target)
                edges.append(index[target])
        rows.append(dict(state=list(st),edges=edges))
    result=dict(graph_exhausted=witness is None,states=len(states),processed=len(rows),
                highest_A=max(s[1] for s in states),witness=witness,classes=[sorted(s) for s in classes],rows=rows,
                elapsed_seconds=time.monotonic()-started,source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
    (base/'macro-certificate.json').write_text(json.dumps(result,separators=(',',':'))+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='rows'}))
    if witness:raise SystemExit(2)
if __name__=='__main__':main()
