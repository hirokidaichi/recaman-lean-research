"""Literal all-start P2 ledgers; no history tags or recurrence inference."""
import hashlib
import json
from pathlib import Path
import resource
import sys

resource.setrlimit(resource.RLIMIT_CPU,(5,7))


def ledger(prefix,tail):
    w=prefix+tail
    f=[0];d=[0];an=[0];end=[];starts=[]
    for b,c in enumerate(w):
        windows=[]
        for t in range(b):
            signs=[1 if x=='A' else -1 for x in w[t:b]]
            if sum(signs)==1 and sum((b-t-i)*s for i,s in enumerate(signs))==0:
                windows.append(t)
        e=c=='A' and bool(windows)
        starts.append(windows);end.append(e)
        f.append(f[-1]+(1 if c=='A' else -1))
        d.append(d[-1]+(c=='S')-e)
        an.append(an[-1]+(c=='A' and not e))
    n=len(prefix)
    return dict(prefix=prefix,tail=tail,F=f,d=d,AN=an,endable=end,P2_starts=starts,
                n=n,q=len(w),prefix_deficit=d[n],positive_tail=min(d[n+1:])>=1,
                tail_free_A=an[-1]-an[n],tail_all_A=tail.count('A'),
                endpoint_deficit=d[-1],depth=max(f[n]-v for v in f[n:]),
                source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())


if __name__=='__main__':
    if len(sys.argv)==1:
        result=ledger('SAAA','SSSSAAAASA')
        assert result['prefix_deficit']==0 and result['positive_tail']
        assert (result['tail_free_A'],result['tail_all_A'],result['endpoint_deficit'])==(2,5,2)
    else:
        result=ledger(sys.argv[1],sys.argv[2])
    print(json.dumps(result))
