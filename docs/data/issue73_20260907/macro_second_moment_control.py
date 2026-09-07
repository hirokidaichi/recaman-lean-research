#!/usr/bin/env python3
import hashlib,pathlib,subprocess
print('protocol=issue73 fixed second-moment sign control')
print('source_revision='+subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
print('script_sha256='+hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest())
for w in ('AAS','AAASSASSSAA'):
    e=[1 if c=='A' else -1 for c in w]
    s=m=0;hits=[]
    for i,x in enumerate(e,1):
        s+=x;m+=i*x
        if (s,m)==(1,0):hits.append(i)
    second=sum(i*i*x for i,x in enumerate(e,1))
    print('newest_first=%s sum=%d moment=%d second_moment=%d P2_lags=%r' % (w,s,m,second,hits))
    assert hits==[len(w)]
print('uniform_negative_second_moment=REFUTED')
