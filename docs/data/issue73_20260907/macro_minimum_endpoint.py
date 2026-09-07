#!/usr/bin/env python3
import hashlib,itertools,pathlib,subprocess
print('protocol=issue73 minimum-P2 endpoint falsifier')
print('source_revision='+subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
print('script_sha256='+hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest())
checked=0
for d in (3,7,11,15,19,23):
    k=(d-1)//2
    for negatives in itertools.combinations(range(1,d),k):
        if sum(negatives)!=d*(d+1)//4:continue
        signs=[-1 if i in negatives else 1 for i in range(1,d+1)]
        s=m=0;hits=[]
        for i,e in enumerate(signs,1):
            s+=e;m+=i*e
            if s==1 and m==0:hits.append(i)
        checked+=1
        if hits==[d]:
            print('REFUTED d=%d negatives=%r newest_first=%s earlier_hits=%r candidates_checked=%d' % (d,negatives,''.join('A' if e>0 else 'S' for e in signs),hits[:-1],checked))
            raise SystemExit(0)
    print('d=%d no_positive_ending_minimum cumulative_candidates=%d' % (d,checked),flush=True)
print('no counterexample in frozen range; no proof')
