#!/usr/bin/env python3
import hashlib,itertools,pathlib,random,subprocess
print('protocol=issue73 explicit short-lag injection regression')
print('source_revision='+subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
print('script_sha256='+hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest())

def check(w):
    p=len(w); images={}; supplied=0
    for t,e in enumerate(w):
        if e<0:continue
        s=m=0; d=None
        for i in range(1,8):
            s+=w[(t-i)%p];m+=i*w[(t-i)%p]
            if s==1 and m==0:
                d=i;break
        if d is None:continue
        supplied+=1
        assert d in (3,7),(w,t,d)
        # Positive distances of all S occurrences in the actual lag window.
        offsets=[i for i in range(1,d+1) if w[(t-i)%p]<0]
        h=offsets[0]
        if d==3:
            assert h==3 and offsets==[3],(w,t,d,offsets)
            image=(t-h)%p
            gap=next(j for j in range(1,p+1) if w[(image+j)%p]<0)
            assert gap>=4,(w,t,d,image,gap)
        elif h==1:
            assert offsets==[1,6,7],(w,t,d,offsets)
            image=(t-7)%p
            gap=next(j for j in range(1,p+1) if w[(image+j)%p]<0)
            assert gap==1,(w,t,d,image,gap)
        else:
            assert h==2 and offsets==[2,5,7],(w,t,d,offsets)
            image=(t-5)%p
            gap=next(j for j in range(1,p+1) if w[(image+j)%p]<0)
            assert gap==3,(w,t,d,image,gap)
        assert image not in images,(w,t,d,image,images)
        images[image]=(t,d)
    assert supplied<=w.count(-1),(w,supplied)
    return supplied

words=events=0
for p in range(1,15):
    count=0
    for w in itertools.product((-1,1),repeat=p):
        events+=check(w);words+=1;count+=1
    print('period=%d all_words=%d cumulative_supplied_A=%d PASS' % (p,count,events),flush=True)
print('exhaustive_words=%d supplied_events=%d PASS' % (words,events))
rng=random.Random(7307); words=events=0
for p in range(15,81):
    for _ in range(100):
        w=tuple(rng.choice((-1,1)) for _ in range(p))
        events+=check(w);words+=1
print('random_seed=7307 period_range=[15,80] words=%d supplied_events=%d PASS' % (words,events))
