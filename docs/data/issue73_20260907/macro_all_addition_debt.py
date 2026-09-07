#!/usr/bin/env python3
import hashlib,pathlib,subprocess
print('protocol=issue73 all-addition continuation debt falsifier')
print('source_revision='+subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
print('script_sha256='+hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest())
def supply(mask,L):
    s=m=0
    for i in range(1,L+1):
        e=1 if mask & (1<<(i-1)) else -1
        s+=e;m+=i*e
        if (s,m)==(1,0):return True
    return False
def future(mask,L):
    bound=(1<<L)-1;out=[]
    for j in range(L):
        if supply(mask,L):out.append(j+1)
        mask=((mask<<1)|1)&bound
    return out
for L in (3,7,11,15):
    bound=(1<<L)-1
    fs=[future(mask,L) for mask in range(1<<L)]
    for mask in range(1<<L):
        a=((mask<<1)|1)&bound;s=(mask<<1)&bound
        assert len(fs[a])==len(fs[mask])-supply(mask,L)
        if len(fs[s])>len(fs[mask])+1:
            print('REFUTED L=%d history_oldest_first=%s F=%d afterS_F=%d future_A_supply_offsets=%r afterS_future_A_supply_offsets=%r' % (L,''.join('A' if mask&(1<<i) else 'S' for i in reversed(range(L))),len(fs[mask]),len(fs[s]),fs[mask],fs[s]))
            raise SystemExit(0)
    print('L=%d histories=%d PASS' % (L,1<<L),flush=True)
print('all frozen tests pass; not an all-L proof')
