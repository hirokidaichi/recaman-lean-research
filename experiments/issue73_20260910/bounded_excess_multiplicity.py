#!/usr/bin/env python3
"""H-20260910-02: both orientations of overlap and the boundary family."""
import hashlib
import json
from pathlib import Path
import subprocess


def subsets_sum(start, end, count, target):
    if count == 0:
        if target == 0:
            yield ()
        return
    if end-start+1 < count:
        return
    if not count*(2*start+count-1)//2 <= target <= count*(2*end-count+1)//2:
        return
    for first in range(start,end-count+2):
        for rest in subsets_sum(first+1,end,count-1,target-first):
            yield (first,)+rest


def p2_words(d):
    for positions in subsets_sum(1,d,(d+1)//2,d*(d+1)//4):
        aset = set(positions)
        yield tuple(1 if i in aset else -1 for i in range(1,d+1))


def hits(word):
    mass = moment = 0
    result = []
    for d, bit in enumerate(word,1):
        mass += bit
        moment += d*bit
        if mass == 1 and moment == 0:
            result.append(d)
    return result


def leading(word):
    return next((i for i,b in enumerate(word) if b == -1),len(word))


def scan(D):
    count = contacts = 0
    modes = {'old_contains_overlap':0,'new_contains_old':0}
    minimum_margin = None
    minimum_R = None
    def inspect(old,new,m,k,mode):
        nonlocal contacts,minimum_margin,minimum_R
        if m < 3:
            return
        a,b = old-(4*m-1),new-(4*(m+k)-1)
        assert a >= 0 and b >= 0 and a%4 == b%4 == 0
        R = max(a,b)//4
        margin = R*(R+1)-m
        assert margin >= 0,(D,old,new,m,k,R,mode)
        contacts += 1
        modes[mode] += 1
        minimum_margin = margin if minimum_margin is None else min(minimum_margin,margin)
        minimum_R = R if minimum_R is None else min(minimum_R,R)
    for word in p2_words(D):
        count += 1
        m = leading(word)
        if m >= 3:
            for k in range(1,5):
                for new in hits((1,)*k+word):
                    inspect(D,new,m,k,'old_contains_overlap')
        for k in range(1,5):
            if m >= k+3:
                for old in hits(word[k:]):
                    inspect(old,D,m-k,k,'new_contains_old')
    return {'max_lag':D,'P2_words':count,'eligible_contacts':contacts,'orientations':modes,
            'minimum_R':minimum_R,'minimum_threshold_margin':minimum_margin,'violations':0}


def sharp(m):
    return (1,)*m+(-1,)*(m-1)+(1,)+(-1,)*m+(1,)*(m-1)


def boundary(R):
    m = R*(R+1)
    old = sharp(m)
    tail = (-1,)*(2*R+1)+(1,-1)+(1,)*(2*R)
    new = (1,)+old+tail
    old_hits,new_hits = hits(old),hits(new)
    assert old_hits == [4*m-1]
    assert new_hits == [4*m+4*R+3]
    assert leading(old)==m and leading(new)==m+1
    assert sum(tail)==-1 and sum(i*b for i,b in enumerate(tail,1))==4*m-2
    delta=len(new)-len(old)
    assert delta*(delta-4)-4*(len(old)-1)==8
    return {'R':R,'m':m,'old_min_lag':len(old),'new_min_lag':len(new),
            'k':1,'old_excess':0,'new_excess':4*R,'threshold_margin':0,'gap_slack':8}


def main():
    print('protocol=H-20260910-02')
    print('source_revision='+subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
    print('script_sha256='+hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    for D in (11,15,19,23,27):
        print(('DISCOVERY' if D<=19 else 'HOLDOUT')+'='+json.dumps(scan(D)),flush=True)
    for R in range(2,65):
        print(('FAMILY_DISCOVERY' if R<=8 else 'FAMILY_HOLDOUT')+'='+json.dumps(boundary(R)),flush=True)
    print('PASS: band threshold survived; boundary family rules out lowering it by one')


if __name__ == '__main__':
    main()
