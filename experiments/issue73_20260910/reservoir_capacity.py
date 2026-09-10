#!/usr/bin/env python3
"""H-20260910-04: abstract cyclic geometry and adversarial short-image occupancy."""
import hashlib
import itertools
import json
from pathlib import Path
import subprocess
from bounded_excess_multiplicity import sharp, hits


def run_data(e):
    p=len(e)
    result=[]
    if all(b==1 for b in e):
        return result
    for t,b in enumerate(e):
        if b!=1:
            continue
        m=0
        while e[(t-m-1)%p]==1:
            m+=1
        B={(t-j)%p for j in range(m+1,2*m)}
        result.append((t,m,(t-m)%p,B,sum(e[q]==1 for q in B)))
    return result


def max_occupancy(e,B,L):
    """Maximum matching from arbitrary A sources into S positions in B."""
    p=len(e)
    edges={u:[(u-j)%p for j in range(1,L+1) if (u-j)%p in B and e[(u-j)%p]==-1]
           for u,b in enumerate(e) if b==1}
    match={}
    def augment(u,seen):
        for q in edges[u]:
            if q in seen:
                continue
            seen.add(q)
            if q not in match or augment(match[q],seen):
                match[q]=u
                return True
        return False
    for u in edges:
        augment(u,set())
    return len(match)


def scan(p):
    words=reservoirs=pairs=wraps=matching_tests=0
    negative=None
    for e in itertools.product((-1,1),repeat=p):
        words+=1
        data=run_data(e)
        for R in range(4):
            eligible=[x for x in data if x[1]>=max(3,2*R+1) and x[4]<=2*R]
            for t,m,a,B,b in eligible:
                reservoirs+=1
                wraps+=int(t-2*m+1<0<=t-m-1)
                assert len(B)==m-1
                for L in (0,1,3,7):
                    occ=max_occupancy(e,B,L)
                    matching_tests+=1
                    assert occ<=2*R+L,(e,t,m,R,L,occ)
                    if m>=4*R+L+2:
                        assert len(B)-b-occ>=1
            for x,y in itertools.combinations(eligible,2):
                if x[2]!=y[2]:
                    pairs+=1
                    assert not x[3]&y[3],(e,R,x,y)
                elif x[3]&y[3] and negative is None:
                    negative={'word':''.join('A' if b==1 else 'S' for b in e),'R':R,
                              'sources':[x[0],y[0]],'runs':[x[1],y[1]],
                              'overlap':sorted(x[3]&y[3])}
    return {'period':p,'words':words,'eligible_reservoirs':reservoirs,'different_run_pairs':pairs,
            'wrapping_reservoirs':wraps,'matching_tests':matching_tests,
            'drop_uniqueness_counterexample':negative,'violations':0}


def almost_sharp(m):
    return (1,)*m+(-1,1)+(-1,)*(m-2)+(1,)+(-1,)*(m+2)+(1,)*m


def structured(R,L,delta,multi):
    threshold=max(3,R*(R+1)+1,4*R+L+2)
    ms=[threshold+delta+i*3 for i in range(3 if multi else 1)]
    e=()
    Q=[]
    for m in ms:
        w=sharp(m) if R==0 else almost_sharp(m)
        assert hits(w)==[len(w)]
        e+=tuple(reversed(w))+(1,)
        Q.append(len(e)-1)
        if multi:
            e+=(-1,)*(L+2)
    data={x[0]:x for x in run_data(e)}
    reservoirs=[]
    worst_free=None
    for t,m in zip(Q,ms):
        _,actual,a,B,b=data[t]
        assert actual==m and b<=2*R
        occ=max_occupancy(e,B,L)
        free=len(B)-b-occ
        assert free>=1
        worst_free=free if worst_free is None else min(worst_free,free)
        assert all(not B&C for C in reservoirs)
        reservoirs.append(B)
    return {'R':R,'L':L,'delta':delta,'multiple_runs':multi,'period':len(e),
            'source_count':len(Q),'runs':ms,'least_free_S_under_worst_short_matching':worst_free}


def main():
    print('protocol=H-20260910-04')
    print('source_revision='+subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
    print('script_sha256='+hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    print('generator_sha256='+hashlib.sha256(Path(__file__).with_name('bounded_excess_multiplicity.py').read_bytes()).hexdigest())
    for p in range(3,19):
        print(('DISCOVERY' if p<=13 else 'HOLDOUT')+'='+json.dumps(scan(p)),flush=True)
    # Fixed before execution: R0..4 discovery, R5..12 holdout; L0,3,7,11;
    # run sizes threshold+delta with delta0,1,5; one and three source runs.
    for R,L,delta,multi in itertools.product(range(13),(0,3,7,11),(0,1,5),(False,True)):
        print(('STRUCTURED_DISCOVERY' if R<=4 else 'STRUCTURED_HOLDOUT')+'='+
              json.dumps(structured(R,L,delta,multi)),flush=True)
    print('PASS: disjointness and unused-S gates survived; uniqueness assumption is necessary')


if __name__=='__main__':
    main()
