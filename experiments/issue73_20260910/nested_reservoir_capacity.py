#!/usr/bin/env python3
"""H-05: exact adversarial Hall cuts for every old short injection.

For a set H of new sources, the worst old short matching occupies
nu_short(union reservoirs(H)) targets. Hall's condition after EVERY old
matching is equivalent to |union S|-nu_short >= |H| for every H.
U may be any subset of the available A sources, so this test is exact.
"""
import hashlib
import itertools
import json
from pathlib import Path
import subprocess
from reservoir_capacity import run_data, max_occupancy


def hall_check(e,Q,L):
    tested=0
    min_slack=None
    for mask in range(1,1<<len(Q)):
        selected=[Q[i] for i in range(len(Q)) if mask>>i&1]
        union=set().union(*(x[3] for x in selected))
        S={q for q in union if e[q]==-1}
        occupied=max_occupancy(e,S,L)
        slack=len(S)-occupied-len(selected)
        assert slack>=0,(e,L,[(x[0],x[1]) for x in selected],S,occupied)
        tested+=1
        min_slack=slack if min_slack is None else min(min_slack,slack)
    return tested,min_slack


def scan(p):
    words=eligible_cases=hall_cuts=multiple_same_run=wrapping_cases=0
    max_Q=0
    min_slack=None
    for e in itertools.product((-1,1),repeat=p):
        words+=1
        data=run_data(e)
        for B,L in itertools.product(range(4),(0,1,3,7)):
            M=2*B+L+2
            Q=[x for x in data if x[1]>=M and x[4]<=B]
            if not Q:
                continue
            eligible_cases+=1
            max_Q=max(max_Q,len(Q))
            multiple_same_run+=int(len({x[2] for x in Q})<len(Q))
            wrapping_cases+=int(any(x[0]-2*x[1]+1<0<=x[0]-x[1]-1 for x in Q))
            tested,slack=hall_check(e,Q,L)
            hall_cuts+=tested
            min_slack=slack if min_slack is None else min(min_slack,slack)
    return {'period':p,'words':words,'eligible_cases':eligible_cases,'Hall_cuts':hall_cuts,
            'multiple_same_run_cases':multiple_same_run,'wrapping_cases':wrapping_cases,
            'maximum_Q':max_Q,'minimum_slack':min_slack,'violations':0}


def structured(B,L,extra,runs):
    M=2*B+L+2
    # Many Qs in the same run. Consecutive nonoverlapping S/A blocks also
    # test multiple cyclic starts. Only exact Hall subsets up to 16 sources;
    # for larger sets test every prefix per run (the nested-family reduction).
    e=tuple(b for i in range(runs) for b in ((-1,)*(M+extra+2+i)+(1,)*(M+extra+2+i)))
    Q=[x for x in run_data(e) if x[1]>=M and x[4]<=B]
    if len(Q)<=16:
        tested,slack=hall_check(e,Q,L)
        mode='all_Hall_subsets'
    else:
        tested=0
        slack=None
        mode='each_run_prefix_only'
        for a in sorted({x[2] for x in Q}):
            same=sorted((x for x in Q if x[2]==a),key=lambda x:x[1])
            for n in range(1,len(same)+1):
                H=same[:n]
                union=set().union(*(x[3] for x in H))
                S={q for q in union if e[q]==-1}
                v=len(S)-max_occupancy(e,S,L)-n
                assert v>=0
                tested+=1
                slack=v if slack is None else min(slack,v)
    return {'B':B,'L':L,'extra':extra,'runs':runs,'period':len(e),'Q':len(Q),
            'test_mode':mode,'cuts_tested':tested,'minimum_slack':slack}


def main():
    print('protocol=H-20260910-05')
    print('source_revision='+subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
    for name in ('nested_reservoir_capacity.py','reservoir_capacity.py','bounded_excess_multiplicity.py'):
        print(name+'_sha256='+hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest())
    for p in range(3,19):
        print(('DISCOVERY' if p<=13 else 'HOLDOUT')+'='+json.dumps(scan(p)),flush=True)
    # Frozen ranges: B0..3 discovery,4..8 holdout; L0,1,3,7;
    # extra0,2,7 and one/three runs. Larger-than-16 Q tests are restricted
    # prefix tests, expressly not exhaustive Hall checks.
    for B,L,extra,runs in itertools.product(range(9),(0,1,3,7),(0,2,7),(1,3)):
        print(('STRUCTURED_DISCOVERY' if B<=3 else 'STRUCTURED_HOLDOUT')+'='+
              json.dumps(structured(B,L,extra,runs)),flush=True)
    print('PASS: universal-old-matching Hall cuts survived; many same-run sources included')


if __name__=='__main__':
    main()
