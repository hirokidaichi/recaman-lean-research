#!/usr/bin/env python3
"""Cross-check and classify the frozen W diagnostic; no extrapolation."""
import argparse
from collections import Counter, defaultdict
import csv
import hashlib
import json
from pathlib import Path

C, V, J, E = 11685598221, 4318940415, 276986, 11685741477
WMAX, N = 3*C+V+5, 31058


def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--births', type=Path, required=True)
    parser.add_argument('--scalar', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    fast = {}
    for row in csv.DictReader(args.births.open(), delimiter='\t'):
        r = {k: (v if k in ('side','sign') else int(v)) for k,v in row.items()}
        fast[r['value']] = r
    scalar = {}
    for line in (args.scalar/'stdout.txt').read_text().splitlines():
        if line.startswith('jointbirth '):
            f = line.split()
            i, w, t, arc, q, r = (int(f[k]) for k in (1,2,3,5,6,7))
            assert i not in scalar and w == WMAX-3*i and w == t*q+r and 0<=r<t
            scalar[i] = dict(value=w, birth=t, sign=f[4], arc=arc, q=q, r=r)
    assert len(scalar) == N
    groups = defaultdict(list)
    for i, r in scalar.items():
        f = fast[r['value']]
        assert (r['birth'],r['sign']) == (f['birth'],f['sign'])
        assert r['birth'] < C+5+2*i
        groups[(r['arc'],r['q'],r['sign'],f['section_start'],f['section_value'],
                f['section_pairs'],f['side'])].append(i)
    assert len({r['birth'] for r in scalar.values()}) == N
    print(f'W={N} scalar/accelerated first_birth_and_sign_matches={N} PASS')
    print('shared_birth_clocks=0 shared_producer_runs='+str(len(groups)))
    group_rows = []
    total_rail = 0
    for key, indices in sorted(groups.items()):
        arc,q,sign,n,v,pairs,side = key
        indices.sort()
        assert indices == list(range(indices[0],indices[-1]+1))
        ilo, ihi = indices[0],indices[-1]
        rail_lo,rail_hi = (v-n-pairs+1,v-n) if side=='L' else (v+1,v+pairs)
        birth_min=min(scalar[i]['birth'] for i in indices)
        birth_max=max(scalar[i]['birth'] for i in indices)
        slope = 6 if side=='L' else -6
        intercept = scalar[ilo]['birth']-slope*ilo
        assert all(scalar[i]['birth'] == intercept+slope*i for i in indices)
        assert (v-n)//n == (v-n-pairs+1)//(n+2*pairs-2)
        assert (v+1)//(n+1) == (v+pairs)//(n+2*pairs-1)
        total_rail += rail_hi-rail_lo+1
        g = dict(arc=arc, level=q, sign=sign, side=side, count=len(indices),
                 i_lo=ilo, i_hi=ihi, birth_min=birth_min, birth_max=birth_max,
                 birth_intercept=intercept, birth_slope=slope,
                 section_start=n, section_end=n+2*pairs-1, section_value=v,
                 section_pairs=pairs, rail_lo=rail_lo, rail_hi=rail_hi,
                 not_in_W=(rail_hi-rail_lo+1)-len(indices))
        group_rows.append(g)
        print('producer='+json.dumps(g,sort_keys=True))
    sorted_rails=sorted((g['rail_lo'],g['rail_hi']) for g in group_rows)
    assert sorted_rails[0][1]+1==sorted_rails[1][0]
    print(f'producer_rail_union=[{sorted_rails[0][0]},{sorted_rails[1][1]}] size={total_rail} '
          f'not_used_by_this_W={total_rail-N}; no claim about other consumers')
    rows={}
    trace=args.scalar/'trace.txt'
    for line in trace.read_text().splitlines():
        if line.startswith('#') or not line: continue
        t,v,q,r,s=line.split()
        rows[int(t)]=(int(v),int(q),int(r),s)
    assert rows[C][0]==V and rows[E][0]==4318376915
    for i in range(N):
        t=C+5+2*i
        prev,cur=rows[t-1],rows[t]
        assert prev[1]==4 and cur[1]==5 and cur[3]=='A'
        assert prev[0]-t==WMAX-3*i
    exit_clock=C+5+2*N
    assert rows[exit_clock][3]=='S' and rows[exit_clock][1]==3
    exit_value=rows[exit_clock][0]
    assert exit_value==WMAX-3*N==sorted_rails[0][0]-2
    print(f'W_consumer_clocks=[{C+5},{C+5+2*(N-1)}] step=2 PASS')
    print(f'phase_exit_clock={exit_clock} fresh_value={exit_value} below_joint_rail=2')
    rail_lo,rail_hi=2*C+V-J-1,2*C+V-1
    q3_targets=[]
    for t in range(C+1,E+1):
        if rows[t][3]=='A' and rows[t-1][1]==3:
            q3_targets.append((t,rows[t-1][0]-t))
    inside=[(t,w) for t,w in q3_targets if rail_lo<=w<=rail_hi]
    print(f'post_popup_q3_additions={len(q3_targets)} '
          f'candidates_in_prelanding_q2_rail={len(inside)} '
          f'outside={len(q3_targets)-len(inside)}')
    weights=Counter(rows[t-1][1] for t in range(C+1,E+1) if rows[t][3]=='A')
    cost=sum((2*q+1)*count for q,count in weights.items())
    assert cost==V-rows[E][0]==563500
    high_count, low_count = weights[4], weights[3]-1
    assert J+2 == 5*high_count+3*low_count
    assert cost == 9*high_count+7*low_count+16
    assert E-C == 2*high_count+2*low_count+8
    print(f'phase_identity N={high_count} K={low_count} J+2=5N+3K drop=9N+7K+16 PASS')
    print(f'addition_cost={cost} original_survival_slack={16*V-7*(V+1+3*J)} '
          f'weighted_candidate_slack={3*cost-7*J}')
    print('scope=fixed-example classification; no global inequality is claimed by this computation')
    args.out.mkdir(parents=True,exist_ok=True)
    (args.out/'issue71_groups.json').write_text(json.dumps(group_rows,indent=2)+'\n')
    with (args.out/'issue71_scalar_births.tsv').open('w') as out:
        out.write('i\tvalue\tbirth\tsign\tarc\tq\tr\n')
        for i in range(N):
            out.write(str(i)+'\t'+'\t'.join(str(scalar[i][k]) for k in ('value','birth','sign','arc','q','r'))+'\n')
    print('input_hashes='+json.dumps({str(p):digest(p) for p in [args.births,trace,args.scalar/'stdout.txt',args.scalar/'arcs.txt']},sort_keys=True))


if __name__=='__main__':
    main()
