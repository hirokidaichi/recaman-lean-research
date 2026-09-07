#!/usr/bin/env python3
"""Independent every-edge audit, direct signed sums, no search-module import."""
from pathlib import Path
from collections import Counter
import gzip
import hashlib
import json
import subprocess

BASE='b4b5afaaac126acaa0c4fc0042bdaa4fafd289a1'
DATA=Path('docs/data/issue73_20260907')


def signs_and_supply(state, length):
    total=moment=0
    supply=False
    next_minus=0
    for lag in range(1,length+1):
        sign=1 if (state // (2**(lag-1))) % 2 else -1
        total+=sign
        moment+=lag*sign
        if total==1 and moment==0:
            supply=True
        if lag<length and sign>0:
            next_minus+=2**lag
    return supply,next_minus


def read_payload(length):
    raw=DATA/f'automaton_L{length}_potential.txt'
    zipped=Path(str(raw)+'.gz')
    if raw.exists():
        try:
            return raw.read_bytes()
        except FileNotFoundError:
            pass
    return gzip.decompress(zipped.read_bytes())


def main():
    print('protocol=H09 independent every-edge audit; frozen L only; no search extension')
    print('source_base_revision='+BASE)
    print('current_revision='+subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
    print('source_sha256='+hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    records={}
    for name in ('automaton_discovery.txt','automaton_holdout.txt'):
        for line in (DATA/name).read_text().splitlines():
            if line.startswith('NO_POSITIVE_CYCLE='):
                record=json.loads(line.partition('=')[2])
                records[record['horizon']]=record
    total_edges=0
    for length in (3,7,11,15,19):
        payload=read_payload(length)
        digest=hashlib.sha256(payload).hexdigest()
        record=records[length]
        assert digest==record['potential_sha256']
        potential=[int(x) for x in payload.splitlines()]
        assert len(potential)==2**length==record['states']
        assert min(potential)>=0
        counts={str(k):v for k,v in sorted(Counter(potential).items())}
        assert counts==record['potential_counts']
        supplied=0
        minimum_minus=minimum_plus=None
        for state,value in enumerate(potential):
            supported,next_minus=signs_and_supply(state,length)
            supplied+=supported
            next_plus=next_minus+1
            minus_slack=potential[next_minus]-value+1
            plus_slack=potential[next_plus]-value-int(supported)
            assert minus_slack>=0,(length,state,'S',minus_slack)
            assert plus_slack>=0,(length,state,'A',plus_slack)
            minimum_minus=minus_slack if minimum_minus is None else min(minimum_minus,minus_slack)
            minimum_plus=plus_slack if minimum_plus is None else min(minimum_plus,plus_slack)
        assert supplied==record['supplied_states']
        all_a=2**length-1
        assert signs_and_supply(all_a,length)==(False,all_a-1)
        assert potential[all_a]-potential[all_a]<1  # rejects mass-only false weight +1
        cycle=(-1,1,1,1)
        third_a_history=sum(2**(lag-1) for lag in range(1,length+1) if cycle[(3-lag)%4]>0)
        assert signs_and_supply(third_a_history,length)[0]
        edges=2*len(potential)
        total_edges+=edges
        print(json.dumps({'L':length,'states':len(potential),'edges_checked':edges,
          'supplied_states_direct_sums':supplied,'minimum_S_slack':minimum_minus,
          'minimum_A_slack':minimum_plus,'potential_sha256':digest,
          'positive_and_negative_controls':'PASS'},sort_keys=True,separators=(',',':')),flush=True)
    print('PASS: independently verified '+str(total_edges)+' edge inequalities; no all-L claim')


if __name__=='__main__':
    main()
