#!/usr/bin/env python3
"""Frozen H-09 finite-state positive-cycle falsifier for E-070."""
import argparse
from collections import deque, Counter
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import time

DEP = Path(__file__).resolve().parents[1] / 'parallel20260907/periodic_search.py'
spec=importlib.util.spec_from_file_location('suppliers', DEP)
supply=importlib.util.module_from_spec(spec)
spec.loader.exec_module(supply)


def is_supplied(mask, horizon):
    for d in range(3, horizon+1, 4):
        bits=mask & ((1 << d)-1)
        if bits.bit_count() != (d+1)//2:
            continue
        moment=0
        while bits:
            low=bits & -bits
            moment += low.bit_length()
            bits -= low
        if moment == d*(d+1)//4:
            return True
    return False


def search(horizon, outdir):
    size=1 << horizon
    bound=size-1
    supported=bytearray(is_supplied(mask,horizon) for mask in range(size))
    potential=[0]*size
    parent=[-1]*size
    depth=[0]*size
    queue=deque(range(size))
    queued=bytearray([1])*size
    relaxations=0
    while queue:
        u=queue.popleft()
        queued[u]=0
        for bit,weight in ((0,-1),(1,supported[u])):
            v=((u << 1) | bit) & bound
            candidate=potential[u]+weight
            if candidate <= potential[v]:
                continue
            potential[v]=candidate
            parent[v]=u
            depth[v]=depth[u]+1
            relaxations+=1
            if depth[v] >= size:
                z=v
                for _ in range(size):
                    z=parent[z]
                    assert z >= 0
                cycle=[z]
                nxt=parent[z]
                while nxt != z:
                    assert nxt >= 0 and nxt not in cycle
                    cycle.append(nxt)
                    nxt=parent[nxt]
                cycle.reverse()
                word=[1 if node & 1 else -1 for node in cycle]
                cycle_weight=0
                for i,u0 in enumerate(cycle):
                    v0=cycle[(i+1)%len(cycle)]
                    bit=v0 & 1
                    assert (((u0 << 1) | bit) & bound)==v0
                    cycle_weight += supported[u0] if bit else -1
                assert cycle_weight > 0
                sig=supply.suppliers(word)
                assert sig == supply.naive(word)
                minus=word.count(-1)
                used=sum(bool(ds) for ds in sig.values())
                assert used > minus
                witness={'horizon':horizon,'period':len(word),'word':''.join('A' if e>0 else 'S' for e in word),'sign_sum':sum(word),'short_cycle_weight':cycle_weight,'A_count':len(word)-minus,'D_count':minus,'U_count':used,'suppliers':sig,'cycle_states':cycle}
                target=outdir/f'automaton_L{horizon}_counterexample.json'
                target.write_text(json.dumps(witness,sort_keys=True,indent=2)+'\n')
                print('CAPACITY_COUNTEREXAMPLE='+json.dumps(witness,sort_keys=True),flush=True)
                return True
            if not queued[v]:
                queued[v]=1
                queue.append(v)
    for u in range(size):
        assert potential[(u << 1) & bound] >= potential[u]-1
        assert potential[((u << 1)|1) & bound] >= potential[u]+supported[u]
    payload='\n'.join(map(str,potential))+'\n'
    target=outdir/f'automaton_L{horizon}_potential.txt'
    target.write_text(payload)
    print('NO_POSITIVE_CYCLE='+json.dumps({'horizon':horizon,'states':size,'edges':2*size,'supplied_states':sum(supported),'relaxations':relaxations,'potential_counts':dict(sorted(Counter(potential).items())),'potential_sha256':hashlib.sha256(payload.encode()).hexdigest()}),flush=True)
    return False


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--mode',choices=('discovery','holdout'),required=True)
    parser.add_argument('--output-dir',type=Path,required=True)
    args=parser.parse_args()
    args.output_dir.mkdir(parents=True,exist_ok=True)
    print('protocol=H-20260907-09 finite automaton capacity falsifier',flush=True)
    print('source_base_revision=b4b5afaaac126acaa0c4fc0042bdaa4fafd289a1',flush=True)
    print('current_revision='+subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),flush=True)
    print('source_sha256='+hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),flush=True)
    print('dependency_sha256='+hashlib.sha256(DEP.read_bytes()).hexdigest(),flush=True)
    for horizon in ((3,7,11,15) if args.mode=='discovery' else (19,)):
        if search(horizon,args.output_dir):
            print('STOP: E-070 refuted; inspect all-A condition separately',flush=True)
            return
    print('COMPLETE: no positive cycle at frozen horizons; not an all-horizon proof',flush=True)


if __name__=='__main__':
    main()
