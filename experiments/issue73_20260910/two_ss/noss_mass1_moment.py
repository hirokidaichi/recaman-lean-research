#!/usr/bin/env python3
"""Min moment among SS-free mass-1 words, vs case-5 target 1-|v|."""
import hashlib, itertools, json, subprocess
from pathlib import Path

def stats(w):
    mass=moment=ss=0
    prev=1
    for i,s in enumerate(w,1):
        mass+=s; moment+=i*s
        if s==prev==-1: ss+=1
        prev=s
    return mass,moment,ss

def main():
    print('protocol=H-20260910-32 NoSS mass-1 moment lower bound')
    print('source_revision='+subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
    print('source_sha256='+hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    for n in range(1,21):
        best=None
        count=0
        for bits in itertools.product((-1,1),repeat=n):
            mass,moment,ss=stats(bits)
            if ss==0 and mass==1:
                count+=1
                if best is None or moment<best[0]:
                    best=(moment,''.join('A' if s==1 else 'S' for s in bits))
        print('LEN='+json.dumps(dict(n=n,noss_mass1=count,
              min_moment=None if best is None else best[0],
              word=None if best is None else best[1],
              case5_need_for_f_eq_nplus1=1-(n),  # |v|=n if extra length? not that
              )))

if __name__=='__main__':
    main()
